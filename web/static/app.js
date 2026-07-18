const $ = (id) => document.getElementById(id);
const input = $('formulaInput');
const runButton = $('run');
const suggestions = $('suggestions');
let parsedFormula = null;
let suggestionIndex = 0;

const suggestionItems = [
  { key: 'box', insert: 'box ', label: '□', help: 'necessity' },
  { key: 'diamond', insert: 'diamond ', label: '◇', help: 'possibility' },
  { key: 'neg', insert: 'neg ', label: '¬', help: '' },
  { key: 'bottom', insert: 'bottom', label: '⊥', help: '' },
  { key: 'and', insert: ' and ', label: '∧', help: '' },
  { key: 'or', insert: ' or ', label: '∨', help: '' },
  { key: 'imp', insert: ' imp ', label: '→', help: '' },
];

function tokenize(source) {
  const tokens = [];
  let i = 0;
  while (i < source.length) {
    const c = source[i];
    if (/\s/.test(c)) { i++; continue; }
    if (source.startsWith('<->', i) || source.startsWith('↔', i)) throw syntaxError('Biconditional is not supported', i);
    if (source.startsWith('->', i)) { tokens.push({type:'imp', pos:i}); i += 2; continue; }
    if (c === '→' || c === '⊃') { tokens.push({type:'imp', pos:i++}); continue; }
    if (c === '&' || c === '∧') { tokens.push({type:'and', pos:i++}); continue; }
    if (c === '|' || c === '∨') { tokens.push({type:'or', pos:i++}); continue; }
    if (c === '!' || c === '~' || c === '¬') { tokens.push({type:'not', pos:i++}); continue; }
    if (c === '□') { tokens.push({type:'box', pos:i++}); continue; }
    if (c === '◇') { tokens.push({type:'diamond', pos:i++}); continue; }
    if (c === '⊥') { tokens.push({type:'bot', pos:i++}); continue; }
    if (c === '(' || c === ')') { tokens.push({type:c, pos:i++}); continue; }
    const match = /^[A-Za-z_][A-Za-z0-9_]*/.exec(source.slice(i));
    if (match) {
      const raw = match[0];
      const word = raw.toLowerCase();
      const aliases = { box:'box', necessarily:'box', diamond:'diamond', possibly:'diamond', neg:'not', not:'not', false:'bot', bottom:'bot', and:'and', or:'or', imp:'imp', implies:'imp' };
      tokens.push({type:aliases[word] || 'prop', value:raw, pos:i});
      i += raw.length; continue;
    }
    throw syntaxError(`Unexpected character “${c}”`, i);
  }
  tokens.push({type:'eof', pos:source.length});
  return tokens;
}

function syntaxError(message, pos) {
  const error = new Error(`${message} at character ${pos + 1}.`);
  error.position = pos;
  return error;
}

function parse(source) {
  const tokens = tokenize(source);
  let index = 0;
  const peek = () => tokens[index];
  const take = (type) => {
    if (peek().type !== type) throw syntaxError(`Expected ${friendly(type)}`, peek().pos);
    return tokens[index++];
  };
  function atom() {
    const token = peek();
    if (token.type === 'prop') { index++; return {type:'prop', name:token.value}; }
    if (token.type === 'bot') { index++; return {type:'bot'}; }
    if (token.type === '(') { index++; const node = implication(); take(')'); return node; }
    throw syntaxError('Expected a proposition, unary operator, or “(”', token.pos);
  }
  function unary() {
    const token = peek();
    if (['not','box','diamond'].includes(token.type)) { index++; return {type:token.type, child:unary()}; }
    return atom();
  }
  function conjunction() {
    let node = unary();
    while (peek().type === 'and') { index++; node = {type:'and', left:node, right:unary()}; }
    return node;
  }
  function disjunction() {
    let node = conjunction();
    while (peek().type === 'or') { index++; node = {type:'or', left:node, right:conjunction()}; }
    return node;
  }
  function implication() {
    const left = disjunction();
    if (peek().type === 'imp') { index++; return {type:'imp', left, right:implication()}; }
    return left;
  }
  const result = implication();
  if (peek().type !== 'eof') throw syntaxError(`Unexpected ${friendly(peek().type)}`, peek().pos);
  return result;
}

function friendly(type) {
  return ({')':'“)”', imp:'implication', and:'conjunction', or:'disjunction', eof:'end of input'})[type] || type;
}

function pretty(node, parent = 0) {
  if (node.type === 'prop') return node.name;
  if (node.type === 'bot') return '⊥';
  if (node.type === 'not') return `¬${pretty(node.child, 4)}`;
  if (node.type === 'box') return `□${pretty(node.child, 4)}`;
  if (node.type === 'diamond') return `◇${pretty(node.child, 4)}`;
  const prec = {imp:1, or:2, and:3}[node.type];
  const op = {imp:'→', or:'∨', and:'∧'}[node.type];
  const rightParent = node.type === 'imp' ? prec : prec + 1;
  const text = `${pretty(node.left, prec + (node.type === 'imp' ? 1 : 0))} ${op} ${pretty(node.right, rightParent)}`;
  return prec < parent ? `(${text})` : text;
}

function serialize(node) {
  if (node.type === 'prop') return `Prop('${node.name.replaceAll("'", "\\'")}')`;
  if (node.type === 'bot') return 'Bot()';
  if (node.type === 'not') return `Imp(${serialize(node.child)}, Bot())`;
  if (node.type === 'box') return `Box(${serialize(node.child)})`;
  if (node.type === 'diamond') return `Diamond(${serialize(node.child)})`;
  if (node.type === 'and') return `And(${serialize(node.left)}, ${serialize(node.right)})`;
  if (node.type === 'or') return `Or(${serialize(node.left)}, ${serialize(node.right)})`;
  if (node.type === 'imp') return `Imp(${serialize(node.left)}, ${serialize(node.right)})`;
  throw new Error('Unknown formula node.');
}

function replaceAndTrack(state, regex, replacement) {
  const matches = [...state.text.matchAll(regex)];
  if (!matches.length) return state;
  let offset = 0;
  let text = state.text;
  let start = state.start;
  let end = state.end;
  for (const match of matches) {
    const originalStart = match.index + offset;
    const originalLength = match[0].length;
    const next = typeof replacement === 'function' ? replacement(match) : replacement;
    text = text.slice(0, originalStart) + next + text.slice(originalStart + originalLength);
    const delta = next.length - originalLength;
    const adjust = (position) => {
      if (position <= originalStart) return position;
      if (position >= originalStart + originalLength) return position + delta;
      return originalStart + next.length;
    };
    start = adjust(start);
    end = adjust(end);
    offset += delta;
  }
  return {text, start, end};
}

function normalizeInput() {
  let state = {text: input.value, start: input.selectionStart, end: input.selectionEnd};
  const replacements = [
    [/->/g, '→'], [/!/g, '¬'], [/&/g, '∧'], [/\|/g, '∨'],
    [/\bbox(?=\s|\(|$)/gi, '□'], [/\bdiamond(?=\s|\(|$)/gi, '◇'],
    [/\b(?:false|bottom)(?=\s|\)|$)/gi, '⊥'], [/\b(?:neg|not)(?=\s|\(|$)/gi, '¬'],
    [/\band(?=\s|\(|$)/gi, '∧'], [/\bor(?=\s|\(|$)/gi, '∨'],
    [/\b(?:imp|implies)(?=\s|\(|$)/gi, '→'],
  ];
  for (const [regex, replacement] of replacements) state = replaceAndTrack(state, regex, replacement);
  if (state.text !== input.value) {
    input.value = state.text;
    input.setSelectionRange(state.start, state.end);
  }
}

function updateEditor() {
  const source = input.value.trim();
  if (!source) {
    parsedFormula = null;
    $('parseStatus').textContent = 'Start typing a formula.';
    $('parseStatus').className = 'parse-status editor-status';
    $('editorShell').classList.remove('invalid');
    runButton.disabled = true;
    return;
  }
  try {
    parsedFormula = parse(source);
    $('parseStatus').textContent = 'Formula recognized — press Enter to prove.';
    $('parseStatus').className = 'parse-status editor-status';
    $('editorShell').classList.remove('invalid');
    runButton.disabled = false;
  } catch (error) {
    parsedFormula = null;
    $('parseStatus').textContent = error.message;
    $('parseStatus').className = 'parse-status editor-status bad';
    $('editorShell').classList.add('invalid');
    runButton.disabled = true;
  }
}

function currentWord() {
  const before = input.value.slice(0, input.selectionStart);
  const match = /[A-Za-z_]+$/.exec(before);
  return match ? {word:match[0], start:input.selectionStart - match[0].length} : {word:'', start:input.selectionStart};
}

function showSuggestions(force = false) {
  const {word} = currentWord();
  const lower = word.toLowerCase();
  const matches = suggestionItems.filter(item => force || (lower && item.key.startsWith(lower)));
  if (!matches.length) { suggestions.classList.add('hidden'); return; }
  suggestionIndex = 0;
  suggestions.innerHTML = '';
  matches.forEach((item, idx) => {
    const button = document.createElement('button');
    button.type = 'button';
    button.className = `suggestion${idx === 0 ? ' active' : ''}`;
    button.dataset.insert = item.insert;
    button.innerHTML = `<strong>${item.key} &nbsp; ${item.label}</strong>${item.help ? `<small>${item.help}</small>` : ''}`;
    button.addEventListener('mousedown', (e) => { e.preventDefault(); applySuggestion(item.insert); });
    suggestions.appendChild(button);
  });
  suggestions.classList.remove('hidden');
}

function applySuggestion(text) {
  const {start} = currentWord();
  const end = input.selectionStart;
  input.setRangeText(text, start, end, 'end');
  suggestions.classList.add('hidden');
  input.focus();
  updateEditor();
}

function moveSuggestion(delta) {
  const items = [...suggestions.querySelectorAll('.suggestion')];
  if (!items.length) return;
  suggestionIndex = (suggestionIndex + delta + items.length) % items.length;
  items.forEach((item, i) => item.classList.toggle('active', i === suggestionIndex));
}

input.addEventListener('input', () => { normalizeInput(); updateEditor(); showSuggestions(false); });
input.addEventListener('click', () => suggestions.classList.add('hidden'));
input.addEventListener('keydown', (event) => {
  const start = input.selectionStart;
  const end = input.selectionEnd;
  if (event.key === '(') {
    event.preventDefault();
    const selected = input.value.slice(start, end);
    const replacement = `(${selected})`;
    input.setRangeText(replacement, start, end, 'end');
    const caret = selected ? start + replacement.length : start + 1;
    input.setSelectionRange(caret, caret);
    updateEditor();
    suggestions.classList.add('hidden');
    return;
  }
  if (event.key === ')' && start === end && input.value[start] === ')') {
    event.preventDefault();
    input.setSelectionRange(start + 1, start + 1);
    return;
  }
  if (event.key === 'Backspace' && start === end && start > 0 && input.value[start - 1] === '(' && input.value[start] === ')') {
    event.preventDefault();
    input.setRangeText('', start - 1, start + 1, 'end');
    updateEditor();
    return;
  }
  if (event.ctrlKey && event.code === 'Space') { event.preventDefault(); showSuggestions(true); return; }
  if (!suggestions.classList.contains('hidden')) {
    if (event.key === 'ArrowDown') { event.preventDefault(); moveSuggestion(1); return; }
    if (event.key === 'ArrowUp') { event.preventDefault(); moveSuggestion(-1); return; }
    if (event.key === 'Tab') { event.preventDefault(); const active = suggestions.querySelector('.active'); if (active) applySuggestion(active.dataset.insert); return; }
    if (event.key === 'Escape') { suggestions.classList.add('hidden'); return; }
  }
  if (event.key === 'Enter' && !event.shiftKey) { event.preventDefault(); if (!runButton.disabled) runProver(); }
});

document.addEventListener('click', (event) => { if (!event.target.closest('.math-editor')) suggestions.classList.add('hidden'); });

document.querySelectorAll('[data-insert]').forEach(button => button.addEventListener('click', () => {
  const text = button.dataset.insert;
  input.setRangeText(text, input.selectionStart, input.selectionEnd, 'end');
  input.focus(); updateEditor();
}));

document.querySelectorAll('[data-example]').forEach(button => button.addEventListener('click', () => {
  input.value = button.dataset.example; input.focus(); input.setSelectionRange(input.value.length,input.value.length); normalizeInput(); updateEditor();
}));

$('clear').addEventListener('click', () => { input.value=''; input.focus(); updateEditor(); });
runButton.addEventListener('click', runProver);

function showPdfPreview(url, title) {
  const preview = $('pdfPreview');
  $('pdfPreviewTitle').textContent = title || 'Generated PDF';
  $('pdfPreviewOpen').href = url;
  $('pdfFrame').src = `${url}#view=FitH`;
  preview.classList.remove('hidden');
}

function clearPdfPreview() {
  $('pdfPreview').classList.add('hidden');
  $('pdfFrame').removeAttribute('src');
}

async function runProver() {
  updateEditor();
  if (!parsedFormula) return;
  const result = $('result');
  result.classList.remove('hidden');
  $('error').classList.add('hidden');
  $('artifactSection').classList.add('hidden');
  clearPdfPreview();
  $('artifacts').innerHTML = '';
  $('output').textContent = 'Running proof search…';
  $('verdict').textContent = 'Running…';
  runButton.disabled = true;
  try {
    const response = await fetch('/api/prove', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({formula:serialize(parsedFormula), compile_pdf:$('compilePdf').checked})});
    const data = await response.json();
    if (!response.ok || !data.ok) throw new Error(data.error || 'Request failed.');
    $('verdict').textContent = data.provable ? 'Provable' : 'Not provable';
    $('output').textContent = data.output || '(No console output)';
    if (!data.provable && data.countermodel_pdf_url) {
      showPdfPreview(data.countermodel_pdf_url, 'countermodel.pdf');
    } else if (!data.provable && data.countermodel_pdf_error) {
      $('error').textContent = data.countermodel_pdf_error;
      $('error').classList.remove('hidden');
    }
    if (data.artifacts.length) {
      $('artifactSection').classList.remove('hidden');
      for (const file of data.artifacts) {
        const link = document.createElement('a'); link.href=file.url; link.target='_blank'; link.rel='noopener';
        const label=document.createElement('span'); label.textContent=file.name;
        const kind=document.createElement('strong'); kind.textContent=file.kind.toUpperCase();
        link.append(label,kind);
        if (file.kind.toLowerCase() === 'pdf') {
          link.classList.add('pdf-file');
          link.title = 'Preview PDF';
          link.addEventListener('click', (event) => {
            event.preventDefault();
            showPdfPreview(file.url, file.name);
            $('pdfPreview').scrollIntoView({behavior:'smooth', block:'start'});
          });
        }
        $('artifacts').appendChild(link);
      }
    }
  } catch (error) {
    $('verdict').textContent = 'Could not run';
    $('error').textContent=error.message; $('error').classList.remove('hidden'); $('output').textContent='';
  } finally { updateEditor(); }
}

updateEditor();
