// Renaissance Labs Mathematics: theme toggle, copy buttons, map search. No dependencies.
(function () {
  var root = document.documentElement;
  var tbtn = document.getElementById('theme');
  if (tbtn) tbtn.addEventListener('click', function () {
    var dark = root.dataset.theme ? root.dataset.theme === 'dark' : matchMedia('(prefers-color-scheme: dark)').matches;
    root.dataset.theme = dark ? 'light' : 'dark';
    try { localStorage.setItem('theme', root.dataset.theme); } catch (e) {}
  });
  document.querySelectorAll('.copy').forEach(function (b) {
    b.addEventListener('click', function () {
      var text = b.parentNode.querySelector('pre').innerText;
      (navigator.clipboard ? navigator.clipboard.writeText(text) : Promise.reject()).then(function () {
        b.textContent = 'Copied'; setTimeout(function () { b.textContent = 'Copy'; }, 1400);
      }, function () { b.textContent = 'Select and copy'; });
    });
  });
  var q = document.getElementById('q');
  if (!q) return;
  var tiles = Array.prototype.slice.call(document.querySelectorAll('.tile'));
  var rows = Array.prototype.slice.call(document.querySelectorAll('.chart .row'));
  var qn = document.getElementById('qn');
  function run() {
    var terms = q.value.toLowerCase().split(/\s+/).filter(Boolean), hits = 0;
    tiles.forEach(function (t) {
      var ok = terms.every(function (x) { return t.dataset.s.indexOf(x) >= 0; });
      t.classList.toggle('dim', terms.length > 0 && !ok);
      if (terms.length && ok) hits++;
    });
    rows.forEach(function (r) { r.classList.toggle('dim', terms.length > 0 && !r.querySelector('.tile:not(.dim)')); });
    qn.textContent = terms.length ? hits + (hits === 1 ? ' area' : ' areas') : '';
  }
  q.addEventListener('input', run);
  q.addEventListener('keydown', function (ev) {
    if (ev.key === 'Enter') { var first = document.querySelector('.tile:not(.dim)'); if (first && q.value) location.href = first.href; }
  });
})();
