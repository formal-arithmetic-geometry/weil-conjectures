## Worker report

The module `Sheaf/AlgebraicGeometry/QuasiAffineBaseChange.lean` states
`AlgebraicGeometry.isQuasiAffineHom_baseChange`.  It uses the upstream relative
quasi-affine notion `AlgebraicGeometry.IsQuasiAffineHom` and the Mathlib fibre
product projection `CategoryTheory.Limits.pullback.snd`.

The node hypothesis that `f : X → S` is quasi-affine is rendered by the explicit
hypothesis `hf : IsQuasiAffineHom f`.  The arbitrary base-change morphism is
`g : S' ⟶ S`, with no finite-presentation, quasi-compactness, or
quasi-separatedness hypothesis.  The conclusion that the projection from the
fibre product is quasi-affine is rendered as
`IsQuasiAffineHom (pullback.snd f g)`.  The schemes are all in the same explicit
universe `Scheme.{u}`; this includes empty schemes and arbitrary base changes.

The dependency declarations used are:

* `AlgebraicGeometry.IsQuasiAffineHom`, from
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` (the recorded
  declaration for `def-nagata-quasi-affine-morphism`).
* `AlgebraicGeometry.Scheme`, from Mathlib (the recorded `mathlib_match` for
  `def-pc-scheme`).
* `CategoryTheory.Limits.pullback` and `.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (the recorded
  `mathlib_match` for `def-pc-fibre-product`).

Edge cases checked: taking `g = 𝟙 S` gives the original projection up to the
chosen pullback; taking `X` or `S'` empty is allowed by the scheme type; no
assumption on the index or on finite presentation is introduced.

Searches actually run in this worker session:

* `msearch.py N0 lem-trf-quasi-affine-base-change leanfinder
  'Base change of a quasi-affine morphism of schemes is quasi-affine'`:
  eight hits, including affine stability, quasi-compact stability, and absolute
  quasi-affine permanence; none states the relative theorem.
* `msearch.py N0 lem-trf-quasi-affine-base-change loogle '"IsQuasiAffine"'`:
  twelve hits in the absolute `Scheme.IsQuasiAffine` API; no relative theorem.
* `msearch.py N0 lem-trf-quasi-affine-base-change grep
  'IsQuasiAffineHom|quasi.affine.*base.change|base.change.*quasi.affine'
  AlgebraicGeometry`: zero Mathlib hits.
* `rg -n 'lem-trf-quasi-affine-base-change|IsQuasiAffineHom'` in the upstream
  `WeilConjectures/` and shared `lean/Sheaf/`, and a further upstream grep for
  the relative class with `QuasiCompact` or `QuasiSeparated`: the upstream file
  `WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean`, lines 230–241,
  gives `IsQuasiAffineHom.of_isPullback` and an instance for `pullback.snd`.
  Both require explicit quasi-compactness and quasi-separatedness assumptions.
  They therefore do not have this node's exact signature. No shared theorem
  or upstream reference to the assigned node id was found.
* `rg` of the node id in `dag/lean_names_upstream.json`: no hit.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-base-change-quasi-affine`, lines 2317–2340. It quantifies over any `g`,
with no finite-presentation hypothesis. The source proof is rendered step by
step in the theorem docstring, naming all five proof-dependency nodes. Among
those proof dependencies, `lem-weil-pbc-relative-spec-base-change` has the
recorded module `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`, imported
non-publicly as required. Its source and current server source were read.
The other proof dependencies have no recorded Lean module in this checkout.

The relative class was read at upstream lines 79–84, with its full docstring:
every inverse image of an affine open is a quasi-affine scheme. Mathlib's
absolute class includes compactness and its canonical open embedding into the
spectrum of global sections, giving exactly the stated convention. The
`Scheme` and `Scheme.Hom` definitions and the full pullback/projection signatures
were also read. The empty scheme and arbitrary identity base change remain
included; the quasi-affine hypothesis is substantive (it excludes, for example,
a positive-dimensional projective scheme over a field).

The only postponed theorem is `AlgebraicGeometry.isQuasiAffineHom_baseChange`,
with proof `sorry`. No new definition, dependency repair, statement correction,
or disputed statement is needed. Initial preflight rejected the recorded
signature's trailing `:= by` and a missing declaration blueprint marker; both
were corrected. Compilation and final delivery preflight are performed using
the prescribed wrappers.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
