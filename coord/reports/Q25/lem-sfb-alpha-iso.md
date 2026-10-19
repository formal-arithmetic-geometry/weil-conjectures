## Worker report

Recorded an exact existing declaration; no Lean module, definition, theorem, or proof is added.
The declaration is `AlgebraicGeometry.ProEtale.isIso_condensedPullbackHom` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, published framework source
lines 592–594 (local side snapshot lines 404–406). Read the complete surrounding section,
its docstrings, and current server source using `scompile.py --source`.

The current blueprint source is
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/lem-sfb-alpha-iso.md`
and its companion proof. Its front matter names this exact declaration.

Hypothesis and clause correspondence:

- A condensed ring Λ is a ring object `[MonObj Λ]` on
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`. This is the precise encoding
  used by the recorded dependency. The existing instance elaborates without the unused
  ring-object parameter; it is the same isomorphism assertion for every underlying
  condensed abelian group and hence applies to every condensed ring. There is no
  commutativity, nontriviality, or characteristic hypothesis.
- Any morphism of schemes is `{X Y : Scheme.{u}} (f : X ⟶ Y)` in the section.
  No finiteness, properness, smoothness, or immersion assumption occurs.
- The arrow α_f is exactly `condensedPullbackHom Λ f`, the declaration already recorded
  by `def-sfb-alpha`, with domain
  `(f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y)` and codomain `condensedRingObj Λ X`.
- The conclusion “is an isomorphism” is `IsIso (condensedPullbackHom Λ f)`.
  This is the isomorphism of the underlying abelian sheaves specified by the node;
  the existing `isMonHom_condensedPullbackHom` also gives its ring compatibility.

Dependency declarations, all in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
`def-sfb-alpha` records `AlgebraicGeometry.ProEtale.condensedPullbackHom`;
`def-sfb-pullback-from-point-comp-iso` records
`AlgebraicGeometry.ProEtale.upperStarFromPointComp`. Both lean records and signatures
were read. The former is the component at Λ of the latter via `Functor.compAlgHom`.
The latter has type
`upperStarFromPoint Y ⋙ (f)^*[Ab.{u + 1}] ≅ upperStarFromPoint X` and is the inverse
composition comparison whiskered with `pointUpperStar`, followed by the identification
induced by `comp_toSpecZ f`. No dependency repair is needed.

The existing proof follows the node's proof exactly: take the inverse component of
`upperStarFromPointComp f` at Λ. Its two composites with the forward component are the
identity components, so `CategoryTheory.NatIso.hom_app_isIso` supplies `IsIso`.
The existing body is `inferInstanceAs (IsIso ((upperStarFromPointComp f).hom.app Λ))`.
No new proof is supplied in this stage-2 delivery.

Edge cases checked: the identity morphism, empty source or target whenever a scheme
morphism exists, zero condensed ring, noncommutative rings, and arbitrary characteristic.
All are covered by the arbitrary-morphism/component formulation; no inhabitance, nonzero,
or geometric condition is used. The single explicit universe u and coefficient universe
u+1 are exactly those of the recorded dependencies and the published framework.

Searches on 2026-10-18:

- `msearch.py ... leansearch "canonical pullback of a condensed coefficient ring along a
  scheme morphism is an isomorphism"`: eight hits concerning scheme structure sheaves,
  module pullback, and unrelated comparisons; no specialized condensed coefficient result.
- `msearch.py ... leanfinder "Every component of a natural isomorphism of functors is an
  isomorphism"`: eight hits, including `CategoryTheory.NatIso.hom_app_isIso`.
- `msearch.py ... loogle '"hom_app_isIso"'`: exact generic component instance, one hit;
  read `Mathlib/CategoryTheory/NatIso.lean` lines 99–101 and its full signature.
- `msearch.py ... grep 'condensedPullbackHom|isIso_condensedPullbackHom'`: no Mathlib hits.
- `rg -n 'condensedPullbackHom|isIso_condensedPullbackHom|lem-sfb-alpha-iso'` over the
  read-only upstream source, side `lean/Sheaf`, and side `lean/WeilConjectures`: the
  older upstream tree has no declaration; side framework Basic.lean contains the exact
  definition and instance; Sheaf contains consumers, no second declaration.
- `rg -n 'isIso_condensedPullbackHom' dag/lean_names_upstream.json`: no hit in that older
  index. Current published source and compiler checks are authoritative here.

No statement dispute, correction, new node, or dependency module.

## Second reading by Q25

This is a disclosed self-check, not an independent review; the maintainer's independent
reader reviews the delivered binding. Reopened the node, current blueprint text, dependency
records, and published source. Matched Λ, arbitrary X/Y/f, the exact direction and identity
of α_f, and the `IsIso` conclusion as above. The source instance has no additional geometric
hypotheses. The potentially confusing section `[MonObj Λ]` does not survive elaboration
because the underlying map and isomorphism are defined without it. No mismatch was found,
and only the item's `lean` field changes. No module is duplicated.

Validation: `scompile.py Q25 lem-sfb-alpha-iso scratch/ExistingCheck.lean` passed
both sandbox and library checks without warnings (2.4 seconds each). `#print` confirms
that the instance and coefficient map quantify over Λ and arbitrary scheme morphisms,
with no ring-structure argument. `#print axioms` for the exact instance reports only
`propext`, `Classical.choice`, and `Quot.sound`. The scratch probe is not delivered.
