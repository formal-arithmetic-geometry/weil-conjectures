## Worker report

The module `Sheaf.TraceFormula.EtaleModuleFinitePresentationLocal` states
`AlgebraicGeometry.Scheme.Modules.etale_module_finite_presentation_local`. It uses
`g : X' ⟶ X`, marked points `x : X` and `x' : X'`, the marked-point equation
`g x' = x`, the étale class `[Etale g]`, and the residue-field isomorphism class
`[IsIso (g.residueFieldMap x')]`. The module `M : X.Modules` carries exactly the
quasi-coherence hypothesis `[M.IsQuasicoherent]`. The conclusion is the iff in the
node: there is an open `U : X.Opens` containing `x` on which `(M.over U)` is of
finite presentation exactly when there is an open `U' : X'.Opens` containing `x'`
on which `((tensorPullback g).obj M).over U'` is of finite presentation.

The Lean rendering of each hypothesis and clause is:

* the schemes and morphism are `{X X' : Scheme.{u}}` and `g : X' ⟶ X`;
* the marked points are `x : X` and `x' : X'`, with `_hx : g x' = x`;
* étaleness is `[Etale g]` and the residue-field condition is
  `[IsIso (g.residueFieldMap x')]`;
* quasi-coherence is `[M.IsQuasicoherent]` for `M : X.Modules`;
* the first clause is
  `∃ U : X.Opens, x ∈ U ∧ (M.over U).IsFinitePresentation`;
* the second clause is
  `∃ U' : X'.Opens, x' ∈ U' ∧
  ((tensorPullback g).obj M |>.over U').IsFinitePresentation`.

Statement dependencies used: `def-weil-etale-morphism` via Mathlib's
`AlgebraicGeometry.Etale` (import `Mathlib.AlgebraicGeometry.Morphisms.Etale`),
`def-weil-residue-field` via `AlgebraicGeometry.Scheme.residueField` and
`Scheme.Hom.residueFieldMap` (import `Mathlib.AlgebraicGeometry.ResidueField`),
`pqf-def-coherent` via `Sheaf.AlgebraicGeometry.CoherentFiniteType` and the
underlying Mathlib `SheafOfModules.IsQuasicoherent`,
`def-weil-pbc-module-finite-type-presentation` via Mathlib's
`SheafOfModules.IsFinitePresentation`, and `def-pc-module-pullback` via
`AlgebraicGeometry.Scheme.Modules.tensorPullback` from
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.

Edge cases checked: `U` and `U'` are arbitrary opens, so the empty-open and
zero-module cases are represented; no nonemptiness or finite-type hypothesis is
introduced. The marked points are arbitrary points, and the residue-field
isomorphism is retained as a typeclass hypothesis. The universe is shared by both
schemes, as in the dependency declarations, and no case is excluded by an
independent smaller universe.

Searches for an existing declaration: `msearch.py leanfinder` with
“finite presentation of a module is local for an etale neighbourhood” and with
“finite presentation of modules under etale pullback finite pushforward and stalk
localization” returned general `SheafOfModules.IsFinitePresentation` and
`Algebra.Etale.finitePresentation`, but no theorem with this marked-point
neighbourhood iff. `msearch.py loogle` with `SheafOfModules.IsFinitePresentation`
and `Module.FinitePresentation` returned only the general classes and module
lemmas. `msearch.py grep` for `finite.*presentation|FinitePresentation` in
Mathlib finiteness files and `rg` over `WeilConjectures` and `lean/Sheaf` found no
matching étale-local theorem. The existing `ElementaryDevissageFinitePresentation`
module uses this exact neighbourhood shape only as a proof dependency, so it does
not duplicate this declaration.

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by Q03

I reread the node JSON, its source locator (Stacks flat.tex, Tag 057T), and the
module signature. The Lean has exactly the two schemes, the étale morphism, both
marked points, the equation identifying their images, the étale hypothesis, the
residue-field isomorphism, and one quasi-coherent module. Each side of the iff has
one open neighbourhood, membership of the marked point, and the finite-presentation
predicate on the corresponding restriction. Pullback is the recorded canonical
`tensorPullback`, so no arbitrary map or extra finite-type condition is present.
The empty-open, zero-module, arbitrary-point, and universe cases remain allowed.
No mismatch was found and no change was needed after the reread.
