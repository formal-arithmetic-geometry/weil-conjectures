# def-pc-projective-morphism (L, stage 2)

## Worker report

Worker W-prj0530 for L, stage 2, item `def-pc-projective-morphism`. Sandbox file
`lean/.sandbox/L/ProjectiveMorphism.lean`, to land as
`lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean` (module
`Sheaf.AlgebraicGeometry.Morphisms.Projective`). Compiles clean (`Compiled in 1.6 s`, no
warning); a probe copy with `#print` confirmed both classes elaborate as intended.

The module defines two Prop-valued classes in namespace `AlgebraicGeometry`:
`IsHProjective f` and `IsProjective f` (extends `IsHProjective f`, `QuasiCompact f`).

Clause by clause:
- "f : X → S a morphism of schemes [def-pc-scheme]": `{X S : Scheme.{u}} (f : X ⟶ S)`
  (Mathlib `AlgebraicGeometry.Scheme`, `Scheme.Hom`); universe `u` bound.
- "for some integer n ≥ 0": `∃ (n : ℕ)`.
- "a closed immersion i : X ↪ P^n_S [def-weil-closed-immersion]":
  `(i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)), IsClosedImmersion i` (Mathlib
  `AlgebraicGeometry.IsClosedImmersion`).
- "projective space over S [def-nagata-projective-space-base-change]": the recorded
  `AlgebraicGeometry.ProjectiveSpace` (module `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`),
  notation `ℙ(n; S)`, where `n : Type u` indexes the *homogeneous* coordinates; the dependency
  node itself says the classical `P^r_S` is `P({0,…,r}; S)`, so `P^n_S` is
  `ℙ(ULift.{u} (Fin (n + 1)); S)` (the `ULift` lifts `Fin` into `Type u`, as the source's
  `ProjectiveLine` does with `ULift (Fin 2)`).
- "f = π ∘ i, π the structural morphism": `i ≫ ℙ(…; S) ↘ S = f`, where `↘ S` is the
  `CanonicallyOver` instance `ProjectiveSpace.over` (`hom := pullback.fst`), the first projection,
  as the dependency node says.
- "projective if H-projective and quasi-compact [def-weil-finite-type-morphism]":
  `class IsProjective … extends IsHProjective f, QuasiCompact f` (Mathlib `QuasiCompact`).
- "X over a field k is projective over k when X → Spec k is projective": no new declaration;
  it is `IsProjective (X ↘ Spec (.of k))` (for `[X.Over (Spec (.of k))]`), stated in the module
  docstring and in the docstring of `IsProjective`, as `def-weil-finite-type-morphism`'s record
  does for finite type over a field.

Edge cases: `n = 0` allowed (`ℙ(ULift (Fin 1); S) ≅ S`, so closed immersions into `S` are
H-projective); the empty `X` is H-projective (the empty map is a closed immersion);
`n` is a natural number so `ℙ` is never the empty-coordinate space. The node's same_as
`def-kun-projective` (no quasi-compactness) is H-projective here; the blueprint's projective
is `IsProjective`, the recorded `declaration`.

Searches for an existing definition:
- grep `IsProjective|HProjective|Projective f|class.*Projective` in
  `~/weil-conjectures-slopmaster2/WeilConjectures`: only module-theoretic `IsProjective`
  (`ModuleCat`); `WeilConjectures/Blowup/Affine/Projective.lean:49` says explicitly
  "this Mathlib has no morphism class `IsProjective` for schemes".
- grep `(def|abbrev|class|structure) IsProjective|IsHProjective` in Mathlib and the source:
  only `IsProjective.iff_projective` (ModuleCat, a theorem); `Mathlib/AlgebraicGeometry` has
  no projective-morphism predicate (ProjectiveSpectrum/Proper.lean is properness of Proj).
- `dag/lean_names_upstream.json`: no `AlgebraicGeometry.IsProjective` / `IsHProjective`.
- The node's stage-1 searches (LeanFinder, Loogle "projective", grep Mathlib): no match.
The names `AlgebraicGeometry.IsHProjective` and `AlgebraicGeometry.IsProjective` are free.

No STATEMENT-DISPUTED; no node fault.

## Second reading by L

Independent review by R-prj0536 (reviewer sub-agent of L): PASS; every clause matched.
