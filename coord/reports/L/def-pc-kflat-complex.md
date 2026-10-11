# def-pc-kflat-complex (L, stage 2)

## Worker report

Worker W-kfl0542 (group L), item `def-pc-kflat-complex`. File `lean/.sandbox/L/KFlatComplex.lean`,
to land as `lean/Sheaf/Algebra/Homology/KFlat.lean` (module `Sheaf.Algebra.Homology.KFlat`).
Compiles clean (`Compiled in 2.4 s`, no warning) with `tools/lean_file.sh`.

### What the module defines

- `CochainComplex.IsKFlat K : Prop` and `CochainComplex.IsKFlatResolution (f : K ⟶ G) : Prop`.
- Two named instances with `sorry` (Prop, needed to form `mapBifunctor` with the sheaf tensor):
  `SheafOfModules.preservesZeroMorphisms_curriedTensor` (`0 ▷ M = 0`) and
  `SheafOfModules.preservesZeroMorphisms_curriedTensor_obj` (`M ◁ 0 = 0`). The source proves
  no `MonoidalPreadditive` for `SheafOfModules.monoidalCategory`; their docstrings carry the proof.

### Clause by clause

| Node | Lean |
|---|---|
| site `C`, sheaf of commutative rings `O` | `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}` |
| sheaves of `O`-modules | `SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)` (Mathlib; abelian by `SheafOfModules.instAbelian`) |
| cochain complex of `O`-modules [def-pc-cochain-complex-modules] | `CochainComplex (SheafOfModules …) ℤ` |
| acyclic [def-pc-acyclic-complex-modules] | `HomologicalComplex.Acyclic` (`F.Acyclic`) |
| `⊗_O` | `SheafOfModules.monoidalCategory R` (source `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`: sheafification of the presheaf tensor `PresheafOfModules.Monoidal`), used via `letI` since it is not an instance |
| `Tot(F ⊗_O K)` [def-pc-tensor-complex-sheaves] | `CochainComplex.mapBifunctor F K (curriedTensor _)` = `HomologicalComplex.mapBifunctor F K (curriedTensor _) (ComplexShape.up ℤ)`, signs `ε₂(p,q) = (-1)^p` as the dependency records |
| K-flat: `∀` acyclic `F`, `Tot(F ⊗ K)` acyclic | `∀ F, F.Acyclic → (mapBifunctor F K (curriedTensor _)).Acyclic` (F on the left, as in 06YN) |
| K-flat resolution: quasi-iso `K → G` [def-pc-quasi-iso-modules] with `K` K-flat | `QuasiIso f ∧ K.IsKFlat` |

Universes: the site and the coefficients share `u` (`C : Type u`, `Category.{u}`, modules in
`Type u`); this is the setting in which the source proves `SheafOfModules.isMonoidal_W` and in
which `HasSheafify J AddCommGrpCat.{u}`, `J.WEqualsLocallyBijective AddCommGrpCat.{u}` and the
countable coproducts for `HasMapBifunctor` are instances. Every Stacks site (a set-sized category)
is covered by choosing `u`. No other hypothesis is added.

Edge cases: `K = 0` (K-flat, its tensor complexes vanish), `F = 0` (acyclic), empty site (all
categories trivial) are all within the binders.

### Searches

- Mathlib: `grep -rln 'MonoidalCategory\|Monoidal' Mathlib/Algebra/Category/ModuleCat/Sheaf/`:
  none; only `Presheaf/Monoidal.lean` (`MonoidalCategory (PresheafOfModules (R ⋙ forget₂ …))`).
  No K-flat notion in Mathlib (node's `mathlib_searches`; `KInjective`/`KProjective` only).
- Source: `grep -rln 'KFlat\|kFlat\|IsKFlat' WeilConjectures`: `FromJoel/CategoryTheory/Monoidal/KFlat.lean`
  defines `MorphismProperty.kFlat W X := localizerMorphism W W (tensorLeft X) ∧ … (tensorRight X)`
  and `FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean` `CochainComplex.KFlat A :=
  (quasiIso A (.up ℤ)).KFlat` for an abelian `A` with `[MonoidalCategory A] [MonoidalPreadditive A]`
  and `GradedObject` tensor hypotheses: "tensoring on both sides preserves quasi-isomorphisms",
  not the node's "tensoring with acyclic complexes gives acyclic complexes" (equivalent only by a
  cone argument), and not instantiated for `SheafOfModules` (no `MonoidalPreadditive` there);
  its uses are étale/pro-étale sheaves (`SixFunctors/…`). So not `existing`.
- Source tensor of sheaves of modules on a site:
  `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`, `SheafOfModules.monoidalCategory`
  (and `symmetricCategory`, `tensorObjIsoSheafification`); used here.
- Names: `IsKFlat`, `IsKFlatResolution`, `preservesZeroMorphisms_curriedTensor` absent from Mathlib,
  `WeilConjectures/`, `lean/Sheaf` and `dag/lean_names_upstream.json` (grep, 0 hits).

### Notes for the lead

- The node `def-pur-sheaf-tensor-product` (status split, no `lean`, no `mathlib_match`) is the
  source's `SheafOfModules.monoidalCategory` (`existing: true` candidate, same universe caveat).
- The prompt cited Tag 06YB; that tag is `cohomology-lemma-check-K-flat-stalks`. The node and
  the file use 06YN (`sites-cohomology-definition-K-flat`) and 06YS.
- No WANTED, no STATEMENT-DISPUTED.

## Second reading by L

Independent review by R-kfl0545 (reviewer sub-agent of L): FIX (noncomputable dropped, signature corrected, docstring remark on the FromJoel notion); every clause matched.
