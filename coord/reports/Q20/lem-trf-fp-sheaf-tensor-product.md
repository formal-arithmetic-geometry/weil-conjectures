## Worker report

Item: `lem-trf-fp-sheaf-tensor-product`, group Q20, 2026-10-24 UTC.

The module `Sheaf.AlgebraicGeometry.Modules.FinitePresentationTensorProduct` states
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorProduct`. Its whole proof
is `sorry`, as required for stage 2. It introduces no definitions or instances.
The node is changed only in `lean`; its statement, dependency lists and proof remain intact.

Source checked: `literature/stacks-project/modules.tex`, lines 2440--2520,
Tag 01CE, `lemma-tensor-product-permanence`, clause (4) and the displayed
presentation in its proof. This is the scheme specialization of that clause.
The source imposes neither flatness nor Noetherian hypotheses.

Hypothesis and clause correspondence:

- A scheme X: `{X : Scheme.{u}}`, using Mathlib's `AlgebraicGeometry.Scheme`.
  The universe `u` is explicitly declared and arbitrary.
- Two sheaves of O_X-modules on the Zariski site: `(F G : X.Modules)`.
  `Scheme.Modules` is Mathlib's `SheafOfModules.{u} X.ringCatSheaf`, where the site
  is the opens of X with the usual open-cover topology. This is the same sheaf
  category as `CategoryTheory.ringedSiteModules` in the recorded dependency,
  not a new category or a restriction to globally presented modules.
- The local finite-presentation condition for H: `H.IsFinitePresentation` is
  `SheafOfModules.IsFinitePresentation` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` (line 267).
  Its `QuasicoherentData` is an open covering with a `Presentation` on each slice;
  `Presentation.IsFinite` requires finite generator and relation index types.
  `Presentation.isColimit` gives the cokernel of the map from the free relations
  module to the free generators module. Conversely `presentationOfIsCokernelFree`
  constructs those generators and relations from a finite-free cokernel sequence.
  Thus it is precisely the node's local exact O_U^m -> O_U^n -> H|U -> 0,
  with arbitrary finite nonnegative ranks. The existence of an open covering is
  equivalent to the stated neighbourhood condition at every point.
  This notion already has DAG node `def-weil-pbc-module-finite-type-presentation`;
  no duplicate predicate or definition node is needed. The item defines it inline,
  so its dependency list is preserved.
- F finitely presented: `[F.IsFinitePresentation]`.
- G finitely presented: `[G.IsFinitePresentation]`.
- Their sheaf tensor product: `F ⊗ G`, for the existing monoidal structure on
  `X.Modules` in `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (line 128).
  Its object construction is `SheafOfModules.monoidalCategory X.sheaf`, the
  localization/sheafification of the sectionwise tensor, as in the recorded tensor
  dependency. The public import of
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` retains that
  dependency's existing generalized tensor interface; no tensor is reconstructed.
- Conclusion: `(F ⊗ G).IsFinitePresentation`, the same local predicate on the
  actual sheaf tensor product. There is no invertibility, flatness, affine,
  quasi-compactness, nonemptiness or Noetherian hypothesis.

Statement dependency declarations used/read:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declaration
  `AlgebraicGeometry.Scheme` (and its recorded `Scheme.Hom`).
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, declaration
  `CategoryTheory.ringedSiteModules`, transparently `SheafOfModules`; the
  scheme specialization is Mathlib's `AlgebraicGeometry.Scheme.Modules`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, declaration
  `SheafOfModules.cochainModulesMonoidal`, together with the recorded symmetric,
  additive and colimit-preserving structure on the same localization tensor.
  For schemes the existing `Scheme.Modules` monoidal instance exposes that tensor.

The following recorded proof dependencies are imported nonpublicly for stage 3:

- `Mathlib.AlgebraicGeometry.Modules.Sheaf`:
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, `restrictAdjunction`.
- `WeilConjectures.Algebra.Homology.ModuleStalkExact`:
  `AlgebraicGeometry.RingedSpace.module_stalk_exact`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`:
  `SheafOfModules.tensor_bilinear_universal`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor`:
  `SheafOfModules.stalkTensorIso`.
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`:
  `LinearMap.rTensor_exact`, `LinearMap.lTensor_exact`, together with
  `LinearMap.rTensor_surjective` and `LinearMap.lTensor_surjective`.
- `WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`:
  `AlgebraicGeometry.Scheme.Modules.exists_restriction_tensor_comparison`.

The theorem docstring includes all four proof steps: restrict two presentations to
one neighbourhood, construct the tensor presentation with ranks ms+nr and ns,
check its exactness by the two-lift stalk kernel chase, and use the canonical
restriction comparison and the stalk exactness criterion to obtain local finite
presentation. No flatness is used in the right-exactness argument.

Edge cases checked mathematically before drafting:

- The empty scheme: its empty covering satisfies the local predicate; no
  nonempty scheme binder or selected point occurs in the theorem.
- Zero sheaves and zero free ranks: finite index types in Mathlib may be empty;
  both input presentations and the ranks ms+nr and ns permit zero.
- Finite free factors (m = r = 0): the rank ns tensor presentation is included.
- Nonflat factors: on Spec Z, the sheaves associated to Z/2 and Z/2 have tensor
  associated to Z/2 and satisfy the conclusion. The proof uses right exactness,
  not left exactness; these factors need not be invertible.
- Schemes with non-Noetherian rings are included: the construction uses only
  finite presentations and stalkwise right exactness.

Searches for existing notions/statements, all on 2026-10-24:

- `msearch.py ... leansearch "Tensor product of finitely presented sheaves of modules
  is finitely presented"`: eight hits. These include ordinary module scalar
  extension `instFinitePresentationTensorProduct`, ordinary finite generation,
  `Module.Relations.tensor`, presheaf tensor objects, and the sheaf predicate.
  None states the scheme sheaf permanence assertion.
- `msearch.py ... leanfinder "The tensor product of two finitely presented sheaves
  of modules on a scheme is finitely presented"`: eight hits, consisting of
  sheaf finite-presentation predicates/presentation data and ordinary module
  scalar extension. No exact theorem.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation,
  SheafOfModules.tensorObj"`: no hits, unknown identifier `SheafOfModules.tensorObj`.
  Retried with `"SheafOfModules.IsFinitePresentation"`: five hits consisting of
  the predicate, its constructor/local data and implications to finite type and
  quasi-coherence. Used the existing predicate.
- `msearch.py ... grep "IsFinitePresentation|isFinitePresentation"
  Algebra/Category/ModuleCat/Sheaf`: five hits in `Quasicoherent.lean`, defining
  the sheaf predicate and the finite condition on local presentation data.
- `rg -n "FinitePresentation.*tensor|finitePresentation.*tensor|
  isFinitePresentation_tensor|tensor.*[Ff]initePresentation"` in Mathlib's module
  sheaf sources and both project roots: found pullback and scalar-extension
  results, and `Scheme.Modules.isFinitePresentation_tensorObj` in upstream
  `AlgebraicGeometry/Modules/ProjectionFormula.lean`. Read its full signature:
  it assumes `[N.IsInvertible]` and is not this two-finitely-presented-factor
  statement. The stage-1 split report had identified the same distinction.
- `rg -n "lem-trf-fp-sheaf-tensor-product" lean/WeilConjectures`: no hits.
- `rg -n "isFinitePresentation_tensorProduct"` across Mathlib and both project
  roots: no pre-existing declaration with the selected name.
- Searched DAG definition records for finite-presentation notions: ordinary
  modules and module objects are distinct; the exact local sheaf predicate is
  already recorded at `def-weil-pbc-module-finite-type-presentation`.

No statement dispute, source mismatch, dependency repair, or new node is needed.

Validation: the prescribed `scompile.py Q20 lem-trf-fp-sheaf-tensor-product <file>`
compiled the module cleanly in both sandbox (23.4 s) and library (5.3 s) naming
modes, each within 60 seconds. All universes/variables are explicit; `autoImplicit`
is disabled. The only postponed proof is the one named theorem above.

## Second reading by Q20

Independent clause-by-clause reading (maintainer reviewer, 2026-10-24), replacing the
delivered section, which was the dispatched worker's own second pass (delivery-errors H11;
brief-stage2 requires a reading by another worker). Node, Stacks place and Lean file open.

Source: `literature/stacks-project/modules.tex` lines 2440-2459, Tag 01CE
`lemma-tensor-product-permanence`, clause (4): ringed space, F and G of finite
presentation, then F ⊗_{O_X} G of finite presentation. No other hypothesis.

Node statement as a list, with its Lean rendering:

1. X a scheme [def-pc-scheme] — `{X : Scheme.{u}}`, Mathlib `AlgebraicGeometry.Scheme`, the
   recorded declaration. Arbitrary universe u. Correct.
2. F, G sheaves of O_X-modules on the Zariski site [def-weil-sheaf-of-modules-category] —
   `(F G : X.Modules)`; `Scheme.Modules X = SheafOfModules X.ringCatSheaf` on `Opens X`,
   which is the recorded `CategoryTheory.ringedSiteModules` (an abbrev of `SheafOfModules`)
   at the scheme's ring sheaf. Correct.
3. The finite-presentation notion "every point has an open U with an exact
   O_U^m → O_U^n → H|_U → 0, m, n finite" — Mathlib `SheafOfModules.IsFinitePresentation`:
   ∃ `QuasicoherentData` (a family of opens covering X, with a `Presentation` of each
   `H.over U_i`) all of whose presentations are finite (finite generator and relation
   index types). The presentation is a cokernel of the free map, so this is the node's
   local exact sequence; a covering family ⇔ a neighbourhood of every point. Ranks may be
   0 (empty Fin types). The node defines the predicate inline and does not cite a node for
   it; the same Mathlib predicate is already used by the project (e.g.
   `Scheme.Modules.isFinitePresentation_tensorObj`). The index universe u₁ of the class is
   left to universe generalization, as in the project's existing uses; the predicate is
   universe-invariant (`QuasicoherentData.shrink` down, `ULift` of the index up), so this is
   no restriction. Correct.
4. Hypotheses F, G finitely presented — `[F.IsFinitePresentation] [G.IsFinitePresentation]`.
   Nothing stronger: no invertibility, flatness, quasi-coherence, Noetherian, affine,
   quasi-compact or nonempty assumption. Correct.
5. F ⊗_{O_X} G [def-pur-sheaf-tensor-product] — `F ⊗ G` with the `MonoidalCategory X.Modules`
   instance of `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, which is
   `SheafOfModules.monoidalCategory X.sheaf` (localization of the sectionwise presheaf
   tensor along sheafification). The recorded dependency declaration
   `SheafOfModules.cochainModulesMonoidal` (CochainTensorUniverses:93) is literally
   `@monoidalCategory … R … (cochainTensorLocalizationIsMonoidal R)`, i.e. the same
   construction with a different (Prop) proof of `IsMonoidal`; whichever instance the
   elaborator selects, the tensor object is the same term up to proof irrelevance. The
   dependency's proof step 1 names this "existing specialized monoidalCategory". No new or
   different tensor. Correct.
6. Conclusion: F ⊗ G finitely presented — `(F ⊗ G).IsFinitePresentation`, same predicate.
   Correct; not weaker (not merely finite type / quasi-coherent), not stronger.

Edge cases: X empty (empty covering satisfies the predicate; theorem true and stated);
F or G = 0 (presentation with n = 0); m = r = 0 (locally free factors, rank ns); non-flat
factors such as Z/2 ⊗ Z/2 on Spec Z (no flatness used or assumed); non-Noetherian X.

One definition per notion: searched side-live lean/Sheaf and lean/WeilConjectures for
`IsFinitePresentation` together with `⊗`/`tensor`: only pullback results and
`Scheme.Modules.isFinitePresentation_tensorObj` (ProjectionFormula.lean:170), which assumes
`[N.IsInvertible]` — a special case, not this statement. `Sheaf.RingTheory.
FinitePresentationTensorProducts` concerns ordinary modules. No existing declaration; the
new module is justified.

Records: the item node differs from the live node only in `lean`; `lean.statement` is
verbatim the file's signature; module and declaration docstrings carry Tag 01CE and
`(blueprint: lem-trf-fp-sheaf-tensor-product)`; the declaration docstring carries the four
proof steps with the cited node ids. Proof is `sorry`; no definitions or instances; no new
nodes or dependency modules. Non-public imports are the proof_deps' modules.

Mismatches found: none in the Lean or the node. Changed: this section only.
