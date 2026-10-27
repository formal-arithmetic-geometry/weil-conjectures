## Worker report

Delivered `Sheaf.Paper.PrincipalCompleteHeartKernels`, with the transparent predicate
`CategoryTheory.PrincipalQuotientCompletion.Model.IsCompleteModule` and the theorem
`CategoryTheory.PrincipalQuotientCompletion.Model.complete_heart_kernels` (proof `sorry`).
The accepted N7 stage-1 split is preserved. The previous worker's unchanged-item
stage-1 refusal does not apply: the item has no Lean record and is stage 2 in the queue.
There is no released repair note for this item.

Hypothesis and clause matching:

- Any scheme T: `(T : AlgebraicGeometry.Scheme.{t})`; no qcqs, Noetherian or
  characteristic hypothesis. The site is exactly `Scheme.ProEt.topology T`.
- Fixed size convention: site objects have universe `t+1` and morphisms `t`.
  Coefficients and module sections have universe `max u (t+1)`, allowing arbitrary
  larger coefficient universes. `HasDerivedCategory.{w}` records the chosen
  localization morphism universe; all universes and variables are explicit.
- A sheaf of commutative rings: `R : Sheaf (Scheme.ProEt.topology T)
  CommRingCat.{max u (t+1)}`. The existing transparent
  `derivedChangeRingIndependentCoefficients` forgets commutativity only.
- A global section t: `a : (SheafOfModules.unit ...).sections`. This is a compatible
  family of sections, i.e. a global section. The regularity hypothesis is
  `_ha : Mono (globalSectionMultiplication R a)` on R, never on M or N.
- The ordinary unbounded derived category is `DerivedCategory` of
  `ringedSiteModules`, not a bounded or complete subcategory. Degree-zero modules
  use `DerivedCategory.singleFunctor _ 0`.
- Q_n, restriction of scalars, derived tensor and the strict reduction tower are
  precisely the existing `PrincipalQuotientCompletion.Model R a` interface. Its
  `quotientTower` tensors the cokernel of a^(n+1) with a representative, using the
  existing total sheaf tensor; this is the underlying R-module of tensor with the
  quotient ring, so the restriction of scalars has already been performed.
  Its `computes` clause requires the counit to be invertible on every K-flat
  representative. Its `quotientRoos` is `roosF` of that strict tower, not an
  arbitrary triangulated derived-limit choice. `unit`, `augmentation`,
  `coordinates` and `unit_computes` fix exactly the quotient-projection unit.
  Zero-based n means positive exponent n+1 throughout.
- The binder `F : Model R a` quantifies over presentations of that same canonical
  construction, including its universal property and unit normalization. It is
  not an extra property of R or a stronger assumption on the modules. Such models
  exist for exact countable products by the already recorded
  `CategoryTheory.PrincipalQuotientCompletion.nonempty_model` in
  `Sheaf.Algebra.Homology.PrincipalQuotientCompletionExists`; on this pro-etale
  site exact products are supplied by the recorded countable-products result.
  Nothing is chosen from a mere existence statement.
- Completeness is exactly `IsIso (F.unit.app ((DerivedCategory.singleFunctor _ 0).obj M))`;
  the helper definition has real data and introduces no alternative completion.
- Every g:M→N: the first conjunct quantifies over both objects and `g : M ⟶ N`,
  with precisely the two completeness premises. Its three conclusions use
  `Limits.kernel g`, `Limits.cokernel g` and `Limits.image g` in the ambient
  abelian module-sheaf category, respectively.
- Every short exact sequence: the second conjunct quantifies over `ShortComplex`
  S and assumes `S.ShortExact`; complete endpoints `S.X₁` and `S.X₃` imply complete
  middle term `S.X₂`. This includes all short exact sequences and no splitness
  assumption.
- No finiteness, constructibility or classical separatedness assumption, and
  no assertion about arbitrary submodules, is present.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  the underlying Mathlib `SheafOfModules` and its ambient Abelian instance.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; `singleFunctor` embeds modules at zero.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, used by the existing model's
  K-flat computation. `Mathlib.Algebra.Homology.BifunctorShift` supplies
  `CochainComplex.mapBifunctor`, the existing total tensor used by the quotient tower.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, whose underlying quotient module is the model's
  `principalQuotient` categorical cokernel.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`. These record the
  ordinary Roos triangle; the existing strict model supplies the augmentation
  required by this item's more specific unit.
- Added the already landed node `def-pur-principal-quotient-completion-model` to
  stmt_deps, using its module `Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel`
  and declaration `CategoryTheory.PrincipalQuotientCompletion.Model`. Read its
  full definition and the existing Koszul/quotient-tower definitions. No existing
  dependency needed an interface repair, and no new node was needed.

Available proof-dependency modules are imported privately:
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.Algebra.Homology.RoosConeCalculus`, and
`Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`.
The ordinary derived-category dependency is public through the model. The nodes
`lem-sfb-regular-principal-completion-fiber` and
`lem-sf-derived-homology-long-exact` have no Lean record at this reading and
therefore no recorded proof modules to import. They remain named in the unchanged
proof and the theorem docstring, not additional statement prerequisites.

Edge cases checked: zero modules and zero morphisms are included; the kernel and
cokernel clauses recover direct sums with zero as expected. The empty scheme and
zero ring sheaf are included. For a unit a the quotient tower is zero and only the
zero module is complete, so all four closure clauses remain valid. For a=0 the
regularity condition forces R to be zero; it does not incorrectly admit nonzero R.
Torsion in M and N is permitted: regularity is only on R. The extension is not
required to split. The statement does not imply that an arbitrary submodule of a
complete module is complete.

Sources: read the local Bhatt--Scholze PDF, printed p.23, Lemma 3.4.14 and its
amplitude proof. Its quotient-completion interpretation is Lemma 3.4.12, as in the
accepted split. No statement correction or STATEMENT-DISPUTED issue was found.

Searches for reuse (msearch.py, group NZ, this item):

- leanfinder: "Derived complete modules over a sheaf of rings for powers of a regular
  principal parameter are closed under kernels cokernels images and extensions".
  Eight hits: IsAdicComplete, IsPrecomplete, AdicCompletion, localCohomology and
  solid condensed modules. Classical completion or unrelated predicates; no match.
- loogle: `"Complete", "kernel"`. One hit:
  `CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels`;
  idempotent completeness, not derived-adic completeness.
- grep: `derived.?complete|complete.*kernel|kernel.*complete` in CategoryTheory.
  Four hits, all from that same idempotent-completeness result; no match.
- leansearch: "Derived complete sheaves of modules are closed under kernels cokernels
  images and extensions". Eight hits: module/sheaf limit and Abelian instances and
  Grothendieck-Abelian sheaves; no completeness-closure statement.
- rg of project Sheaf and WeilConjectures for principal-completion, derived-complete,
  quotient-tower, completion-unit and complete-kernel/cokernel names found the
  existing principal quotient completion model and its quotient towers, reused here.
  Constant-coefficient/integral-lisse results are specializations and do not state
  this arbitrary-ring-sheaf result. Grep of WeilConjectures for this node ID found
  no existing declaration. Mathlib AdicCompletion and upstream Complete modules
  provide classical completion or constant-ring derived completeness, not this
  ring-sheaf heart closure.

Validation: all compiler probes used module mode and scompile.py only. Explicit
universe arguments on `Model` and `IsCompleteModule` resolve otherwise ambiguous
localization universes without identifying site universes. No max-heartbeat or
wall-time limit was raised. The final delivered file is compiled separately.

## Second reading by NZ

A second pass by the same worker compared the current node, all clause binders,
the existing model's universal property and coordinates, and the module. The
maintainer supplies the independent review specified by this dispatch; this
paragraph does not claim that a second worker read the delivery. This pass found
no added ring hypothesis, no change from ambient kernels/cokernels/images to an
abstract equivalent heart, and no arbitrary lift replacing the canonical unit.
The only implementation correction was making universe parameters explicit;
mathematical objects and hypotheses were unchanged. All the source's closure
clauses are present. The helper definition is exactly the completeness predicate
introduced in this node, not a second tensor, tower or completion construction.
