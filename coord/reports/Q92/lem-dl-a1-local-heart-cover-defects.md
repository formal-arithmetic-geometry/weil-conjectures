## Worker report

The module `Sheaf.Paper.DlLocalHeartCoverDefects` states
`WeilConjectures.dlLocalHeartCoverDefects`, with `sorry` as its only proof.
Its conclusion is `Nonempty (DlLocalHeartCoverDefects D c T)`. The structure is
an assertion package belonging to this theorem, not another local-heart category.
Its fields supply the abelian structures and all the stated evaluation and cover
properties on the existing category. There are no new nodes, dependency repairs,
statement corrections, new axioms, or disputed statements.

Sources read: the assigned node, including all eight proof steps; Bhatt--Scholze
Proposition 6.8.14 and Remark 6.8.15, PDF printed pages 61--62; Stacks Tag 04TQ,
`sites.tex`, `lemma-glue-maps`; and the current blueprint
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-exact/p-dl-a1-exact.proof.md`,
Steps 1 and 5. The local-family universal-property argument is the assigned
node's argument, not a claim that BS literally states this additional lemma.

Hypotheses and clauses, matched individually:

- The fixed finite-field datum is `D : FiniteFieldDatum.{u}`. The prime, its
  distinction from the characteristic, and the algebraic closure of Q_l are
  `c : D.CoefficientDatum`, with the existing instances on `c.l` and `c.Qbar`.
- A scheme over k0 is `T : Over (Spec (.of D.k₀))`; local finite type is precisely
  `[LocallyOfFiniteType T.hom]` on the theorem. No global separatedness or
  quasi-compactness binder is present.
- The objects and compatible arrows are literally
  `DlLocallyConstructibleAdicHeart D c T`, using the dependency's existing
  `DlAdicLocalData.value`, completed restriction isomorphisms and cocycle, and
  `dlAdicLocalCompatible`. No category or restriction functor is redefined.
- The separated finite-type opens are `DlAdicFiniteOpen D T`. Its defining
  conjunction is local finite type, quasi-compactness and separatedness of
  `U.val.ι ≫ T.hom`, exactly the required structure map to k0.
- The component category is literally `sfCommonStageHeart c.l U.val.toScheme c.Qbar`.
  Its property is the intersection of the two isomorphism-closed common-stage
  standard classes at zero. Each class is represented at a finite coefficient
  stage by an integral localized standard class. This definition is independent
  of choosing k rather than k0 as the geometric base; the node explicitly
  specifies its bounded-standard-heart meaning over k0. The component abelian
  structure is supplied as the `componentAbelian U` field, not assumed.
- The local category is abelian: `localAbelian`. Both it and `componentAbelian`
  are instance fields of the conclusion package, so all subsequent kernels and
  cokernels exist as local or component heart objects.
- Evaluation is the recorded `dlAdicLocalEvaluation D c T U`, with its literal
  componentwise object and arrow formulas. `evaluationAdditive`,
  `evaluationLimits` and `evaluationColimits` state that it is exact in the
  abelian-category sense. `evaluationExact` explicitly carries a short complex's
  `ShortComplex.Exact` to the evaluated complex's `Exact`.
- Kernels and cokernels are computed componentwise:
  `kernelComponents` and `cokernelComponents` assert invertibility of Mathlib's
  `kernelComparison` and `cokernelComparison`, for every arrow and basis open.
  These are the canonical comparisons: their defining equations commute with
  the kernel inclusion and cokernel projection. Since the source category is
  the cartesian-family category, its kernels/cokernels are themselves cartesian
  families, and the component universal properties force the induced restriction
  identifications. This states componentwise computation up to the canonical
  isomorphism, without equating unrelated chosen limit objects.
- A short complex `A → B → C` with zero composite is
  `S : ShortComplex (DlLocallyConstructibleAdicHeart D c T)`; its maps are `S.f`
  and `S.g`, and the equation is the existing `S.zero`.
- The left defect is `kernel S.f`; the right defect is `cokernel S.g`.
  The middle defect is `cokernel (kernel.lift S.g S.f S.zero)`: the factorization
  of f into ker(g), quotiented by its image, is exactly ker(g)/im(f).
  `homologyComponents` gives its evaluated/component isomorphism.
  `evaluationHomology` also states the existing Mathlib notion of preservation
  of kernels and cokernels. In particular the comparison is induced by those
  universal properties and their maps, not by an arbitrary comparison morphism.
- Any covering is `(I : Type w) (U : I → DlAdicFiniteOpen D T)` with
  `(⨆ i : I, (U i).val) = ⊤`. The universe w is independent and unrestricted.
- `coverZero` says `IsZero K ↔ ∀ i, IsZero (evaluation.obj K)` for every object K.
- The three conjuncts of `coverDefects` give the three requested iff statements,
  with the corresponding kernel, middle cokernel-of-kernel-lift, and cokernel
  formed after evaluation. These are statements about arbitrary short complexes,
  not just short exact ones.
- There is no global coefficient-field witness, no bound or finiteness assumption
  on I, and no quasi-compactness assumption on T. Coefficient stages remain the
  per-open stages already present in the recorded local category.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`, including their full fields and instances.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, used in
  the recorded basis-open definition.
- `Sheaf.Paper.DlLocallyConstructibleAdicHeart`: `DlAdicFiniteOpen`,
  `dlAdicOpenPull`, `dlAdicOpenPullComp`, `DlAdicLocalData`,
  `dlAdicLocalCompatible`, `DlLocallyConstructibleAdicHeart`,
  `dlLocallyConstructibleAdicHeartZero`, `dlAdicLocalEvaluation`, and
  `dlAdicLocalEvaluationZero`. The entire module was read.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageStandardClass`,
  `sfCommonStageHeartProperty`, `sfCommonStageHeart`, and the signatures and
  docstrings of `sfCommonStageStandardTStructure_existsUnique` and
  `sfCommonStageHeart_properties`.
- `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicPbcQbarCategory`, whose carrier
  is `generalAlgebraicallyClosedConstructibleCategory`, the literal ambient
  carrier in the existing component-heart definition.
- `Sheaf.Paper.AdicHeartIntrinsicFibres`: `sfAdicHeartPullbackFibres`, its
  full signature, docstring and intrinsic-fibre normalization interfaces; publicly
  imported as a statement dependency and used in the supplied proof plan. Its common-standard and fibre clauses are over
  an arbitrary field, as required by the node's explicit k0 convention.
- `Mathlib.Algebra.Homology.ExactSequence`: `ComposableArrows.Exact`;
  the used short-complex special case is `ShortComplex.Exact`, with
  `ShortComplex` retaining the zero-composite equation.
- `Mathlib.CategoryTheory.Abelian.Basic`: `Abelian` with its full defining
  fields, not a replacement predicate.
- Proof imports: `Sheaf.Paper.AdicStratifiedPullbackInterface`,
  `AlgebraicGeometry.Scheme.AdicFibreComparison.pullbackAssertions`;
  `Sheaf.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting`,
  `CategoryTheory.Triangulated.TStructure.heart_abelian_and_idempotent_kernel_decomposition`;
  `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`,
  `CategoryTheory.Functor.preservesHomologyOfExact`. Their recorded
  signatures and proof/source docstrings were read. The last module is public
  because the assertion package also uses its `Functor.PreservesHomology` class.

Edge cases checked before writing: the empty scheme admits an empty cover
(`I = Empty`); its top and bottom opens agree and all component defects are zero.
Empty basis opens are included by the existing basis definition. Zero objects,
zero arrows and the all-zero short complex satisfy the asserted comparisons and
iff statements. Infinite covers of a non-quasi-compact locally finite-type scheme
remain allowed. T need not be separated, so intersections are handled by smaller
basis opens as in proof Step 8, never by assuming the intersection is itself
separated finite type. Repeated basis opens retain the dependency's identity
normalization. No coefficient-field uniformity is introduced by the package.

Searches actually run through `msearch.py Q92 lem-dl-a1-local-heart-cover-defects`:

1. leanfinder: `Cartesian local constructible adic heart evaluation exact kernels cokernels homology zero detected by open cover`.
   Eight hits: Profinite Nobeling exactness, local cohomology, completion
   exactness, condensed AB5, and scheme section-continuity results. None states
   this local cartesian adic heart assertion.
2. loogle: `CategoryTheory.Functor.PreservesHomology, CategoryTheory.Limits.PreservesFiniteLimits, CategoryTheory.ShortComplex.mapHomologyIso`.
   Zero hits for the combined query.
3. grep: `dlAdicLocal|DlLocallyConstructible|mapHomologyIso`.
   Eight hits for generic `ShortComplex.mapHomologyIso`, including its
   `PreservesHomology.lean` definition and naturality lemmas; no local adic theorem.
4. Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
   `dlAdicLocal|DlLocallyConstructible|local.heart.*cover`, and `grep -rn` for
   the item id in `lean/WeilConjectures`: no existing match. The existing
   `DlConstructibleFibresExact` module states a local short-exactness criterion,
   but does not supply abelianity, componentwise defects, or general-object
   cover-zero detection, so is not an exact match. It is a consumer and is not
   imported, avoiding the downstream proof cycle.
5. Direct `rg` for both new names in Mathlib, `lean/WeilConjectures`,
   `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing declarations.
6. Mathlib source searches located `Abelian`, `Preadditive`,
   `Functor.PreservesHomology`, the two canonical kernel/cokernel comparisons,
   and the homology construction, whose signatures and docstrings were read.

Compiler-interface diagnosis: the named `ShortComplex.homology` initially failed
instance synthesis on the supplied local zero-arrow presentation, even after
importing `ShortComplex.Abelian`. The final statement uses the equivalent explicit
cokernel-of-kernel-lift construction on those prescribed zero arrows. It adds no
hypothesis or replacement zero structure. All compilation uses `scompile.py`.

## Second reading by Q92

This is the worker's clause-by-clause rereading; the independent reading belongs
to the maintainer, as specified in this dispatch. No second agent was started.
The assigned statement and final module were reread together: all geometric and
coefficient hypotheses are the original ones, every basis open uses the literal
recorded common-stage heart, and every comparison and cover clause above has a
field in the assertion package. The left defect uses f and the right defect g;
the middle defect uses the factorization of f into ker(g). The cover equality
is a supremum of opens equal to top, with arbitrary universe and no finite or
nonempty index restriction. All abelian structures are outputs, not new
hypotheses. The earlier named-homology elaboration issue was repaired by the
explicit standard quotient formula. No mathematical mismatch or statement
correction was found.

Validation before delivery: `scompile.py` passed sandbox and library-mode compilation
without errors or warnings (18.4 s and 9.8 s). The final public visibility of the
adic-heart statement dependency is also checked in the delivery dry run.
