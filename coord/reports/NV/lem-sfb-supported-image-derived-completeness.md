## Worker report

The module `Sheaf.Paper.SupportedImageDerivedCompleteness` states
`AlgebraicGeometry.ProEtale.supported_kernel_image_derived_complete` with its
whole proof postponed by `sorry`. There are no new definitions or other
postponed declarations. The natural-language statement and accepted stage-1
split are preserved. The earlier unchanged-item rejection concerned the
stage-1 handoff; this delivery adds the previously missing stage-2 Lean record.
There is no released repair note for this item.

Hypotheses and clauses, in order:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. A finite extension of Q_l is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The recorded continuous integral ring
  `DerivedNakayama.integerRing l E` is C(-,O_E) with the spectral norm topology,
  and `AdicCompletion.Modules l E T` is the internal module category over its
  pulled-back ring on T. Its positive-level quotients and chosen uniformizer
  are those of the recorded completion dependency. E = Q_l is included.
- The base is `(X : Scheme.{u}) [IsAffine X]`. The small pro-etale site and its
  actual affine object are `(U : X.ProEt) [IsAffine U.left]`; its arrow is
  `U.hom`. The site has object universe u+1 and morphism universe u; abelian
  coefficient sheaves have values in `Ab.{u+1}`. No extra equality of these
  universe levels is imposed. The etale site is a contextual convention,
  with no etale cohomological-dimension assertion in this node.
- The support chain is `{S : Scheme.{u}} (tree : QcqsOpenClosedTree X)
  (p : tree.Path S)`. Its module operation J_R is precisely the existing
  `p.extension R`: a root path is the identity, an open edge appends
  `CondensedRing.openImmersionLowerShriek R j`, and a closed edge appends
  `CondensedRing.lowerStar R i`. The construction retains the actual maps.
  This reuses `def-sfb-qcqs-open-closed-tree`, added to stmt_deps as an already
  landed definition, rather than introducing another chain definition.
- This encoding includes EVERY support chain in the statement. Starting from
  the affine root, each vertex of such a chain is qcqs: a quasi-compact open
  subscheme of a qcqs scheme is qcqs, and a closed subscheme of a qcqs scheme
  is qcqs (closed immersions are affine). At an open step, take the reduced
  closed complement as the unused sibling. At a closed step, take its given
  quasi-compact open complement as the unused sibling. These siblings are
  qcqs and may be single-vertex trees. Iterating produces a finite tree and
  a path with exactly the specified edges and exactly J_R. Conversely every
  tree path has only the allowed edges and quasi-compact open complements.
  Nothing requires p to end at a leaf; paths ending at internal vertices are
  allowed. Thus the additional tree data restricts none of the allowed chains.
- The finite scalar local models are `(L M : AdicCompletion.Modules l E S)`
  and the separate assumptions `hL` and `hM` of
  `HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) S`. That
  recorded predicate chooses a pro-etale cover and finite scalar presentation
  separately for each module, so neither common cover nor common presentation
  nor torsion-freeness is added. Its scalar presentation is chosen on the
  condensed point before pullback, as required by the node.
- The map `(f : L ⟶ M)` is unrestricted. `kernel f` and `image f` are the
  actual categorical kernel and image in this abelian category; there is no
  closure of an image, constant-matrix hypothesis, or reduction of f.
- The first and second conjuncts are respectively
  `IsDerivedComplete l E S ((DerivedCategory.singleFunctor _ 0).obj (kernel f))`
  and the same expression with `image f`. The third and fourth conjuncts
  apply `p.extension` and then `CondensedRing.upperStar ... U.hom` to the
  same actual kernel and image, put the resulting module in degree zero,
  and assert `IsDerivedComplete l E U.left`.
- All four predicates use exactly the recorded normalized quotient-tower
  completion augmentation of `sk-def-pe-derived-completion`, in the ordinary
  uncompleted derived category of internal modules. Its definition asks that
  the specified augmented Roos map on a K-flat representative become an
  isomorphism, and its `roos_isDerivedLimit`/`completionMap` interface identifies
  this with the stated inverse limit of derived finite reductions with scalar
  restriction. No arbitrary completion map is substituted. No RΓ, vanishing,
  cohomological-dimension, or completion assumption is added to the hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `def-weil-size-convention`: the convention record has no declaration;
  explicit u, u+1 and the existing derived-category instances implement it.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek`;
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar` and `CondensedRing.upperStar`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and
  `CondensedRing.moduleObjectDerivedPullback` preserve the ordinary derived
  pushpull convention; these functors do not replace the actual module operations.
- `Sheaf.Paper.CondensedConstantConstructibility`: `HasFiniteConstantLocalModel`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  extension module: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`,
  `Padic.coefficientExtensionRing`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `IsLocalizingAdmissibleCoefficient` provides the contextual coefficient family;
  no localizing-closure or admissibility hypothesis is needed by this integral node.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `IsDerivedComplete`,
  `AdicCompletion.Modules`, `AdicCompletion.ring`, and its specified quotient tower.
- `Sheaf.Paper.QcqsOpenClosedTree`: `QcqsOpenClosedTree`,
  `QcqsOpenClosedTree.Path` and `QcqsOpenClosedTree.Path.extension`.

The five stated proof dependencies are imported privately, including the
coefficient resolution, finite-model completeness, strict completion/restriction,
derived support localization, and open/closed recollement modules. The proof
node `lem-sfb-principal-complete-heart-kernels` has no Lean declaration at the
base, so there is no module for it to import. It is not a statement dependency;
its existing DAG obligation and the five-step docstring are retained.

Sources checked: the latest blueprint constructibility and derived-completion
section files and the ancestor refinement proof; Bhatt--Scholze Lemma 3.4.14
in the local PDF. The lemma explicitly treats ordinary kernels, cokernels and
images; support preservation follows the node's separate open/closed unit
comparison argument. The exact support-preservation reference remains WANTED,
as the unchanged node states. No counterexample or statement fault was found.

Edge cases checked before writing: f = 0, f = identity, zero modules, modules
with uniformizer torsion, different scalar covers/presentations, empty source,
empty affine base, root/empty chain, paths ending at internal vertices, repeated
identity support arrows, and U = X with the identity pro-etale arrow. The four
completeness clauses make sense in every case and impose no dimension bound.
An identity closed arrow has empty open complement, which the tree allows.

Searches for existing statements (all through the prescribed msearch wrapper):

- leanfinder: "Kernels and images of finite scalar locally constant integral pro
  etale modules are derived complete after supported open or closed extension".
  Eight hits, including condensed solid-module and BDeRham declarations; none
  states this completeness theorem.
- loogle: "IsDerivedComplete, kernel, image". Zero hits; the search service does
  not know the project-specific `IsDerivedComplete` identifier.
- leansearch: "Kernels and images of morphisms between derived adically complete
  sheaves of modules are derived complete". Eight hits: ordinary AdicCompletion
  statements and generic `CategoryTheory.Abelian.image`, none this theorem.
- grep: "IsDerivedComplete|supported.*complete|SupportChain". Zero Mathlib hits.
- Direct rg of `lean/WeilConjectures` for the item id found no declaration.
  Concept searches of `lean/Sheaf/Paper` and `lean/WeilConjectures/SixFunctors`
  located `FiniteScalarLocalModelComplete`, the downstream
  `SupportedThreeTermScalarCd` docstring, and `QcqsOpenClosedTree`; they supply
  inputs, a consumer, and the existing chain encoding, respectively, not this
  four-clause statement. The tree's owning DAG node was read in full.

Validation: scompile.py compiled the file both in sandbox and library module
mode without errors or warnings (2.9 s and 2.5 s respectively). The delivered
statement has explicit variables and universe, and the only proof is `sorry`.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
