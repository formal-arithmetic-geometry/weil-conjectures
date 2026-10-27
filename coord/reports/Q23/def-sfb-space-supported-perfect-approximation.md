## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation` defines
`AlgebraicGeometry.AlgebraicSpace.HasSupportedPerfectApproximation`, the property
A(X) of Stacks spaces-perfect.tex, Tags 08HI and 08HJ. Its two helper predicates,
`IsMPseudoCoherent` and `ModuleSupportedOn`, expand the fixed-degree
pseudo-coherence and support notions explicitly introduced in this same node.
All three declarations have real definition bodies. There are no theorems,
axioms, postponed proofs, new nodes, dependency repairs, or statement corrections.

The previous ending concerned a stage-1 unchanged-node refusal. The live item is
stage-1 split and reviewed, has no `lean` record, and is in the stage-2 queue.
This delivery adds its first Lean record and module while preserving the
accepted natural-language statement and split. No repair note exists for it.

Clause-by-clause correspondence:

- The base scheme S and algebraic space Y are `{S : Scheme.{u}}` and
  `(X : AlgebraicSpace S)`. There is no finite-type, separation, Noetherian,
  quasi-compactness, or nonemptiness hypothesis on either object.
- The size convention is explicit `universe u w`. The existing `SmallEtaleModel`
  is a small affine etale basis, with structure ring sections in universe u.
  `[HasDerivedCategory.{w} X.SmallModules]` retains an arbitrary localization
  morphism universe. It selects an available derived localization rather than
  imposing any additional geometric hypothesis or equality of universes.
- D(O_Y) is the recorded `X.DerivedModules`. The actual restriction equivalence
  `X.smallModuleEquivalence` identifies this with the original module topos.
  `X.derivedQCohProperty F` requires that every cohomology sheaf transported
  through its inverse satisfies Mathlib `SheafOfModules.IsQuasicoherent`.
- The local notion of b-pseudo-coherence is `X.IsMPseudoCoherent b K`.
  `E : CochainComplex X.SmallModules ℤ` and
  `Nonempty (K ≅ DerivedCategory.Q.obj E)` mean that E represents K.
  `∀ V, ∃ R : Sieve V, R ∈ X.smallEtaleModelTopology V ∧ ...` is locality
  on every object, with all arrows of the covering sieve allowed.
  On each member U, `F : CochainComplex (SheafOfModules (X.smallStructureRings.over U)) ℤ`
  is a complex on the slice site. Its bounds are
  `∃ a c : ℤ, ∀ n, n < a ∨ c < n → IsZero (F.X n)`.
  `StrictPerfectCoefficientPackageOnSite ... F` supplies finite-free splittings
  degree by degree. Its maps are not required to be chain maps, as intended.
  The actual complex map α goes into the termwise slice restriction of E;
  `IsIso (HomologicalComplex.homologyMap α i)` for `b < i`, and
  `Epi (HomologicalComplex.homologyMap α b)`, give the two cohomology clauses.
  The chosen representative, local covers, bounds, and ranks are existential
  and may vary as the statement allows. Checking on this affine basis is
  equivalent to checking on every object of the original small etale site:
  cover every etale scheme by affine opens and use the fixed ringed comparison.
  This is the representative formulation of sites-cohomology.tex Tag 08FT;
  Tag 08FU supplies representative independence.
- The closed subset is `T : Set (Point X.obj.obj)` with `IsClosed T`, using
  exactly the existing field-valued point quotient and its final topology.
- The open complement inclusion is quasi-compact precisely when its inverse
  image in every affine scheme is quasi-compact. This is written directly as
  `∀ (U : Over S), IsAffine U.left → ∀ a : yoneda.obj U ⟶ X.obj.obj,
  IsCompact (schemePointMap a ⁻¹' Tᶜ)`.
  It covers all affine scheme maps, including non-etale ones. The inverse
  image is the point set of the pulled-back open subspace; its subspace
  topology is the scheme topology. No choice of atlas or open immersion data
  is imposed. The imported `openSubspace_points_orderIso` identifies this
  complement with the unique open subspace specified by the node.
- Vanishing outside T is `X.ModuleSupportedOn T M`: every object V of the
  original `X.EtaleSite` whose scheme-point image is disjoint from T has
  zero module restriction. Such charts are exactly the objects lying in the
  open complement; their slices have the same restricted structure rings.
  Thus this tests the zero restriction to its entire small etale site,
  rather than sectionwise surjectivity or an unsupported stalk replacement.
  The displayed `Disjoint (Set.range (schemePointMap V.obj.hom)) T` expresses
  image containment in the complement. Transport back to the original site
  is explicitly `X.smallModuleEquivalence.inverse.obj M`; restriction is the
  existing `X.etalePullback V`.
- `∃ r : ℤ` follows T and its two hypotheses and precedes
  `∀ (m : ℤ) (F : X.DerivedModules)`. Hence r depends only on X,T and not m,F;
  it is an arbitrary integer, without a sign constraint.
- The input degree is exactly `(m - r)`, in `X.IsMPseudoCoherent (m - r) F`.
  The input support hypothesis quantifies `∀ i : ℤ, m - r ≤ i → ...` and
  applies `ModuleSupportedOn` to the existing derived cohomology functor.
- The output is `∃ (P : X.DerivedModules) (v : P ⟶ F)`. Perfection is the
  recorded `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}`
  for `X.smallStructureSheaf`; it means local bounded finite-free retract
  representatives, with no added global bounds or extra QCoh hypothesis.
- Output support is required for every integer i, with no lower bound.
  `IsIso ((DerivedCategory.homologyFunctor X.SmallModules i).map v)` for
  `m < i` renders the strict upper-degree inequality. `Epi` of that same
  cohomology map at m renders surjectivity in the category of module sheaves,
  hence local surjectivity, not surjectivity on sections on every chart.

Recorded dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention, implemented by explicit u,w.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its `Hom`; source signatures and docstrings read.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `EtaleSite`, `structureSheaf`, `Modules`,
  and `etalePullback`. The original small site remains in the support helper.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`; cohomology is
  `DerivedCategory.homologyFunctor` from `DerivedCategory.HomologySequence`.
- `def-trf-space-quasi-coherent-module`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`,
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, built from the actual Mathlib
  `SheafOfModules.IsQuasicoherent`, which the derived QCoh predicate uses too.
- `def-weil-pbc-strict-perfect-coefficient-package`:
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its imported
  `StrictPerfectCoefficientPackageOnSite`. The local representation record's
  full signature and the bodies of its perfectness predicates were read.
- `def-a1-space-point-topology`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`,
  `pointTopologicalSpace`; its dependency `Point` and `schemePointMap` were read.
- `def-a1-space-open-subspace`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`, `OpenSubspace`.
- `lem-a1-space-etale-open-image`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`,
  `openSubspace_points_orderIso` identifies the unique complement. Restriction
  and quasi-compactness are expressed on its chart objects, so no arbitrary
  representative for that unique open subspace is chosen.
- Added the already landed `def-sfb-space-derived-module-calculus` to stmt_deps:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`, `DerivedModules`,
  `derivedQCohProperty`, using `SmallModules`, `smallStructureSheaf`, and the
  fixed small-model equivalence from its recorded small-ringed-model dependency.
  This reuses the existing D_QCoh definition rather than making a private copy.

Edge cases checked before writing: T empty requires vanishing on every chart
and therefore zero cohomology in the specified range. T the whole point space
has empty complement with quasi-compact inverse images; support then imposes
no restriction except zero restriction to empty charts, which is automatic.
The empty algebraic space and empty charts are allowed. All integer degrees,
including negative degrees and m=0, are quantified; r need not be nonnegative.
The zero derived object has a zero strictly perfect local model, with rank
zero in every degree. Local bounds and ranks need not be globally uniform.
No coefficient universe is artificially raised to the point-space universe.

Searches made:

- msearch.py leanfinder: "Uniform supported perfect approximation on algebraic
  spaces with an integer loss in pseudo coherence" returned eight ordinary
  scheme-limit/chart hits, none the property being defined.
- msearch.py loogle: `"PseudoCoherent", "PerfectComplex"` returned no hits.
- msearch.py grep: `SupportedPerfect|IsMPseudoCoherent|IsPseudoCoherent`
  returned no Mathlib hits.
- msearch.py leansearch: "Uniform supported perfect approximation on algebraic
  spaces with fixed integer loss in pseudo coherence" returned eight uniform
  topology/analysis hits, none the present property.
- rg over `lean/WeilConjectures` and `lean/Sheaf` by pseudo-coherence,
  supported approximation, proposed declaration names, and the blueprint id:
  the existing ring `DerivedCategory.IsMPseudoCoherent` applies to ordinary
  modules; the scheme pseudo-coherence definitions use the Zariski site;
  `AlgebraicSpace.IsPseudoCoherent` requires all degrees. None defines the
  finite-degree etale-space predicate or the uniform supported property.
- Read DAG nodes `def-sfb-m-pseudo-coherent-complex` and
  `def-sfb-supported-perfect-approximation-property`: both are scheme/Zariski
  notions and have no Lean binding. `lem-sfb-ringed-site-pseudocoherent-top-finite-type`
  likewise only introduces fixed-degree coherence in its own statement and
  has no binding. There is no independent node for the present helper.
- Read `SpacePseudoCoherentPerfectApproximation.lean`: its
  `exists_perfect_approximation` is a theorem for qcqs spaces and fully
  pseudo-coherent objects, not the uniform supported property being defined.
- Searched `dag/lean_names_upstream.json` for the proposed names: no match.

Sources checked locally: spaces-perfect.tex definitions approximation-holds
and approximation, and sites-cohomology.tex definitions pseudo-coherent and
representative independence. The latest blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` is unchanged;
this is a supporting definition, not the unit's own statement.

Validation: scompile.py compiled the module both as a sandbox file and at its
library module name, cleanly without warnings (17.4 s and 6.5 s respectively).
The delivery wrapper repeats per-file compilation and the server preflight.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
