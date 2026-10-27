## Worker report

The module `Sheaf.AlgebraicGeometry.SpacePerfectTestRelativePerfection` states
`AlgebraicGeometry.AlgebraicSpace.isPerfectRelativeToScheme_of_perfect_tensor_tests`.
Its sole theorem has proof `sorry`; no new definition, axiom, or theorem proof is supplied.
The source was read in `literature/stacks-project/spaces-more-morphisms.tex`,
lemma-characterize-relatively-perfect (0GFL) and lemma-bounded-on-fibres (0GFK).
The six-step natural-language proof from the node is included in the declaration docstring.
The source's printed D-minus in the proof is the already documented D-plus typo;
the stated conclusion and the node's corrected proof are preserved.

Clause correspondence:

- The size convention is explicit `universe u w`; schemes, rings and module sections
  have universe u and the source derived category has independent localization size w.
  `HasDerivedCategory.{w} X.SmallModules` is the localization choice, not an extra
  geometric hypothesis. The scalar derived category uses its canonical standard localization.
- `S : Scheme.{u}` is the auxiliary base used by the recorded algebraic-space category.
  `A : Type u` with `[CommRing A]` is an arbitrary commutative ring. `Y : Over S`
  and `e : Y.left ≅ Spec (.of A)` present exactly the affine target Spec A. This does
  not restrict the theorem: any space over A is included by taking S=Spec A and Y=id.
- `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace Y` are the algebraic space and
  its morphism to the affine target; schemeSpace uses the existing represented sheaf.
- `hsep : MapIsSeparated f` says the diagonal is representable by closed immersions.
- `hflat : MapIsFlat f` is flatness on every compatible pair of etale scheme charts.
- `hfp : MapIsLocallyOfFinitePresentation f` is local finite presentation on those
  charts; `hqc : MapIsQuasiCompact f.hom.hom` supplies quasi-compactness. Together
  with separatedness, which implies quasi-separatedness, these are precisely finite
  presentation. No unnecessary properness, Noetherianity or smoothness is imposed.
- `K : X.DerivedQCoh` is the full subcategory of D(O_X) with quasi-coherent
  cohomology, using the recorded equivalent small affine etale ringed model.
  It is not the derived category of the quasi-coherent abelian subcategory.
- `htest` quantifies over EVERY `E : X.DerivedModules`; the antecedent
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u,u,u,w}
  X.smallStructureSheaf E` means etale-local bounded models of finite-free retracts.
  E is not required to be globally strictly perfect or separately assumed quasi-coherent.
- `X.derivedDualityModel.closed.tensor.obj (E,K.obj)` is the existing normalized
  K-flat derived tensor. `affineDerivedSections A Y e X f` is the actual A-valued
  Hom(O_X,-) right derived by K-injectives, with A-action pulled back through f.
  Thus the tested object is exactly RΓ(X,E tensor^L K), not just H^0 or its
  underlying abelian group. `DerivedCategory.IsPerfectRingComplex` means an
  isomorphic bounded complex of finitely generated projective A-modules.
- `IsPerfectRelativeToScheme Y f K.obj` gives quasi-coherent cohomology and, on
  every affine etale chart, scheme pseudo-coherence and finite Tor dimension over
  the inverse-image base structure sheaf. The recorded definition is explicitly
  equivalent to the node's pseudo-coherence and locally finite relative Tor
  amplitude under flat local finite presentation. The Tor test uses ALL module
  sheaves over that inverse-image ring, not only modules pulled back from A.
- The final conjunct uses a covering sieve T on every object V of the small etale
  model. For each arrow g in T, there is an integer c such that for ALL n<c the
  restriction by `SheafOfModules.overFunctor` of H^n(K) is zero. Exact slice
  restriction makes this precisely local cohomological lower boundedness. The
  bound can vary on every cover member; no global uniform lower bound is added.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: Scheme and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: AlgebraicSpace, EtaleSite,
  structureSheaf and Modules; no competing presentation is introduced.
- `Sheaf.CategoryTheory.RingedSiteModules`: ringedSiteModules, the transparent
  abbreviation for the original SheafOfModules category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: HasDerivedCategory,
  DerivedCategory and the localization Q; homology is the descended homology functor.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: QCoh uses exactly
  Mathlib SheafOfModules.IsQuasicoherent and the supplied slice instances.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  IsPerfectOnRingedSiteOfUniverses uses locally bounded finite-free retracts.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  DerivedCategory.IsPerfectRingComplex uses bounded finite projective models.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  ringedSiteZerothHypercohomologyOfUniverses records H^0 of the same unbounded
  K-injective derived global sections; it remains publicly imported as an original
  statement dependency. The A-valued derived functor needed here is the already
  landed affineDerivedSections, not a private copy of hypercohomology.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: SmallModules,
  DerivedModules, DerivedQCoh, derivedQCohProperty, and derivedDualityModel.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: affineDerivedSections.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect`:
  IsPerfectRelativeToScheme. Its underlying scheme HasFiniteTorDimensionOver
  declaration was also read, including the all-module inverse-image-ring test.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: MapIsSeparated,
  MapIsFlat, MapIsLocallyOfFinitePresentation; MapIsQuasiCompact is the recorded
  affine scheme-test predicate from ProperCurveModuli, publicly available here.

The last four landed nodes were added to stmt_deps so the selected existing
interfaces are explicitly named. No existing dependency record needed repair.
The source category, modules, and perfectness modules are publicly reachable from
these imports. Every stated proof dependency is imported without public visibility.
The four proof-only nodes without Lean records at this reading were
lem-sfb-space-perfect-tests-pseudocoherence,
lem-sfb-space-generator-detects-lower-bound,
lem-sfb-space-affine-derived-pushforward-conservative, and
lem-sfb-space-relative-perfect-fibre-criterion. Their future imports belong to the
maintainer's normal proof-dependency import update; none is required to TYPE this
statement. All remain cited in the proof docstring and unchanged proof_deps.

Edge cases checked before writing: the zero ring (empty Spec), empty X, zero K,
zero E, all integer degrees including negative degrees, non-Noetherian A, and
varying local Tor/lower bounds. There is no nonempty-space, nonzero-ring,
characteristic or boundedness assumption. Empty covers on the empty site behave
vacuously as required. Perfect tests have no common bound imposed on them.
The definition of relative perfection supplies local bounds on affine charts;
quasi-compactness allows finite refinements without imposing a global Tor bound
in the statement. The explicit last clause keeps local lower boundedness local.

Searches for an existing statement:

- msearch.py leanfinder: "A quasi coherent complex on a separated flat finitely
  presented algebraic space over A is relatively perfect if all perfect tensor
  tests have perfect derived global sections". Eight hits: ordinary flat scheme
  morphisms and finite-presentation quasi-coherent module data; no matching theorem.
- msearch.py loogle: "DerivedCategory.IsPerfect, AlgebraicGeometry.AlgebraicSpace".
  Zero hits, unknown identifier DerivedCategory.IsPerfect.
- msearch.py grep: "IsPerfectRelativeTo|perfect.*test|characterize.*perfect" in
  Mathlib/AlgebraicGeometry. Zero hits.
- rg in lean/WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry
  for the same expressions found the existing scheme pseudo-coherence criterion,
  the exact relative-perfect definition, base-change lemmas and references in the
  adjoint-unit proof, but no algebraic-space perfect-test relative criterion.
- rg for the exact node id in lean/WeilConjectures returned no matches.
- Concept searches of the Sheaf tree found the existing scalar global-sections
  construction and the inline local-lower-bound form in
  AlgebraicSpacePseudoCoherentRHomQuasiCoherent, which are reused here.

Validation: the prescribed scompile.py compiled both the sandbox file and the
library module successfully (3.7 and 3.8 seconds). No error or unexpected warning.
No statement correction, STATEMENT-DISPUTED flag, or new definition node.

## Second reading by Q11

A separate second pass by this dispatched worker compared the full node and file:
A is arbitrary; X is an actual algebraic space; separated, flat, and finitely
presented are all present; K has quasi-coherent cohomology; tests range over all
perfect ambient derived objects; their A-valued derived sections are perfect;
the conclusion uses the recorded all-module relative Tor predicate, and the
explicit lower-bound clause permits a different bound on each covering member.
No mismatch was found and no statement change was made. This is a self-check,
not an independent-agent review: the dispatcher forbids spawning another agent;
the maintainer performs the independent delivery review specified in the brief.
