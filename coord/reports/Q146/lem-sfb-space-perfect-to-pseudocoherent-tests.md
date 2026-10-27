## Worker report

Item: lem-sfb-space-perfect-to-pseudocoherent-tests. The module
`Sheaf.AlgebraicGeometry.SpacePerfectToPseudoCoherentTests` states
`AlgebraicGeometry.AlgebraicSpace.isPseudoCoherent_tensor_sections_of_perfect_tests`,
with `sorry` as its entire proof. It introduces no definitions or auxiliary theorems.
Source read directly: `literature/stacks-project/spaces-perfect.tex`,
`lemma-perfect-enough`, Tag 0CWH, statement and full proof. The unchanged node agrees
with that source. The theorem docstring gives all seven recorded proof steps,
including the cone boundary degree, tensor bound, adjacent vanishing groups, and
all-m ring pseudo-coherence criterion.

Clause-by-clause correspondence:

- Universes and schemes: explicit `universe u w`, `{S : Scheme.{u}}`, and
  `[HasDerivedCategory.{w} X.SmallModules]`. The small affine etale model has objects,
  morphisms, rings and modules in u; localization morphisms have the independent
  universe w. The canonical A-valued section functor fixes the standard localization
  of `ModuleCat.{u} A`. No extra mathematical existence or finiteness assumption is added.
- A commutative ring: `(A : Type u) [CommRing A]`, allowing the zero ring.
- X over Spec A: `(Y : Over S) (e : Y.left ≅ Spec (.of A))`,
  `(X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)`. This is the existing API's
  presentation of the actual structure map to Spec A. It allows an arbitrary ambient
  scheme S, and in particular S = Spec A with Y the identity object. It adds no
  representability condition on X or f: only the specified affine target is represented.
- Quasi-compact X: `(hqc : CompactSpace (Point X.obj.obj))`, exactly finite-subcover
  compactness of the already defined algebraic-space point topology.
- Quasi-separated X: `(hqs : X.IsAbsolutelyQuasiSeparated)`, the existing affine-test
  formulation of quasi-compactness of the absolute diagonal, not a relative-diagonal
  substitute depending on S. Its source is Stacks Tag 0AHR.
- K in D_QCoh(O_X): `(K : X.DerivedModules) (hK : X.derivedQCohProperty K)`.
  This is the full ambient derived category with its quasi-coherent-cohomology
  predicate, not the derived category of the abelian category QCoh.
- Cohomology of K zero for i > some integer b:
  `hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero
  ((DerivedCategory.homologyFunctor X.SmallModules i).obj K)`.
  This imposes no lower bound and no finite-generation condition on K.
- Perfect tests: `hTests` quantifies over every `P : X.DerivedModules` satisfying
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
  X.smallStructureSheaf P`. This is the recorded local bounded finite-free-retract
  representation, with bounds and ranks allowed to vary over the cover.
- Derived tensor P tensor K: `X.derivedDualityModel.closed.tensor.obj (P, K)`.
  This is the existing K-flat-normalized tensor of the small ringed model; it is
  not an arbitrary bifunctor supplied as a hypothesis.
- RΓ(X,-) in D(A): `(affineDerivedSections A Y e X f).obj ...`, the canonical
  K-injective right derived functor of Hom(O_X,-) with the A-action induced by f.
  Abelian-group-valued H0 hypercohomology alone would not express this node's D(A).
- The perfect-test hypothesis asserts `DerivedCategory.IsPseudoCoherent` of these
  A-valued derived sections, exactly the bounded-above finite-free A-complex predicate.
- Conclusion: `∀ E : X.DerivedModules, X.IsPseudoCoherent E →` the same ring
  pseudo-coherence predicate for `(affineDerivedSections ...).obj
  (X.derivedDualityModel.closed.tensor.obj (E, K))`. There is no added global upper
  bound or separate quasi-coherence assumption on E; the existing etale-local
  pseudo-coherence predicate is used unchanged.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; these are publicly available through the imported dependencies.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its `EtaleSite`, `structureSheaf`, and `Modules` define the original small etale
  ringed topos, transported by the recorded small-model equivalence.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is precisely `SheafOfModules`, used by `SmallModules`; no second category is defined.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, using Mathlib's
  `SheafOfModules.IsQuasicoherent`. The same predicate appears after transport in
  `derivedQCohProperty`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`. Its full definition
  was read; it is H0 of the K-injective right derived Hom(O,-) functor. The statement
  requires the full A-valued RΓ, so it uses the already landed scalar counterpart below.
- `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`:
  `SheafOfModules.IsPerfectOnRingedSiteOfUniverses` and its
  `IsLocallyStrictPerfectComplexOfUniverses` implement the recorded local perfectness.
- `WeilConjectures.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`, with its finite-free bounded-above representative.
- Newly cited existing node `def-sfb-space-derived-module-calculus`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`:
  `DerivedModules`, `derivedQCohProperty`, `derivedDualityModel` in namespace
  `AlgebraicGeometry.AlgebraicSpace`.
- Newly cited existing node `def-sfb-space-pseudocoherent-complex`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`:
  `AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent`.
- Newly cited existing node `def-sfb-space-absolute-quasi-separated`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- Newly cited existing node `def-sfb-space-affine-global-sections`, module
  `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`:
  `AlgebraicGeometry.AlgebraicSpace.affineDerivedSections`, using the actual
  `affineGlobalScalar` and `affineScalarSections` constructions.

All four additional statement dependencies are already recorded, landed definition nodes;
no new node or dependency replacement is needed. The only item changes are `lean` and
these additions to `stmt_deps`. The statement, proof, and proof dependencies stay unchanged.
All recorded proof-dependency modules, including Mathlib matches for affine qcqs,
long exact sequences and standard truncation, are imported without `public`. The three
proof dependencies with no declaration yet are not imported:
`lem-sfb-space-qcqs-permanence`,
`lem-sfb-space-affine-chart-uniform-qcoh-vanishing`, and
`lem-sfb-space-product-preserving-derived-functor-upper-bound`.
They remain named in the proof docstring for stage 3.

Edge cases checked against the definitions and source:

- Empty X: the point topology is compact, the diagonal condition holds, and all
  section tests are zero; no Nonempty binder excludes it.
- Zero coefficient ring: permitted; the affine base and hence X are empty, covered above.
- Zero K, zero P or zero E, and rank-zero local free modules are permitted; their
  corresponding tensor test is zero and hence pseudo-coherent.
- K can be unbounded below and need not itself be pseudo-coherent. E may only have
  local upper bounds; no global boundedness is silently imposed on the conclusion.
- The upper bound is strict `b < i`, with b any integer, including negative values.
  In the proof the cone vanishes already at a, not just above a; this is the reason
  for using the surjection at a and both adjacent cone groups.
- X need not be a scheme, separated, Noetherian, proper, or of finite presentation.
  S need not be quasi-separated; hqs uses absolute quasi-separatedness.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder` query: "On a quasi compact quasi separated algebraic
  space bounded above quasi coherent complex perfect tensor derived global section
  tests imply pseudo coherent tensor tests". Result: 8 ordinary scheme qcqs and
  affine-transition-limit facts, no matching statement.
- `msearch.py ... loogle '"PseudoCoherent"'`: OK, 0 hits.
- `msearch.py ... grep 'perfect.*approximat|approximat.*perfect|[Pp]seudo[Cc]oherent'`:
  OK, 0 Mathlib hits.
- `msearch.py ... leansearch` query: "A bounded above quasi coherent complex on a
  qcqs algebraic space with pseudo coherent perfect tensor global sections has pseudo
  coherent pseudo coherent tensor global sections". Result: 8 ordinary sheaf
  quasi-coherence constructors and presentation facts; no matching statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for perfect tests, pseudo-coherence,
  approximation and the item ID: no duplicate theorem. The scheme-specific
  `isPseudoCoherent_of_perfect_tensor_tests` is a different detection theorem with
  flat finite-presentation assumptions and conclusion about K, not this theorem.
  Searches found the existing algebraic-space pseudo-coherence, derived module,
  scalar-section and absolute-diagonal interfaces, all reused above.

No statement dispute, source discrepancy, or hollow definition was found.

Validation: scompile.py compiled both the sandbox and library-mode module without
errors or warnings. The final import list is also checked by the delivery dry run.

## Second reading by Q146

No second agent was started, as the dispatcher explicitly forbids it. I reopened
both the node and the completed module for a separate clause-by-clause rereading.
A is the coefficient ring throughout, and f supplies its actual scalar action.
The Y/e presentation identifies only the target with Spec A; it imposes no
representability hypothesis on X. CompactSpace on Point is the finite-open-subcover
condition; the absolute diagonal predicate avoids silently assuming anything about S.
The hK and hbounded binders independently express the two clauses of D^-_QCoh.
hTests ranges over ambient perfect objects, not only globally strict perfect objects.
The conclusion ranges over all locally pseudo-coherent objects and uses exactly
E tensor K in the same tensor and section functors as the hypothesis. The ring
pseudo-coherence predicate is the existing finite-free representative definition.
All variables and universes are explicitly bound and autoImplicit is disabled.
The rereading found no mathematical mismatch and required no statement change.
It did add explicit plain imports for the Mathlib proof matches (affine qcqs,
cohomology exactness and standard truncation), in addition to the recorded
project proof modules. Every theorem proof remains just `sorry`.
