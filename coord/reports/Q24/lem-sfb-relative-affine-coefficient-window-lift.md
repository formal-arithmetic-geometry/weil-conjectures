## Worker report

The module `Sheaf.Algebra.Homology.RelativeAffineCoefficientWindowLift` states
`ModuleCat.relativeAffineCoefficientWindowLift`, with one `sorry` and no new definitions.
It formalizes the unchanged mathematical statement of
`lem-sfb-relative-affine-coefficient-window-lift`. Its statement dependencies are exactly
the five definition nodes on current main. The restriction-square transport is written
inline using the existing derived restriction composition and congruence isomorphisms.
The cancellation theorem remains a proof dependency only, with a plain import.
No dependency node is changed and no new node is needed.

Hypothesis and clause audit:

- Commutative Noetherian B: `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Commutative A and B -> A: `[CommRing A] [Algebra B A]`; its map is `algebraMap B A`.
- Commutative finite-type B-algebra R: `[CommRing R] [Algebra B R]
  [Algebra.FiniteType B R]`. `FiniteType.iff_quotient_mvPolynomial''` is exactly the
  finite-polynomial-quotient description in the node.
- R_A: the actual tensor ring `R ⊗[B] A`, not an arbitrary algebra with the same name.
- The fixed surjection A[t_1,...,t_r] -> R_A: `r : ℕ`, `p : @AlgHom A
  (MvPolynomial (Fin r) A) (R ⊗[B] A) ... TensorProduct.rightAlgebra`, and
  `hp : Function.Surjective p`. Explicit rightAlgebra supplies the canonical A-action
  from the second factor; the ordinary default tensor algebra is over R instead.
  The explicit `@AlgHom.toRingHom` in hK preserves precisely that algebra structure.
- K in D(R_A): `K : DerivedCategory (ModuleCat.{u} (R ⊗[B] A))`.
- Pseudo-coherence after the specified polynomial restriction: hK is exactly
  `DerivedCategory.IsPseudoCoherent ((derivedRestrictScalars p.toRingHom).obj K)`,
  with the implicit rightAlgebra arguments spelled out in the file.
- Every integer a: the theorem has the unrestricted binder `(a : ℤ)`.
- Existence of a commutative finite-type coefficient stage D factoring B -> A:
  existential `D`, `CommRing D`, `Algebra B D`, `Algebra D A`, `IsScalarTower B D A`,
  followed by `Algebra.FiniteType B D`. The tower states equality of the composite
  with the given B -> A, not just existence of unrelated ring maps.
- R_D and L: the actual ring `R ⊗[B] D` and
  `L : DerivedCategory (ModuleCat.{u} (R ⊗[B] D))`.
- Bounded cohomology: `∃ c b : ℤ, ∀ i, i < c ∨ b < i → IsZero (H^i L)`.
  No termwise boundedness or Tor-amplitude hypothesis is substituted.
- Finite cohomology: `∀ i, Module.Finite (R ⊗[B] D) (H^i L)`.
- The prescribed gamma: the target is K restricted through
  `TensorProduct.map (AlgHom.id B R) (IsScalarTower.toAlgHom B D A)`, exactly R_D -> R_A.
- The canonical tensor and action composite: T is an A-derived object, eta is an
  arrow from the D-restriction of L to the D-restriction of T, and
  `IsDerivedBaseChange η` requires the universal property of A tensor_D^L L.
  The theta transpose equation is eta followed by Res(theta) equal to Res(gamma)
  followed by the canonical restriction-square transport. This uniquely specifies
  theta as the extension/action composite mu_K (1 tensor gamma). It is not an
  arbitrary map or an extra assumption on the input. K-flat computation gives this
  same universal tensor, as specified by the dependency's existing API.
- Cone: `Triangle.mk θ ι δ ∈ distTriang _` fixes a distinguished cone of that map.
  The bound is `∀ i : ℤ, a ≤ i → IsZero (H^i C)`, including i=a.
  This is expressed on the A-linear map, exactly as in the landed cancellation
  interface. The stipulated R_D-linear tensor map and this A-linear map have the
  same underlying D-complex: resolve A as a D-module and tensor with the representing
  R_D-complex. Gamma followed by the ordinary A-action gives the same chain-level
  action map in both descriptions. Forgetting the two cones to D is exact and
  faithful and commutes with cohomology, so zero cohomology is equivalent. No
  R_A-module structure on the tensor source is claimed, and there is no erroneous
  restriction functor from R_D-modules to A-modules.
- No flatness assumption, exact descent, lower cone bound, or transition map is added.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (abbreviation for
  `IsNoetherian B B`, the ideal finite-generation condition).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`; its cohomology functor from `DerivedCategory.HomologySequence`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`,
  with a bounded-above finite-free representative and derived isomorphism.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, preservation of quasi-isomorphisms on
  both tensor sides, directly publicly imported.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `.Triangulated`:
  `CategoryTheory.Pretriangulated`, `distTriang`, `Triangle.mk`, and `IsTriangulated`.
- `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`:
  `ModuleCat.derivedRestrictScalars`, `IsDerivedBaseChange` and
  `derivedRestrictScalarsCompIso`, read in full. The first is termwise exact
  restriction localized; the second is bijectivity of the transpose map for every
  target. Thus it fixes tensor and unit up to unique compatible isomorphism.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`:
  `ModuleCat.restrictScalarsCongr`, lifted by `Functor.mapDerivedCategoryNatIso`.
  In the transpose equation, the explicit composite is
  `derivedRestrictScalarsCompIso rfl ≪≫
  Functor.mapDerivedCategoryNatIso (restrictScalarsCongr w) ≪≫
  (derivedRestrictScalarsCompIso rfl).symm`, where the first and last ring maps
  are given explicitly and w is `TensorProduct.map_comp_includeRight` on ring maps.
  This is the exact body of the former helper, without depending on that helper.
- `Sheaf.Algebra.Homology.SingleDegreeCoefficientConeCancellation`:
  `ModuleCat.singleDegreeCoefficientConeCancellation` is used by the proof plan only.
  Its full signature, proof plan and retained-action convention were read. The
  module now has a plain proof import, not a public statement import.

All recorded, stated proof dependencies are imported. Besides cancellation, these
are `Sheaf.RingTheory.PolynomialPresentationPseudoCoherence`,
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion`,
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
`WeilConjectures.RingTheory.PseudoCoherentIffAllM`,
`WeilConjectures.RingTheory.ConePseudoCoherent`,
`WeilConjectures.RingTheory.FiniteHomologyOfMPseudoCoherent`, and
`Mathlib.RingTheory.FiniteType` (directly publicly imported).
The docstring carries all six proof steps with their named dependencies.
A dependency traversal found no path from cancellation back to this item.

Edge cases checked before writing:

- r=0 is allowed by `Fin 0`; no positive rank or nonempty variable set is imposed.
- Zero rings and K=0 are allowed: there is no Nontrivial assumption. The zero model
  with D=B gives the initial stage whenever the requested window is above K.
- Every negative and positive a is admitted. The conclusion includes the boundary
  a, and preserves the weaker below-window freedom allowed by the node.
- Nonflat B -> A and D -> A are allowed; negative Tor is retained by universal
  derived base change rather than ordinary extension.
- L need not have finite Tor dimension; its cohomology alone is bounded and finite.
- All rings/modules are taken in a common arbitrary universe u, as in the cancellation
  interface and the standard module-derived-category instance. Any finite collection
  of rings and a representative fits such a common universe; there is no independent
  smaller test-object universe, omitted smallness case, or extra localization axiom.
- Identity stages and maps are admitted by the algebra-tower binders. There is no
  requirement that gamma, theta or the lower-degree comparison be invertible.

Searches actually run:

- msearch.py leanfinder: "Approximate a relatively pseudo coherent complex over a
  finite type algebra by derived scalar extension from a finite Noetherian coefficient
  algebra in any upper cohomological window". Eight hits, headed by
  `DerivedCategory.exists_iso_Q_obj_of_isGE`, then derived fraction factorization,
  injective single-complex, CM5b and t-structure statements. None is this approximation.
- msearch.py loogle: `ModuleCat.restrictScalars, MvPolynomial`. Zero hits.
- msearch.py grep: `pseudo.?coher|coefficient.?window|[Dd]escente`. Zero Mathlib hits.
- msearch.py leansearch: "finite coefficient algebra approximation of relatively
  pseudo coherent complex with derived scalar action cone vanishing in all degrees
  above a fixed integer". Eight hits on finite presentation coefficients, strict
  cochain bounds, truncation and quasi-coherent presentations; none is this statement.
- rg of lean/WeilConjectures and lean/Sheaf for the node id, finite-window and
  coefficient-window names found no prior theorem. Searches for scalar-action and
  coefficient-cone names found the landed cancellation module. Its theorem is a
  proof dependency; the plain helper's existing composition/congruence body is
  expanded inline rather than citing the theorem as a statement dependency.
- rg of dag/lean_names_upstream.json for the node id and the chosen theorem name found
  no existing declaration. The current name is absent from upstream and Sheaf sources.

Sources read: perfect.tex, the complete Tag 0CSD lemma and immediately following Kiehl
paragraph (lines 7547 onwards); the current blueprint's
sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof.
The source only asserts the general Kiehl finiteness theorem; this affine lemma is
explicitly an agent-formulated prerequisite, as the node already records. No numbered
Stacks theorem is falsely claimed for it. No statement correction or disputed statement.

Validation of the repaired file: scompile.py compiled both the sandbox alias and
final library module cleanly (11.0 s and 3.4 s). The only proof remains the intended
`sorry`. Explicit rightAlgebra arguments are retained. No direct compiler or global
build was used. The delivery wrapper refreshes the base and builds its temporary
worktree; no direct Git command was run in the shared read-only clone.

## Second reading by Q24

Worker final consistency reread, not a claim of an independent reviewer: read the
node statement and final signature together. The explicit right-factor A-algebra
presentation matches the surjection in the node; its derived restriction is along
that same p. The existential tower retains the given B -> A. Boundedness is only
cohomological, finiteness is over R_D, gamma is R_D-linear, and the universal transpose
equation fixes the action composite. The distinguished A-linear cone tests precisely
the same underlying cohomology bound as the R_D-linear cone. The boundary comparison
is a ≤ i, with no strict-bound substitution. No statement text was changed.
Independent review is performed by the maintainer on this self-delivered worker task,
as specified in the dispatch brief; no additional agents were started.


## Returned delivery repair

H2 on immutable head `110e2ac4e538`: repaired by the reviewer's inline-composite option.
Removed `lem-sfb-single-degree-coefficient-cone-cancellation` from stmt_deps; it
remains in proof_deps, unchanged. Replaced the sole occurrence of
`coefficientConeRestrictionSquareIso` in the signature with its exact composition /
derived congruence / inverse composition body, read from the landed module's lines
58–67. Explicit ring-map arguments fix both composite restrictions, and the same
`map_comp_includeRight` equality fixes the middle congruence. No new notion, helper
node, theorem, or change to the mathematical statement is needed.

Changed cancellation's public import to a plain proof import. Added direct public
imports for the definitions and ring constructions that the statement uses.
The node's recorded signature and note now describe the inline transport. Compared
with current main: all non-lean fields, including the original five stmt_deps and
all proof_deps, agree exactly. The sandbox before repair held the returned head's
helper call and erroneous extra statement dependency; both have been changed.

Final worker reread of the repaired signature: the expanded natural isomorphism
has source restriction along R_D -> R_A then D -> R_D and target restriction
along A -> R_A then D -> A. It is exactly the former helper's canonical
identity-on-elements transport. All existential objects, pseudo-coherence,
finite cohomology, scalar-action normalization, distinguished triangle and a ≤ i
bound are unchanged. This addresses the sole returned point; the maintainer's
independent reading found the remaining clauses faithful.
