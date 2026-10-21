## Worker report

This is a stage-2 statement delivery, not another split. NF's stage-1 split was merged
and reviewed (coord/ledger.md, 19:55 on 2026-10-21), but the current item has no lean
record. The retained assignment's previous blocker confused those two stages. The
statement, source, proof, proof_deps and stage-1 review are preserved verbatim.

The main module is lean/Sheaf/Paper/IndUnipotentProcyclicDifference.lean. Its theorem
Profinite.CondensedAction.IndUnipotent.ind_unipotent_procyclic_difference states the
ordinary derived isomorphism, with its exact H^0 inclusion normalization. Its only
proof is sorry. IndUnipotentSystem.lean supplies the input/presentation definition;
its exists_presentation theorem is also sorry. No definition takes data from either
postponed theorem. All variables/universes are explicitly bound; autoImplicit is false.

Hypotheses and clauses, in the order of the natural-language statement:

* Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The algebraic closure is `(Ω : Type u)
  [NormedField Ω] [Algebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`; hΩ fixes its extended
  normalized p-adic norm. Neither completeness nor a completed closure is assumed.
* The finite intermediate field is expressed without choosing a concrete subtype:
  E is a normed finite-dimensional Q_ell field, with Q_ell-algebra embedding j into
  Ω; hE identifies its norm with the inherited norm. The E-algebra structure of Ω
  is pinned to j by hj. This is precisely a finite intermediate field up to its
  unique identification with j.fieldRange, and includes every intermediate field.
* F has an E-algebra embedding ι into Ω and hι makes that embedding isometric.
  hF says either E -> F is surjective or ι is surjective. Since field embeddings
  are injective, the former identifies F with E, the latter identifies it with Ω.
  Conversely both coefficient choices in the node supply this data. This avoids
  topology-instance ambiguity on nested intermediate-field subtypes, without adding
  a field case or requiring a completion. Both topologies are exactly the original
  norm topologies. E and F may live in the arbitrary common site universe u.
* The existing coefficient ring is `normContinuousRing F`, whose carrier and monoid
  structure are `continuousMapRingObjOfUniverse F` and its recorded MonObj. It is
  the all-continuous C(S,F) condensed ring, including when F is noncomplete.
* G is a Type u group with TopologicalSpace, IsTopologicalGroup, CompactSpace,
  T2Space, and TotallyDisconnectedSpace. The additive p-adic integer group is
  `IntegerGroup ℓ := Multiplicative (ULift (PadicInt ℓ))`. Its topology is the
  original p-adic topology, not the discrete topology. Its norm-topological and
  inverse-limit-topological descriptions coincide. `generator ℓ` is additive 1;
  multiplicative `1` is additive 0. In particular retained restricts by (g,0).
* T.V n are the arbitrary finite-dimensional E-vector spaces, bundled as ModuleCat;
  they live in Type (u+1), as required by the already landed realization interface.
  T.finite expresses finite dimension. Finite-dimensional Hausdorff norm topology
  is exactly moduleTopology, used by T.continuous. This encodes arbitrary such
  spaces, rather than restricting to a chosen coordinate space.
* T.transition and T.injective are the injective linear inclusions. T.operator,
  T.exponent, T.positive and T.nilpotent give exactly D_n and D_n^(e_n)=0 with
  e_n >= 1. T.compatible is the equation commuting D with transitions.
* T.action is the combined G x H representation. T.commutes is the commutation of
  D with G; T.equivariant is compatibility with transitions. T.exponential states
  the finite sum from the node verbatim, with t mapped through Q_ell into E.
  The combined action's joint continuity and H-equivariance impose no extra
  mathematical assumption: continuity is a finite polynomial in t and continuous
  G-action, and compatibility follows from D compatibility. They record the
  properties of the uniquely specified combined action, so no action is arbitrary.
* P.stage uses exactly `PrimeToEll.Extended E F (T.V n)` and
  `extendedRepresentation ... (T.action n)`, realized by the landed
  `ContinuousRepresentation.Realization`. Extended is the actual F tensor_E V_n,
  endowed with its finite-dimensional module topology. The Realization scalar,
  restriction and action fields pin sections, scalar multiplication, restrictions,
  and action on every generalized element. P.identify permits any isomorphic
  representative. P.transition specifies the original scalar-extended transition
  on every profinite section. exists_presentation supplies these presentations for
  continuous coefficient maps; hE, hι and hj ensure this condition here. Its
  existence is not used to choose unknown data in a definition.
* c is a cocone on P.diagram, hc its IsColimit certificate in the FULL internal
  G x H action category. Thus c.pt is precisely the sheaf colimit required by the
  node, up to its canonical colimit isomorphism. No topology on the colimit, no
  sectionwise completion, and no bound on the sequence are introduced. Colimits
  exist by the landed Grothendieck action-category structure.
* v is any existing normalized ProductInvariants datum, including its sectionwise
  fixed-submodule inclusion, projection-inflation adjunction and residual G-action.
  Its existence is already the product_action_inflation theorem; its specification
  fixes the functor up to normalized isomorphism. No new assumption on the modules
  or the group is hidden in v. retained keeps the original G-action on c.pt.
* DifferenceModel existentially supplies an ACTUAL equivariant internal map d and
  specifies on EVERY profinite S and section m that d(m)=tau.m-m. This uniquely
  characterizes d, rather than allowing an arbitrary endomorphism. At each finite
  stage T.exponential identifies tau with exp(D_n); compatible transitions identify
  its colimit with exp(D). Consequently this is exactly exp(D)-1. D itself is the
  induced compatible endomorphism; no infinite exponential series is used.
* differenceComplex is Mathlib's actual HomologicalComplex.double d, at integer
  degrees 0 and 1. e is an isomorphism from the ordinary rightDerivedFunctor of
  v.functor on c.pt[0] to DerivedCategory.Q.obj of this complex. Source and target
  are in D(ActionModule (normContinuousRing F) G). Derivation is in the full
  Grothendieck action category, using the existing K-injective API. There is no
  derived functor on a smaller class of ind-unipotent representations.
* z identifies v.functor.obj c.pt with degree-zero complex homology. The equation
  `(z.hom ≫ differenceH0Inclusion ...).val = v.inclusion.app c.pt` identifies them
  by their common inclusion into c.pt. differenceH0Inclusion uses the canonical
  homology-to-opcycles map and the inverse of the canonical pOpcycles isomorphism
  (the incoming differential is zero), then the actual degree-zero term identity.
* The final H^0 square uses the canonical right-derived unit invariantUnit and
  DerivedCategory.homologyFunctorFactors. It asserts that H^0 of THE SAME e is z,
  with the standard H^0(single degree zero) identification. Thus the derived iso
  itself, not an unrelated cohomology isomorphism, has the required normalization.

Dependency declarations read and used:

* Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingObjOfUniverse and its monoid/commutativity structures,
  through the landed normContinuousRing in Sheaf.Paper.NormContinuousMonodromyData.
* Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod, ModObj and equivariant
  internal module morphisms; Sheaf.CategoryTheory.CondensedActionModule: Modules,
  sectionModule, ActionModule, inflate and ProductInvariants, including every field
  of its full signature and normalized inclusion/adjunction specification.
* Sheaf.CategoryTheory.CondensedProductActionInflation: product_action_inflation.
  Sheaf.CategoryTheory.CondensedProductBarComparison: productBarActionAbelian and
  productBarActionGrothendieck, derived from that very theorem without a changed
  sectionwise addition. This already landed node is added to stmt_deps.
* Sheaf.CategoryTheory.CondensedDerivedInflationArrows: PrimeToEll.actionsDerived
  and modulesDerived supply the standard localization sizes. This already landed
  definition node is added to stmt_deps. The product invariant unit is constructed
  from the generic rightDerivedFunctorUnitQ, rather than copying its scalar version.
* Sheaf.Paper.ContinuousRepresentationCondensation: ContinuousRepresentation.Realization,
  exists_realization, exists_unique_map, and PrimeToEll.Extended,
  extendedTopology, extendedRepresentation. Their full section/action and topology
  signatures were read. This notion is cited through the new node and not duplicated.
* Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, Q and
  HasDerivedCategory. FullyFaithful gives the canonical single/H^0 isomorphism;
  ShortComplex.HomologicalComplex gives homologyι and pOpcyclesIso; Double gives
  double and its actual degree-zero identification. The metatheoretic size
  convention is rendered by explicit u and the standard u+2 derived localization.

Every currently stated proof dependency is imported non-publicly: normed scalar
profinite internal-Hom acyclicity, first-quadrant total comparison, derived invariant
bar, complex short-exact triangle, triangle two-out-of-three, and the abstract derived
category. Unstated proof-only nodes are not assumed as hypotheses. Their full ten-step
proof plan is carried in the theorem docstring, separating complete E from noncomplete Ω.

Edge cases checked mathematically: G trivial uses exactly the same action category;
V_n=0 gives zero realizations and the zero double complex; D_n=0 (e_n=1) gives
identity H-action and differential zero, hence degree-zero and degree-one copies of
M. A 2-by-2 nilpotent Jordan block gives the expected ker D and coker D, fixing the
positive generator-minus-identity convention. Increasing Jordan blocks permit
unbounded e_n and dimension, since both are functions of n and no bound occurs.
The empty profinite test set is included in all section and naturality quantifiers.
Neither complete scalar topology nor uniform nilpotence is used in the signatures.
No statement dispute or source correction was needed.

Searches (all three required kinds were actually run by msearch.py):

* LeanFinder, derived invariants of p-adic procyclic group on countable ind-unipotent
  representations: eight hits on finite abstract cyclic groups, not this statement.
* Loogle, `"procyclic", "cohomology"`: zero hits.
* Mathlib grep, `(procyclic|nilpotent|unipotent).*(cohomolog|invariant)|...`:
  zero hits. LeanSearch, derived invariants continuous procyclic unipotent
  representation condensed modules: eight hits on discrete coefficient condensed
  modules or ordinary topological continuous cohomology; no match.
* For the new system node: LeanSearch, `Sequence of finite dimensional nilpotent
  representations with commuting profinite action and exponential p adic integer
  action`, found individual nilpotent operators and finite exponentials only.
  LeanFinder, `Countable system of finite unipotent continuous representations
  with nilpotent operators and injective transition maps`, found unrelated
  nilpotent Lie/root representations. Mathlib grep,
  `IndUnipotent|indUnipotent|ind_unipotent|ContinuousRepresentation.Realization`,
  gave zero hits. Raw tool records, queries and result digests are in that node.
* Project rg on WeilConjectures and Sheaf for procyclic, ind-unipotent and the item
  id found no theorem. The abstract subgroupIndUnipotent is a different object.
  A further search found the continuous-section realization and tensor topology;
  these are reused. DAG grep found this item and its polynomial-translation consumer;
  blueprint_refs search `ind unipotent` returned zero blueprint nodes. The item's
  blueprint ancestor is None, preserved in the new node. Existing names were
  checked in Mathlib, WeilConjectures and Sheaf before creating the new declarations.

## New nodes

`def-sfb-ind-unipotent-system` defines exactly the finite nilpotent system and its
continuous-section diagram presentation needed to state this item. It also states
existence of the presentation for continuous coefficient inclusions, with a complete
natural-language construction proof. Its source is this item's source, paragraph (3)
of the current main-20261015 direct-image proof, agent-formulated rank-one input.
It is not a second definition of a realization, tensor topology, module category,
profinite group or nilpotence: it reuses those existing objects and packages only the
compatible countable sequence and its exponential/transition equations. The searches
above distinguish it from abstract ind-unipotent subgroup representations. All its
definitions have real data; existence is a named theorem with sorry, and no definition
chooses a presentation from it. The item cites this new definition directly.

## Second reading by NI

The dispatcher explicitly forbids starting other agents; no independent second worker
was started. I performed a separate consistency reading of the node and both modules;
the maintainer's independent review remains required. This pass checked additive zero
versus the multiplicative identity of H, degree 0/1 placement, the direction of the
canonical derived unit and homology factorization, the actual tensor transition maps,
and the joint inclusion normalization of e and z. It also confirmed that the norm
compatibility/field-embedding presentation covers precisely F=E and F=Ω up to canonical
coefficient isomorphism and excludes no zero or unbounded-stage cases. The only
compiler repairs were a parenthesis, the canonical previous-degree equality, and
transporting total disconnectedness through the universe lift; no source statement,
module category or mathematical hypothesis was weakened.
