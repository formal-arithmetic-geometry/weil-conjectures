## Worker report

Item: lem-sfb-condensed-cup-mate-coherence. Group Q48, stage 2.
Module: Sheaf.CategoryTheory.CondensedCupMateCoherence.
Main declaration: CategoryTheory.CondensedDerivedRestriction.cupMateCoherence.
The node's mathematical statement and accepted proof split are unchanged. No new nodes
or dependency-node replacements are needed. All theorem proofs are `by sorry`.

The module uses the actual condensed internal-action categories and actual normalized
functors. It supplies the missing canonical group/scalar action tensor interfaces as
helpers of this node, as authorized by the launcher. These are not arbitrary comparison
maps: ordinary group comparison is fixed by the underlying tensor identity; scalar
comparison is fixed by the balanced underlying scalar map; both derived comparisons
include their unit and total-complex localization equations. Every data selection uses
a uniqueness theorem, not a mere Nonempty existence assertion. The underlying objects,
module categories, derived categories, functors, and scalar/base tensor structures are
all the recorded existing ones.

Hypotheses and clauses, in order:

- The small coherent profinite site, its section sizes and the larger coefficient
  universe are the existing `CondensedBar.Ring.{u}`, `Modules`, `Equivariant`, and
  `DerivedCategory.{u + 1}` encodings. `universe u` and `autoImplicit false` make all
  universes and variables explicit. There is no additional smallness restriction.
- An arbitrary commutative condensed coefficient ring is `A : CondensedBar.Ring.{u}`.
  This is CommMon of the existing abelian-sheaf tensor category, not a topologically
  presented or discrete ring. The same holds for `A'`.
- Arbitrary topological groups are `G H : Type u` with Group, TopologicalSpace and
  IsTopologicalGroup; no compactness, profiniteness, separation, finiteness or discreteness
  is required. The continuous group map is `v : H →ₜ* G`.
- The given internal modules and natural C(S,G)-actions are the existing `Modules A`
  and `Equivariant A G` (an abbreviation of Profinite.CondensedAction.ActionModule).
- The ordinary unbounded derived categories, normalized invariant functor, trivial
  inflation and actual adjunction are `derived A G`, `trivialDerived A G` and
  `adjunction A G` from CondensedDerivedInvariants. `groupDerived A v` and `groupMap A v`
  retain the invariant-inclusion normalization and canonical computation units.
- The derived tensor and signed total comparisons are the existing K-flat tensor.
  The existing `derivedTrivialMonoidal` is strong and is built from
  `derivedTrivialTensor`; its ordinary and derived normalization predicates were read.
  The first main conjunct gives the symmetry equation for this exact tensorator,
  using the explicit canonical Koszul `DerivedCategory.braidedCategory'` on both sides.
  No alternate braiding or tensor structure is chosen.
- The lax pairing and unit are the existing `derivedLax`. `CounitMateModel` states
  exactly the two adjunction transposes: inverse homEquiv of μ is δ_L followed by
  the tensor of the actual counits; inverse homEquiv of ε is η_L, the inverse strong
  unit comparison. The second main conjunct says these equations characterize exactly
  `derivedLax`. Associativity and both unit laws are fields of this LaxMonoidal
  structure, so they are retained rather than imposed as new hypotheses.
- The next two conjuncts state `NatTrans.IsMonoidal` for the actual adjunction unit
  and counit. This class includes both tensor and unit equations.
- The group tensor equation and its unit equation are
  `NatTrans.IsMonoidal (groupMap A v)`. Expanding its tensor field gives
  μ_G ; b_(X tensor Y) = (b_X tensor b_Y) ; μ_H ; F_H(μ_U).
  Our strong restriction structure has μ_U = t_U inverse, exactly the displayed
  node equation. Its unit field is ε_G ; b_unit = ε_H ; F_H(ε_U).
  `coefficientRestriction` and the explicitly stated `groupCupMap` unit equation
  give the node's regular-unit formulation.
- An arbitrary condensed ring map is `a : A ⟶ A'`. The scalar monoidality conjunct
  is `NatTrans.IsMonoidal (scalarComparison (G := G) a).hom`. Its source is
  `scalarDerived a G ⋙ derived A G` and target is `derived A' G ⋙ scalarBase a`,
  exactly F_R s_J -> s_0 F_R'. Typeclass composition supplies the composite lax
  structures. The base structure is the dependency's `scalarLax`; the action structure
  is `scalarActionDerivedLax`, fixed by the same balanced computation equation.
- The following two conjuncts are CommShift of groupMap and scalarComparison for ℤ.
  These are the existing canonical signed shift structures, not arbitrary alternatives.
- The three cup algebra conjuncts give associativity with the actual associator,
  and left and right unit equations with the actual unitors, for existing `cup` and
  `cupUnit` on `cohomology A G = (derived A G).obj (coefficient A G)`.
- The next two conjuncts say `groupCupMap` preserves binary cup and unit.
- The next two say `coefficientCupMap` preserves binary cup and unit, with precisely
  μ_(scalarBase a) before scalar image of multiplication and ε_(scalarBase a)
  before scalar image of the cup unit. There is no coefficient-flatness hypothesis.
- The last two conjuncts quantify over EVERY `n : ℕ` and assert the orderedProduct
  equalities for the actual group and coefficient maps. `tensorPowerMap` preserves
  factor order and the dependency's right-associated recursion. The target scalar
  algebra is exactly its lax scalar image. In particular n = 0 is the empty product.
  These are equalities of derived arrows, so precomposing them with ANY tensor of
  homogeneous class arrows gives the corresponding graded equality. The fixed
  `DerivedCategory.shiftTensorShiftIso` can be used to form those source arrows;
  no new comparison or permutation occurs. The CommShift conjuncts also identify
  the shifted group/scalar components with the shifts of these very components.

Dependency declarations used (namespace CategoryTheory.CondensedDerivedRestriction
unless a full namespace is given):

- def-weil-size-convention: convention record, rendered through universe u and the
  already fixed coefficient/site sizes; there is no declaration to import.
- sk-def-sfb-condensed-ring: Sheaf.Topology.ProfiniteCondensedRing,
  Profinite.CondensedRing; used through the existing bundled CommMon refinement
  CondensedBar.Ring and its underlying toMon.
- sk-def-sfb-module-objects: Mathlib.CategoryTheory.Monoidal.Mod, CategoryTheory.Mod;
  used through existing CondensedBar.Modules and regular module.
- def-sfb-condensed-action-module: Sheaf.CategoryTheory.CondensedActionModule,
  Profinite.CondensedAction.ActionModule, inflate and its ordinary unchanged maps.
- def-weil-abstract-derived-category: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  DerivedCategory, HasDerivedCategory, Q and singleFunctor.
- def-sfb-condensed-derived-invariants: Sheaf.CategoryTheory.CondensedDerivedInvariants,
  derived, trivialDerived, adjunction, groupDerived, groupMap, scalarAction,
  scalarDerived, scalarBase, scalarComparison and their computation-factor isomorphisms.
- def-sfb-condensed-action-tensor: Sheaf.CategoryTheory.CondensedActionTensor,
  actionTensor, actionMonoidal, actionFlat, trivialTensor and their forgetCore comparisons.
- def-sfb-condensed-derived-cup: Sheaf.CategoryTheory.CondensedDerivedCup,
  derivedTrivialTensor, derivedTrivialMonoidal, derivedLax, coefficient, cohomology,
  cup, cupUnit, coefficientRestriction, groupCupMap, tensorPower, tensorPowerMap,
  orderedProduct. We retain the existing degree-zero regular coefficient identifications.
- def-sfb-condensed-scalar-tensor: Sheaf.CategoryTheory.CondensedScalarTensor,
  scalarModules, scalarOrdinaryLax, scalarLax and coefficientCupMap.

Statement dependencies are publicly available through CondensedScalarTensor. Explicit
proof imports include the recorded ActionToposGeometricRestriction,
RingedDerivedMonoidalComparisons, CondensedRestrictionMateNormalization and
DerivedTensorShiftDescent modules, and Mathlib Adjunction.Mates. The Mathlib leaves
monoidal-adjunction-mates, monoidal-adjunction-unit-counit, composite-adjunction and
integer-total-tensor-shifts are already available through the imported monoidal,
adjunction and shift modules. The action-injective-infrastructure,
derived-scalar-lax-normalization and scalar-restriction-interchange proof nodes have
no recorded Lean module in the read snapshot, so there is none to import. The downstream
CondensedDerivedRestrictionCalculus is deliberately not imported: that node lists this
item as a proof dependency. Its already existing cupLaws/restrictionCup/coefficientCup
and ordered-product statements are not copied into individual new declarations; the
main theorem packages those consequences together with the additional mate coherence.

Edge cases checked before writing and again on the statement:

- Zero coefficient ring: regular module and tensor unit still exist, and all maps and
  universal properties remain typed; no nonzero hypothesis occurs.
- Trivial groups and identity group map: the underlying identity tensor/unit formulas
  and normalized group mate reduce to the expected identity comparisons.
- Identity coefficient map: scalar comparison and scalar lax unit retain the actual
  regular identities under the existing normalization.
- Nonflat coefficient map, e.g. Z -> F_l at a point: the derived scalar tensor map is
  allowed to kill positive Tor. Its computation equation RETAINS μ_Q on restricted
  complexes and never inverts it, so there is no erroneous K-flat-over-Z assumption.
- n = 0 uses tensorPower 0 = tensor unit and orderedProduct 0 = cupUnit; n = 1 uses
  the fixed unitors, and n = 2 is the binary equation with the right-associated source.
- All integer shifts, including zero and negative shifts, use the canonical commShift
  structures and the existing first-then-second signed tensor shift extraction.
- Generalized sections on empty profinite test objects are included in the underlying
  model specifications; no nonempty test-object assumption has been introduced.

Searches performed before writing (recorded also by msearch in searches.jsonl):

- leanfinder: "Derived invariants of condensed group actions tensor counit mate cup
  product monoidal group and scalar restriction". Eight hits: Rep coinvariant/induction
  maps and LightCondensed monoidal closedness, none the stated internal varying-ring
  normalized derived assertion.
- loogle: "CategoryTheory.Adjunction.rightAdjointLaxMonoidal,
  CategoryTheory.NatTrans.IsMonoidal". Zero hits for the combined query; the individual
  declarations were read directly and reused.
- Mathlib grep via msearch: "(Condensed|condensed).*(cup|LaxMonoidal)|
  (cup|LaxMonoidal).*(Condensed|condensed)". Zero hits.
- leansearch: "Lax monoidal structure on a right adjoint as tensor of counits mate and
  monoidal natural transformations". Eight generic hits, including rightAdjointLaxMonoidal,
  IsMonoidal unit/counit and whiskering. These generic notions are reused, not copied.
- rg on lean/WeilConjectures for the node id: no matches. Concept searches for cup
  coherence and associativity find generic projection-cup and etale cup theorems,
  which concern different categories and maps.
- rg on lean/Sheaf for groupCupMap, coefficientCupMap, orderedProduct and monoidal
  restriction: the recorded cup/scalar definitions and the downstream restriction
  calculus supply the specific definitions and several individual consequences, but
  not the full mate theorem or the missing normalized group/scalar action interfaces.
- DAG search for "restriction tensorator", "restriction.*strong monoidal" and
  "scalar.*diagonal.*tensor" identifies generic internal-restriction-module-tensor
  and derived-inflation normalization nodes. Neither records this specialized derived
  group/scalar action comparison. Helpers here only type the comparisons of this
  node; no independent DAG notion has been invented.

No statement correction, STATEMENT-DISPUTED flag or known mathematical fault.
The source's exact external-reference-wanted status is retained in the module source
attribution, rather than replaced by a fabricated citation.

## Second reading by Q48

This dispatcher assignment explicitly prohibits starting another agent and says the
maintainer supplies the independent delivery review. Consequently this section records
an in-thread second pass, not a claim of an independent worker's review.

I reopened the node and the final source and compared the hypotheses and clauses above.
The initial direct braiding expression lacked a small-colimit derivability instance;
I replaced it with the published canonical DerivedCategory.braidedCategory' wrapper,
which supplies that instance internally. I corrected the orientation to
μ_L ; L(β) = β ; μ_L. I checked the two scalar composites' direction against the actual
scalarComparison signature, and added explicit CommShift conjuncts for both normalized
transformations. I checked the total-complex scalar model against DerivedScalarTensorModel:
its noninvertible localization map stays on the left of the balanced chain map. The
unit model uses the singleMapHomologicalComplex inverse in the same direction as the
recorded base scalar model. No local notation, local instances, hidden let binders,
auto-bound variables or proved theorems remain. Every helper's postponed assertion has
a source and a complete mathematical construction/uniqueness argument in its docstring;
the main docstring carries all twelve accepted proof steps.
