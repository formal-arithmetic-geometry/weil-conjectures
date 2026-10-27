## Worker report

The module `Sheaf.CategoryTheory.CondensedRestrictionMateNormalization` states the mate,
bounded-below adjunction, injective-resolution and triangle clauses of the canonical derived
invariant restriction normalization. Public imports supply the existing computation-unit,
shift, degree-zero and identity clauses. Its new theorems have only `sorry` proofs. Two helper definitions give the actual ordinary trivial-action comparison and its
canonical exact localization; their components are identities of the original internal
modules. They select no arbitrary maps or isomorphisms. No node statement was changed and
no dependency interface needed repair.

Hypotheses and clauses, matched against the node:

- The small coherent profinite site and coefficient bound are inherited through
  `CondensedBar.Ring.{u}`: commutative ring objects in
  `Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1}`. This bundles exactly an
  arbitrary commutative condensed ring, with no topological presentation required.
  `Modules A` is the existing internal module category; `Equivariant A G` is the existing
  natural sectionwise linear action category. `G H : Type u` with `Group`,
  `TopologicalSpace`, and `IsTopologicalGroup` uses the same size convention as the
  recorded derived-invariants interface. No compactness, Hausdorffness, profiniteness,
  finite generation, or nontriviality of the groups is imposed.
- `invariants A G` has the fixed-section inclusion and both underived transpose formulas.
  `trivialDerived A G`, `derived A G`, and `adjunction A G` are the dependency's exact
  trivial inflation, ordinary unbounded derived invariants, and canonical derived
  adjunction. The computation unit is `.functor.rightDerivedFunctorUnitQ`.
  The common derived morphism universe is the recorded `u+1`; no new equality of
  independent site universes is assumed.
- A continuous homomorphism is `v : H →ₜ* G`; `groupDerived A v` is exactly D(v*).
  `restrictionTrivial` has identity internal-module components and is localized by
  `mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` to
  `restrictionTrivialDerived`. This writes out the canonical U L_G = L_H comparison
  which the informal formulas suppress.
- `groupMap_mate` says that the actual total-derived inclusion `groupMap A v` equals
  eta_H followed by F_H of the exact comparison and F_H(U epsilon_G), at every N.
  Its second conjunct gives the inverse Hom transpose as that same restricted counit.
  Equality to the canonical `groupMap` asserts beta = b, rather than just existence of
  a transformation with an arbitrary chosen normalization.
- `groupMapNormalization` from `Sheaf.CategoryTheory.CondensedDerivedInvariants` is the node's computation-unit equation at every complex
  P, with `inflate.mapDerivedCategoryFactors.hom.app P` displayed. The chain map is
  `NatTrans.mapHomologicalComplex (invariantRestriction ...) (.up ℤ)`.
- `groupMap_mate_plus` applies to either group (G is arbitrary). Its first conjunct is
  preservation of D+ (`∃ n, IsGE n` on the image); its second is the normalization of
  the canonical `rightDerivedFunctorPlusCompatibility` by the two computation units.
  That named comparison is a natural isomorphism from R+ followed by inclusion to
  inclusion followed by RF. Thus its inverse is precisely the node's theta. Both
  functors, their natural isomorphism and their units are existing library data.
- `groupMap_mate_plus_adjunction` states both the unit and counit comparison equations
  between the ambient adjunction and `.adjunction.derivedPlus`, using the canonical
  exact-inflation comparison and the computation-unit-normalized right-derived
  comparison. This specifies the restricted bounded-below adjunction itself.
- `groupMap_mate_injective_counit` quantifies over every integer lower bound and every
  degreewise injective complex I. It asserts invertibility of alpha_I and
  L(alpha_I); epsilon = Q(e_I), inserting the exact-localization comparison. Together
  with the preceding counit comparison, this is the requested termwise counit in D+.
- `groupMap_mate_resolutions` takes P, I, I', separate integer lower bounds, degreewise
  injectivity of I and I', and quasi-isomorphisms s : P → I and t : v*I → I'. It
  explicitly asserts invertibility of both injective computation units. Its equality
  is the representing-map square: identify F_G(QP) with Q Gamma_G(I) by
  alpha_I and inverse F_G(Qs), identify the target by F_H(UQs; factors; Qt), and
  obtain Q(iota_I); Q(Gamma_H(t)); alpha_I'. This retains the two distinct resolutions
  and assumes no preservation of injectives by v*.
- `groupMapShift` from `Sheaf.CategoryTheory.CondensedDerivedInvariants` is compatibility
  with every fixed signed integer shift.
  `groupMap_mate_triangles` states the first, second and connecting-arrow squares for
  every distinguished triangle. The third square includes both canonical
  `commShiftIso (1 : ℤ)` maps and the shifted component of b. Hence the components
  form a morphism of the two image triangles, with no last-arrow clause omitted.
- `restrictionDegreeZero` from `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`
  uses the dependency's `degreeZeroIso`, which is specified
  by H0(alpha), and the canonical `mapDerivedCategorySingleFunctor 0` for restriction.
  It says exactly H0(b) = iota under those normalized identifications.
- `identityRestriction` from `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`
  takes `[Subsingleton G]`, expressing the trivial-group
  case without choosing a particular carrier, and composes with the dependency's
  identity comparison `identityGroup` to give the actual identity of F_G(N).

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`; its general ring
  abbreviation is specialized by the dependency's bundled commutative ring.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`;
  these are the actual internal module objects and linear morphisms.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Profinite.CondensedAction.ActionModule`,
  `inflate`, `trivial`, `Invariants`, its inclusion and normalized transpose fields.
- `Sheaf.CategoryTheory.CondensedDerivedInvariants`: `invariants`, `derived`,
  `trivialDerived`, `adjunction`, `groupDerived`, `groupMap`, `invariantRestriction`,
  `degreeZeroIso`, `identityGroup`, and canonical shift instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`,
  `HasDerivedCategory`; the size convention has no additional mathematical object.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and `rightDerivedFunctorPlusUnit`, which are
  the recorded Mathlib match of lem-weil-pbc-right-derived-plus-injective.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`:
  `rightDerivedFunctorPlusCompatibility`, `rightDerivedFunctorPlusιUnit`,
  `ιRightDerivedFunctorUnit`; these are the existing comparison, not a new choice.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `Adjunction.derivedPlus`; the source gives its normalized unit and counit.
- The public exact-functor imports supply `mapDerivedCategoryFactors`,
  `mapDerivedCategorySingleFunctor`, `mapDerivedCategoryNatIso`,
  `mapDerivedCategoryCompIso`, and `mapDerivedCategoryPlusCompatibility`.

Proof-only imports follow every recorded proof dependency that has a declaration:
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`,
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
`Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
`Mathlib.CategoryTheory.Shift.CommShift`, and
`Mathlib.CategoryTheory.Abelian.RightDerived`.
The bounded subcategories are publicly supplied by the Plus imports.
The infrastructure and additive-plus-normalization proof nodes currently have no Lean
record; this statement uses the already recorded derived-invariants constructions and
upstream comparison directly, so it does not need their missing proof statements to type.
The repaired module publicly imports `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`
to reuse its existing identity and degree-zero clauses. That node lists this item as a proof
dependency. Consequently the maintainer must omit the reverse automatic proof import into
`CondensedDerivedRestrictionCalculus`, as required by stages/2-statements.md §3(7), to avoid
an import cycle. The current source of that module does not import this item.

Edge cases checked mathematically: zero coefficients/modules/complexes; all integer
lower bounds, including negative ones; identity and trivial homomorphisms; trivial groups
on arbitrary subsingleton carriers; noncompact and nondiscrete topological groups;
empty profinite test objects. The action and invariant definitions quantify over every
profinite base change. No injectivity preservation, coefficient flatness, or boundedness
of the general derived input was added. The bounded-below restrictions occur only in the
clauses where the node imposes them. Definition fields contain explicit identities, and
the categorical law fields are inferred proofs; no definition contains sorry data.

Searches made (all before finalizing the module):

- msearch.py leanfinder: “Derived invariants restriction natural transformation is the
  adjunction mate and agrees with fixed section inclusion on injective resolutions”.
  Eight hits, including InjectiveResolution.rightDerived_app_eq and augmentation
  formulas; none states this internal condensed derived-mate normalization.
- msearch.py loogle: “CategoryTheory.mateEquiv,
  CategoryTheory.Functor.rightDerivedFunctorPlus”: zero hits.
- msearch.py grep: “rightDerivedFunctorPlus|rightDerivedPullback|mateEquiv” in
  CategoryTheory: generic derived and adjunction infrastructure, no condensed theorem.
- msearch.py grep: “condensed.*(restriction|invariant)|CondensedDerivedRestriction|
  groupMap_mate”: zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf, by the node id, groupMap, mate/restriction,
  restrictionTrivial and groupMap_mate; inspected the full derived-invariants and
  derived-restriction-calculus modules. The former contains the canonical constructions
  and computation/shift properties; the latter has degree-zero/identity consequences
  and already states the degree-zero and identity clauses. The former already states the
  computation-unit and shift clauses. Neither states the mate equality or normalized
  plus-adjunction/resolution statement.
  Thus no declaration states the whole assigned node, and no second definition of its
  invariants, action, derived functors, restriction transformation or comparisons was
  introduced. Auxiliary comparisons `restrictionTrivial*` had no existing declaration.
- Read the blueprint direct-images proof paragraph (3), and the node's full eight-step
  proof with its Stacks references. The node is explicitly an agent-formulated auxiliary
  statement (exact external reference wanted); the delivery preserves this status.

No STATEMENT-DISPUTED flag and no mathematical node fault.

## Second reading by Q109

This is the author's self-check, as required for dispatcher direct delivery; no independent
worker was started. Independent review is performed by the maintainer after delivery.
Reopened the complete node and module and matched every clause as listed above. The mate
comparison direction is L_H → L_G U, so both composites have source L_H(F_G N). The
computation equation has source Q(Gamma_G P) and target F_H(Q(v*P)), after the explicit
factorization map. Both plus-adjunction comparisons use the same plus/unbounded right-derived
isomorphism and exact-inflation identification. The resolution square uses inverse F_G(Qs)
only because s is a quasi-isomorphism, and keeps an independent injective target resolution.
The connecting square uses the signed shift structures rather than just naturality at the
first two arrows. H0 and the identity case use the actual normalized dependency comparisons.
The compiler found syntax errors in a piped shift expression and a missing pair of
parentheses around the single-functor comparison component; both were repaired. The triangle
clause explicitly takes a distinguished triangle, matching the node's image-triangle claim.
No source statement, dependency record, or DAG edge was changed. The repair self-check below
updates which declarations supply the four existing clauses.

## Repair of return L (immutable head 27013c65ed24)

The initial saved-packet dry run passed as commit 828faa775cc; that mechanical result did
not resolve the maintainer's duplicate-statement return. Compared the saved module and
node record with the returned descriptions and current shared main. The main node has no
Lean attachment; the saved node differs from it only in `lean`. Retained the original mate,
plus-adjunction, injective-counit, resolution and triangle statements and the real-data
comparison definitions.

Removed `groupMap_mate_identity` and `groupMap_mate_shift`, rather than adding aliases or
new proofs. The trivial-group identity clause now uses the public existing theorem
`CategoryTheory.CondensedDerivedRestriction.identityRestriction` from
`Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`; the shift clause uses
`CategoryTheory.CondensedDerivedRestriction.groupMapShift` from
`Sheaf.CategoryTheory.CondensedDerivedInvariants`. Read their full signatures and surrounding
variable declarations: both use `A : CondensedBar.Ring.{u}`, `G : Type u` with `Group`,
`TopologicalSpace` and `IsTopologicalGroup`. The shift statement additionally has `H` with
those same structures and `v : H →ₜ* G`; the identity statement has `[Subsingleton G]`
and `N : DerivedCategory.{u+1} (Equivariant A G)`. These are the same binders and conclusions
as the removed statements; implicit versus explicit binding of A does not change the claim.

The same self-check found two further existing clauses and removed their duplicate
statements as well: `groupMap_mate_computation` is supplied by
`CategoryTheory.CondensedDerivedRestriction.groupMapNormalization` in
`Sheaf.CategoryTheory.CondensedDerivedInvariants`, and `groupMap_mate_degreeZero` by
`CategoryTheory.CondensedDerivedRestriction.restrictionDegreeZero` in
`Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`. Their complexes, coefficients,
actions, comparison maps and equations agree after renaming the complex binder P/K and
making the inferred `R := A.toMon` explicit. No mathematical clause was removed from the
node; these clauses are supplied by the imported existing statements.

Added the public restriction-calculus import. Updated the module's main-statement list,
node `lean.declarations` (only declarations actually owned by this module) and `lean.note`
with all four reused theorem names and modules. No replacement theorem or proof was added.
Targeted source searches used `rg -n` for `identityRestriction`, `groupMapShift`,
`groupMapNormalization`, `restrictionDegreeZero`, `variable` and `universe` in the two
existing modules, followed by reading their complete signatures and docstrings.
The own-theorem list now consists of exactly the mate/transpose, D+ preservation/comparison,
D+ unit/counit, injective counit, two-resolution computation and three triangle squares.
The clause-by-clause worker report above has been updated to cite the existing declarations.

Rechecked the zero and trivial cases and the comparison directions against the full node.
The mate source remains F_G N; its transpose has source L_H(F_G N). The real comparison
has direction L_H → L_G U. The resolution equality retains two injective resolutions and
the separate quasi-isomorphisms, and the triangle clause retains the connecting square.
No dependency declaration or mathematical node statement needed a correction.

Validation of the repaired packet: scompile.py Q109 compiled the delivered file in both
sandbox and library module modes against the live server build (23.2 s and 24.3 s), with
no errors or unexpected warnings. A source self-check verified that only `lean` differs
from current main, all eight owned declarations match `lean.declarations`, the main
signature is recorded verbatim, all six new theorem proofs are `sorry`, all four duplicate
declarations are absent, and every Lean source line is at most 100 characters.

## Maintainer review fix (5df0b8df7db7)

The public import of `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus` was removed.
No declaration of this module uses it, and it is the module of the node
lem-sfb-condensed-derived-restriction-calculus, which lists this item as a proof dependency.
Keeping the import would have stopped that module from importing this one for its stage-3 proofs,
because the import would close a cycle. The degree-zero and identity clauses are still not
redeclared. The module docstring and `lean.note` now name the two existing theorems in that
module, together with proof steps 7 and 8. The usual proof-dependency import of this module
into CondensedDerivedRestrictionCalculus is no longer omitted. No statement changed.
