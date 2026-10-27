## Worker report

Item: `lem-sfb-stack-topology-open-substacks`, group NR, stage 2.
Module: `Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks`.

This is the repair of return L on immutable head `017950a4d632`.
The module has one concrete definition, `OpenModuliSubstack.pointImage`, and five
named theorems with `sorry` proofs. It reuses the existing field-point quotient,
closed-set predicate, chart preimages, open substacks and 2-fibre products.
No topology or scheme-point map is defined. There are no new nodes, dependency
modules, mathematical statement corrections or STATEMENT-DISPUTED flags.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `{S : Scheme.{u}}` is the arbitrary base scheme. The stacks are
  `F : BasedCategory.{v₁, w₁} (Over S)` and, in the pullback clause,
  `G : BasedCategory.{v₂, w₂} (Over S)`. Their DM hypotheses are
  `hF : IsDeligneMumfordModuliStack F` and the corresponding `hG`.
  No finiteness, separation, characteristic or base-field restriction is added.
  Stack object and arrow universes are independent of each other and of u.
- The field-valued quotient is the existing `ModuliPoints F`, namely the quotient
  of `ModuliFieldObject F` by the arrow-generated `ModuliFieldRelation F`.
  `moduliPoints_eq_iff_common_field` states that two representatives are equal
  exactly when some field object z has arrows to both. Every arrow in a category
  fibred in groupoids is cartesian: these are precisely the two field extensions
  and their common pullback isomorphism. The fields remain in the scheme universe u.
- Opens are expressed by `ModuliPointIsClosed F Wᶜ`, using the definition already
  owned by `def-sfb-dm-stack-morphism-properties`. Its chart preimage is the existing
  `moduliChartPreimage a W`, which tests actual field representatives above each
  scheme point. The theorem `moduliPointIsClosed_compl_iff` quantifies over every
  scheme atlas `a`, with exactly `ha : IsEtaleModuliAtlas a`, and states
  `ModuliPointIsClosed F Wᶜ ↔ IsOpen (moduliChartPreimage a W)`.
  Thus any individual étale surjective atlas tests exactly these same opens.
  Complements translate the existing closed-set convention into the node's open-set
  convention. No fourth topology is introduced.
- The scheme clause `moduliSchemePoint_topology` gives an equivalence
  `e : T.left ≃ ModuliPoints (discreteModuli (yoneda.obj T))` for every `T : Over S`.
  Its first conjunct characterizes this equivalence for every subset W by
  `moduliChartPreimage (BasedFunctor.id (discreteModuli (yoneda.obj T))) W = e ⁻¹' W`.
  In particular singleton subsets determine e uniquely: it is the residue-field
  identification, not an arbitrary bijection. Its second conjunct says that W has
  closed complement exactly when `e ⁻¹' W` is open in the usual scheme topology.
  These clauses give the canonical point identification and the usual topology.
- An open substack is the existing `OpenModuliSubstack F`. Its `property` gives a
  full subcategory, `pullback` gives stability under all arrows, including fibre
  isomorphisms, and `open_pullback` identifies every scheme 2-base change, with its
  projection, with an actual open immersion. Thus it is strictly full and has all
  the scheme tests in the node. `category` is this same full subcategory.
- `OpenModuliSubstack.pointImage` is the actual range of
  `moduliPointMap (fullModuliInclusion F U.property)`. This is precisely |U| inside |F|.
- `moduliOpenSubstack_pointImage_bijection` gives an equivalence from open substacks
  to `{W : Set (ModuliPoints F) // ModuliPointIsClosed F Wᶜ}`. Its explicit clause
  `(e U).val = U.pointImage` identifies the assignment with the actual point image;
  the equivalence supplies injectivity and surjectivity. The final clause
  `U.IsContainedIn V → (e U).val ⊆ (e V).val` is inclusion preservation.
- `moduliOpenSubstack_pointImage_pullback` quantifies over every `BasedFunctor G F`,
  with no representability, smoothness or surjectivity hypothesis. The resulting
  `V : OpenModuliSubstack G` has exactly the predicate `U.property (f.obj y)`.
  Its category is equivalent to the actual
  `moduliTwoFiberProduct f (fullModuliInclusion F U.property)`, and `ModuliTwoIso`
  identifies the composite with the first projection with the inclusion into G.
  The final equality is exactly
  `V.pointImage = moduliPointMap f ⁻¹' U.pointImage`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsFibredInGroupoids`, `ModuliTwoIso`, `discreteModuli`, `discreteModuliMap`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `IsModuliStack`,
  `HasSpaceBaseChange`, `SpaceMapIsEtale`, `SpaceMapIsSurjective`, and
  `IsDeligneMumfordModuliStack`. Read their full signatures and docstrings.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `ModuliFieldObject`, `ModuliFieldRelation`, `ModuliPoints`, `moduliPointMap`,
  `IsEtaleModuliAtlas`, `moduliChartPreimage`, and `ModuliPointIsClosed`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `fullModuliInclusion`, `OpenModuliSubstack.category`, and
  `OpenModuliSubstack.IsContainedIn`.
- `Mathlib.CategoryTheory.FiberedCategory.BasedCategory`: `BasedFunctor.id`.

The two added statement dependencies are the already-landed DEFINITION nodes
`def-sfb-dm-stack-morphism-properties` and `def-sfb-open-moduli-substack`, as allowed
by brief-stage2 section 5. The unneeded theorem dependency
`lem-sfb-smooth-presentation-closed-subsets` has been removed from the saved packet.
Neither it nor its module is used. Compared with the current read-clone node,
only `lean` and these two allowed definition-node additions in `stmt_deps` differ.
The node's statement, proof and proof dependencies are unchanged.

Proof-only imports follow the recorded common-extension-fields theorem, affine
étale-cover theorem, open-subspace classification theorem and Mathlib étale open-map
input. The chartwise-calculus node has since acquired a landed Lean record, so its
module `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus` is now imported
as a proof dependency too. `lem-sfb-invariant-open-substack-descent` still has no
recorded Lean declaration and is named in the proof docstring; no import can yet
be added for it. It is not needed to type the stage-2 statements.

Edge cases checked before the repair:

- Empty stack and empty scheme: empty quotient, unique topology and unique open
  substack. The scheme equivalence is the empty equivalence. No nonemptiness binder.
- Empty and whole opens: complements are respectively whole and empty; all atlas
  preimages and point images have the expected values. Pullback covers both.
- Identity atlas: its chart preimages identify the ordinary scheme subsets,
  including every singleton, so the scheme equivalence is canonical.
- Identity f and arbitrary f: the predicate, equivalence over G and point inverse
  image all remain present. No condition on f excludes the identity or empty source.
- Arbitrary fields, including imperfect fields and inseparable extensions:
  all field objects and all common extensions are included.
- Arbitrary disconnected and non-Noetherian S: no special base hypothesis is used.
- Fields and residue fields live in Type u for Scheme u; the stack category
  universes remain independent. No extra universe equality was introduced.

Searches and source checks:

1. Saved `msearch.py ... leanfinder "The topology of a Deligne Mumford stack is
   independent of its etale atlas and open substacks correspond to open subsets"`:
   eight ordinary scheme/presheafed-space hits, no stack classification theorem.
2. Saved `msearch.py ... loogle "TopologicalSpace.coinduced, OrderIso"`: zero hits.
3. Saved `msearch.py ... grep "OpenSubstack|DeligneMumford|ModuliStack|StackPoint"`:
   zero Mathlib hits.
4. Saved `msearch.py ... leansearch "Open substacks of a Deligne Mumford stack
   correspond bijectively to open subsets of its underlying topological space"`:
   eight hits concerning scheme opens and scheme open immersions, no stack theorem.
5. Repair search `rg -n 'moduliSchemePointMap|moduliPointTopologicalSpace|
   moduliSmoothPointTopology|def moduliSchemePoint' lean/Sheaf lean/WeilConjectures`:
   found `StackPointTopologyFlatLfpOpen` and `SmoothPresentationClosedSubsets`.
   Read both constructions and the residue-field map definitions. They confirm the
   returned duplicate; étale and smooth atlas topologies agree for DM stacks.
6. Repair search `rg -n 'moduliChartPreimage|ModuliPointIsClosed'
   lean/Sheaf/AlgebraicGeometry`: found the existing definitions at
   `DmStackMorphismProperties.lean:113` and `:124`, their uses in that module,
   and the smooth-atlas generated topology. Read their full definitions/docstrings.
   Reused those exact definitions for every topology clause in this delivery.
7. Repair `msearch.py NR lem-sfb-stack-topology-open-substacks grep
   'ModuliPointIsClosed|moduliChartPreimage|moduliPointTopologicalSpace'`:
   `[grep] OK 0 hit(s)` in Mathlib. The same searches in `lean/WeilConjectures`
   and the item-id search there returned no occurrences.
8. Repair name search for `moduliPointIsClosed_compl_iff`,
   `moduliSchemePoint_topology`, `OpenModuliSubstack.pointImage`, and
   `moduliOpenSubstack_pointImage_bijection` in `lean/Sheaf` and
   `lean/WeilConjectures`: no existing declaration in the read clone.
9. Reopened the local Stacks source `stacks-properties.tex`, Tags 04XL and 06FJ,
   including the common-refinement proof and open-substack correspondence. Earlier
   source reading covers 04XF/04XG (field equivalence) and 04XH (pointwise pullback).
   No older blueprint snapshot or external replacement statement was used.

## Return L repaired

The saved packet first passed `deliver2.py --no-push` at `31c26ea7577`. Inspection
showed that it still contained exactly the duplicate topology in return L, so that
mechanical pass was not treated as resolving the independent mathematical finding.

Deleted `moduliPointTopology`, removed it from `lean.declarations`, and removed the
unused `Mathlib.Topology.Order` import. Rewrote its atlas theorem as
`moduliPointIsClosed_compl_iff` using the owning closed predicate and chart preimage.
Rewrote the scheme clause with the canonically characterized equivalence above and
the classification codomain with closed complements. Deleted the smooth-presentation
import and the associated theorem id from `stmt_deps`. No canonical point map has
been copied elsewhere. The statement has not been corrected or weakened.

The common-field quotient theorem, concrete pointImage definition, actual-image and
inclusion clauses of the bijection, and the pullback theorem with its projection-
compatible 2-fibre-product equivalence are retained. Search results above explicitly
record all the overlapping topology constructions and the reused owning definitions.
The delivery wrapper rebases the packet on current main without direct git commands.

## Second reading by NR

The dispatcher forbids starting another agent and assigns independent review to the
maintainer. This is the worker's own second reading with the node and file open.

Checked each base and DM binder, common-field equality, individual atlas criterion,
canonical scheme equivalence and usual-topology test, strictly full open-substack
interface, actual point range, both bijection directions, inclusion preservation,
and the arbitrary morphism pullback predicate, 2-fibre-product equivalence, projection
comparison and point inverse-image equality. The old mismatch was a duplicate
representation of the topology; all topology clauses now use the already cited
closed-set and chart-preimage definitions. The scheme equivalence is forced by its
preimage equation on all subsets, so its existential binder introduces no arbitrary
point identification. All five postponed proofs retain source-based proof docstrings.
No new mathematical mismatch or excluded edge case was found.

Validation (2026-10-24): prescribed `scompile.py` passed with no errors or warnings
in both sandbox mode (30.4 s) and library mode (5.2 s). The repaired dry run printed
`OK (dry run): commit 908aa594fa5 passes the preflight and compiles; nothing pushed`.
The final structural self-check confirms one real definition, five sorry-only
named theorems, exact recorded main signature and declarations, 100-column Lean
lines, no deleted topology references or smooth-presentation import/dependency,
and no node changes outside `lean` and the two authorized definition dependencies.
