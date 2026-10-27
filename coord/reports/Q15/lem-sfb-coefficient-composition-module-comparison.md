# Worker report: lem-sfb-coefficient-composition-module-comparison

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-coefficient-composition-module-comparison.json`: statement, split into five steps; not a Mathlib leaf as a whole. Statement and statement dependencies preserved.
- `citations.json`: one verbatim statement quotation for each of the nine step/node citation pairs.
- No new nodes, hence zero new Mathlib leaves. `searches.jsonl` records the actual Q15 searches; the item's earlier NA search records were retained.

## Attachments

None. Searched the live project under `lean/WeilConjectures/` for the blueprint tag and for `mapMod`, `mapModCompIso`, restriction and conjugation. `CategoryTheory.Functor.mapModCompIso` in `CategoryTheory/ModuleObjects/MapMod.lean:327` gives a related comparison with coefficient monoid `QP(A)` and restriction along `c_A`, rather than the item's arbitrary `B,C,psi,chi,phi`, and does not state the normalized adjoint clauses. It does not attach to this whole item. The generic module constructors are also only portions, so the item is split.

## WANTED

None.

## Corrections and scope

The item had no proof. I kept its statement, including the assumption that every forward component is already C-linear. The coefficient factorization and monoid-morphism hypotheses are retained; no inversion of coefficient maps is introduced. Forward linearity is not re-proved using monoidality, because this item expressly assumes it. Its parent handles the forward action calculation separately.

The unit and chapter records were read. The item is not the unit's key statement, so no unit realization fields were edited. The route remains the unit's prescribed lifting of the pushforward comparison followed by uniqueness of left adjoints. The only result imported from another unit is the existing Mathlib leaf `lem-weil-pbc-conjugate-iso-unit-equation`, which is a generic tool by the project's route rule; no off-route non-Mathlib theorem is used.

The source paragraph is the current main-20261015 blueprint's `sk-def-sfb-module-pushforward-pullback.proof.md`, with the two detailed lower-star-comp and upper-star-comp statements. The source does not spell out the abstract conditional proof. I supplied those calculations and marked the proof as agent-written, using the existing mate-calculus nodes and their verified Stacks/Mathlib sources. No statement dispute was found in this item. In particular, the equation has the correctly typed direction `d:S_H -> S_PS_Q` conjugate to `delta:T_QT_P -> T_H`; the supplied adjunctions, rather than any newly chosen adjunction, determine the units.

## Searches and reuse

Before considering a new node I searched all DAG statements and titles for conjugation, uniqueness of adjoints, mates and module comparisons; the existing `lem-weil-pbc-conjugate-iso-unit-equation` states exactly the normalized unit characterization needed. Read its entire statement, source and Mathlib match. Whole-blueprint searches with `tools/blueprint_refs.py` used `composition module`, `conjugate`, `restricted`, `mapMod`, and `left adjoints`, and the ancestor query confirmed `sk-def-sfb-module-pushforward-pullback`. The geometric module-composition nodes and coefficient-square nodes are specializations or different squares, not the whole conditional item, so `blueprint.same_as` remains empty. No new node was needed.

Q15 ran LeanFinder, LeanSearch, Loogle and source grep through msearch.py, then a second semantic phrasing and a more focused Loogle search. The ordinary ModuleCat restriction results concern modules over ordinary rings; the internal-module constructor hits cover the elementary inverse/linear-map portion. `CategoryTheory.conjugateIsoEquiv` covers generic conjugation, already represented by existing DAG leaves. Read the pinned Mathlib Mates.lean:275–315 and 400–439, and Mod.lean:260–321, rather than treating semantic names from a differently named Mod_ version as the pinned library. The item is not a one-line specialization of those results: its action formulas and lifting to the internal module functors are still explicitly proved.

## Not duplicates

No new nodes. The existing generic adjoint comparison leaf is reused, not recreated; neither an elementary inverse calculation nor a clause of the item has been moved into a new node.

## Review by Q15

I read delivery-errors B–E in full and checked the proof with each cited statement open. For the item I read the current blueprint unit/chapter and the pushforward/pullback composition source files, then the transport and restriction source files. For mate calculus I read Stacks Tag 0B65, `categories.tex`, label `lemma-transformation-between-functors-and-adjoints` (the Hom-set characterization and counit diagram), and the local Mathlib unit-conjugation and conjugate-isomorphism declarations. There are no new nodes whose sources require a separate review.

Step 1 uses precisely the action and map assignments stated by `def-sfb-modobj-transport` and `def-sfb-modobj-restriction`. The three coefficient maps have the right domains and are monoid morphisms, so restriction is defined. In the second transport, `T_PM` is a B-module, which is why the outer tensor map has indices B and PM. This verifies the displayed a_M rather than silently replacing B by PA. This step is only substitution into the cited formulas.

Step 2 uses the tensor bifunctor laws from `def-sfb-monoidal-category` and the module-map action equation from `sk-def-sfb-module-objects`. Composing by the two inverses gives the displayed inverse linearity equation with domain C tensor HM. Only c_M and its tensor with the identity are inverted. The identity module composites follow from equality of underlying maps, which is immediate from the module-map definition. This is an elementary calculation, not a new lemma.

Step 3 uses the same module-map definition to reflect equality of maps. Naturality of c is a hypothesis of the item, and applies to every underlying A-linear morphism t. The underlying functor assignments were established in step 1; multiplying that equation by c_N inverse and c_M inverse checks inverse naturality explicitly. Thus the components form an isomorphism of module functors and determine it uniquely. No claim of fullness of a forgetful functor is used.

Step 4 uses `def-weil-pbc-composite-adjunction` for the actual composite adjunction and its unit, and `lem-weil-pbc-conjugate-iso-unit-equation` for existence, isomorphism and uniqueness. Its statement explicitly gives R1(d) eta1 = delta eta2, not merely uniqueness for an identical right adjoint. I checked all four functor substitutions, the two module categories, and the R2-to-R1 direction of delta. The hypotheses are the given adjunctions and step 3's natural isomorphism, with no coefficient equivalence or finiteness assumption.

Step 5 uses the component formula and inverse clause in `def-weil-pbc-adjunction-conjugate` and the adjunction of `def-weil-pbc-composite-adjunction`. Substituting the established unit equation at R2N and moving delta past the counit by naturality leaves the right-adjoint triangle identity. All maps have source R2N and target R1N. This supplies an explicit identification of the mate, rather than simply declaring it canonical. The inverse statement is exactly the cited inverse clause.

Edge cases checked: identity ambient functors and coefficient maps give the identity lifted comparison; the unit normalization still selects the comparison for the specified adjunction structures even when adjunction structures differ. Arbitrary noninvertible coefficient maps in ordinary rings (for example Z -> Z/2 for the first restriction, then identity restriction) are allowed: the identity underlying comparison stays linear after the same restrictions. Zero modules cause no cancellation problem since cancellation uses actual isomorphisms, not nonzero elements. Noncommutative monoid objects require no symmetry or commutation; the inverse calculation uses only the functor C tensor (-). No size-dependent colimit or existence theorem is hidden in the proof.

For B–E specifically: no new-node form, duplicate, or whole-clause relabelling issue occurs; every non-elementary input is the statement of the cited existing leaf, and no proof of another node is being used. The action, inverse, naturality and mate formulas were checked against their actual objects. All five steps are under 2000 characters (the longest is 902), and their elementary calculations are written explicitly. The statement, source and maintainer-owned metadata were retained. citations.json records the actual statement text for every citation. No Lean source or repository file was changed, and no compiler was run.

## Unfinished work

None in the requested one-level split. Validation and direct delivery are performed with the required deliver.py dry run and push.
