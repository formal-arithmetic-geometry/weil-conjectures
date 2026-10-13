## What changed

Proved `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction_exists`
without changing its signature. Added the proof-only import
`Mathlib.AlgebraicGeometry.Pullbacks` and five fully proved private helpers.
The construction uses the ring pushout of `s.α` and `R → R_p`. Mathlib's
`isPullback_SpecMap_pushout` and étale base-change stability prove étaleness.
`SpecToEquivOfField` gives the prime and residue-field map of the pointing to K;
applying the inverse equivalence proves the required evaluation equation.
The prime lies over q by applying Spec to the base-pointing equality and evaluating
at the closed point of Spec K. The pushout universal property supplies every
compatible local morphism, and cocone naturality proves both naturality of the
restricted legs and their compatibility with arbitrary pointed global-to-local maps.
The construction is first proved for an arbitrary compatible base map; hψ and hK
then specialize it to the stated prime localization.

Updated the item's DAG proof, proof dependencies, and proof origin to this route.
The source text was checked at Stacks Tags 04GW and 00U2 (3). The sole mathematical
base-change dependency is the existing Mathlib leaf
`lem-weil-pbc-etale-ring-base-change`; no holed project theorem is used.
The unit record `sk-prop-input-spreading` has no realization of this item as a unit
statement or step, and its route and all unit records are unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction_exists`
(node `new-lem-sbc-etale-triples-prime-localization-cocone-restriction-exists`).
No sorries remain in the item, no holes were added, and no statements were split off.
All private helpers are fully proved. No definition or public interface was changed.
Single-file compilation passed without warnings in 3.2 seconds before packaging.
The delivery dry run supplies the axiom and final preflight checks.

## No longer needed

No imports, existing proof-dependency nodes, or modules were removed: the original
file had only its statement import, and the original node had no proof dependencies.
The original plan's explicit denominator localization, nonzero-denominator lemma,
fraction formula, localization uniqueness calculations, and separate localized
residue-field construction are unnecessary. The pushout and field-point APIs
provide those constructions and equations directly; no new nodes for those tasks
are needed. No pruning of any other item's dependencies is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's first step was non-elementary with no proof dependencies, and its second
step silently required extensions of compatible maps. Both are now fully proved
using Mathlib pushouts. There was no mathematical error: the localization plan
was valid but substantially longer than the base-change construction needed here.
The cocone restriction argument in fact holds for every compatible base ring map,
although the existing public theorem retains exactly its prime-localization signature.

During elaboration, generic `simp` on compositions involving the semireducible ring
diagram could not type-check their objects at implicit transparency. Explicit
associativity calculations and `Category.comp_id` resolve this without changing any
definition, signature, compiler option, or time limit.


## Second reading by U3

1. **Unchanged interfaces — pass.** Read the entire module and its repository
   diff. The existing theorem signature, including R, p, arbitrary field K, χ,
   q, ψ, the A-algebra instance, hψ, hK, V, θ, and the existential compatible-leg
   conclusion, is byte-identical. Its declaration docstring is unchanged.
   The only added import is proof-only `Mathlib.AlgebraicGeometry.Pullbacks`;
   all five added lemmas are private. No definitions or other modules changed.
2. **Proof and construction — pass.** Compiled the delivered module cleanly.
   A scratch copy with `#print axioms` for the public theorem reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There are no sorry tokens or forbidden declarations in the module.
   P is Mathlib's ring pushout, b is its explicit `pushout.desc` map, and the
   pointing is obtained from the proved field-point equivalence. The choice in
   the cocone proof uses a fully proved existence lemma; no data is obtained
   from an unproved existence assertion. Checked the orientation of the Spec
   pullback: étaleness of s.α gives étaleness of the pushout's A-map.
3. **Split statements — pass, none.** No new public statement, node, or hole is
   split off. Read all private helpers: `pointing_over` obtains the prime
   equation by evaluating the equality of Spec maps at the unique closed point
   of Spec K; the base-change helper produces both compatibility equations and
   the local morphism for every compatible β by the pushout universal property.
   These arguments use only Field K, not separable closedness or injectivity
   hypotheses beyond what field maps provide. Identity base change is covered;
   zero base rings admit no specified prime, so their cases are vacuous.
4. **Shortest route and pruning — pass.** Searched the library for base-change
   triples, cocone restrictions, and pushout cocones; inspected Mathlib
   `SpecToEquivOfField`, `isPullback_SpecMap_pushout`, and étale base-change
   stability. Existing similar pointing helpers in `EtaleResidueTriplesFiltered`
   are private and cannot be reused. No existing public theorem supplies the
   full restriction relation. The two imports are needed for the statement and
   the affine pullback proof respectively. The original `proof_deps` was empty,
   so the no-pruning list is complete. Read `sk-prop-input-spreading.realized`:
   the item realizes no fixed unit step, and the unit route is preserved.
5. **DAG and mathematical route — pass.** The only node changes are `proof`,
   `proof_deps`, and `proof_origin`. Its four steps match the Lean: construct
   the pushout triple; extend β and check its pointing by `pushout.hom_ext`;
   use θ.naturality to build η and prove the relation; specialize ℓ using hψ
   and hK. Its sole dependency is the Mathlib base-change leaf
   `lem-weil-pbc-etale-ring-base-change`, whose statement is exactly the property
   used through scheme base-change stability. Read Stacks
   [04GW](https://stacks.math.columbia.edu/tag/04GW) for pointed triples and
   [00U2 (3)](https://stacks.math.columbia.edu/tag/00U2) for arbitrary étale base
   change. The cocone theorem is correctly recorded as an agent-written
   consequence, rather than a verbatim Stacks assertion. The existing leaf's
   source record calls base change item (2); the current source calls it (3),
   as the delivered module already does. This inherited citation typo does
   not affect the leaf statement or this proof.

Second reading changed only this report: added the independent review and the
inherited leaf citation observation. No Lean or node repair was needed.
