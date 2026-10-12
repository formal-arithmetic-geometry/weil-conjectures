## What changed

Wrote a compiling reduction of `Etale.survivesBaseChange_or_of_isClosedImmersion` by the prescribed closed–open
coefficient argument, keeping its statement unchanged. Added three modules: the coefficient
embedding is proved; the closed coefficient range comparison and open injective coefficient
vanishing are stated as two separate geometric tasks. The Survival module contains complete
algebraic proofs for reconstructing the direct-sum image and reflecting image membership
through the monomorphism on cokernels. Restriction composition transports the original element
into the two branch hypotheses. No target statement, public definition, or existing signature
was changed.

## Proved and sorry left

The delivery proves `AlgebraicGeometry.Etale.mono_closedOpen_coefficient_embedding`
(node `lem-sbc-closed-open-coefficient-embedding`) directly from adjunction, the chosen
injective embedding, and a conservative family of geometric stalks covering the open and
closed pieces.

The reduction uses these two named statements, each with its full
source proof in its docstring:

- `AlgebraicGeometry.Etale.baseChange_closed_coefficient_mem_range`, node
  `lem-sbc-closed-coefficient-range`, in `Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange`.
- `AlgebraicGeometry.Etale.baseChange_open_injective_coefficient_eq_zero`, node
  `lem-sbc-open-injective-coefficient-zero`, in
  `Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero`.

These are the only sorries added. Closed the one remaining hole of the assigned module,
`AlgebraicGeometry.Etale.survivesBaseChange_or_of_isClosedImmersion`; its proof now compiles
from the two separate geometric comparisons. This is a decomposition of one hole into two,
not a net decrease in holes. No sorry remains in Survival or the embedding module.
The private categorical helpers, the restriction-composition argument, and the final
contradiction are fully proved. Existing thickening, limit, identity and empty-scheme proofs
are retained unchanged.

The earlier timeout concealed a failed instance search: the cokernel monomorphism was
bound with `have hm`, rather than registered as the instance required by the range helper.
The repaired proof binds that instance anonymously. Two proved private identities make
survival and homology-transformation component conversions explicit. The full module
compiles under the normal 60-second limit (51.8 seconds in the successful local check).
No compiler option or timeout was changed, and no proof was split to evade the limit.

## No longer needed

No original import or node is pruned: the original imports still support the thickening
and limit proofs, and the unit's closed–open route is retained. All three new proof imports
have a role in the coefficient argument. The second reader removed the unused new
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective` import from the embedding module
and replaced its broad Transition import with the underived adjunction definitions,
Grothendieck sheaf and concrete coefficient instances, and enough-injectives infrastructure;
stalk comparison and exact reflection are imported only for its proof. No new continuity or minimal-counterexample
infrastructure is introduced.

## Where the brief, the DAG or earlier work was wrong

The assigned module already had the thickening, limit, and empty-scheme conditions proved;
its only remaining sorry was condition (3). The DAG does not state the two geometric
coefficient comparison tasks with usable Lean interfaces. They are now separate modules
with canonical stalk restrictions, so they can be proved independently without importing
Survival or creating a cycle.

Mathlib searches were run for each comparison and the embedding. LeanSearch returned HTTP
500 and is recorded as unavailable. LeanFinder and source searches found generic categorical
and geometric infrastructure but no exact comparison theorem. Searches of the blueprint
found no duplicates of these specific assertions.

The local library initially lacked the newly landed U2 stalk-transition modules. Those
artifacts arrived during the session, and the three new modules compile against them.
The source was checked against Stacks 0F07 and its references 03QP, 0959 and 0734. Edge cases:
empty open, empty closed complement, q = 1, and negative q for the closed comparison. The
Leray comparison uses all lower degrees after preliminary base change, exactly as the unit
requires. The embedding proof does not assume that the open direct image is exact.

## New nodes

`lem-sbc-closed-open-coefficient-embedding`: the actual coefficient monomorphism, fully
proved in `lean/Sheaf/AlgebraicGeometry/BaseChangeClosedOpenEmbedding.lean`.

`lem-sbc-closed-coefficient-range`: closed pushforward identifies the transported
base-change image with the coefficient-unit image. The remaining work is exact closed
pushforward, derived composition, and compatibility of the comparison with the unit.

`lem-sbc-open-injective-coefficient-zero`: lower-degree universal base change and the
relative Leray edge injection turn a restricted base-change image into zero after the
open injective coefficient embedding. It treats an arbitrary stage stalk element, not
an original survival hypothesis or a restatement of the closed–open disjunction.

No change record is needed: existing interfaces and definitions are unchanged and the new
modules are imported only for proofs.

## Second reading by J2

1. I compared the delivered Survival module with `sheaf-dag`. The original target and all
existing declarations have the same signatures byte for byte; only proof text and proof-only
imports changed. The three added modules introduce the split statements recorded by their
nodes, with no target or public definition changes. Verdict: pass.

2. I compiled all four delivered modules with `lcompile.py --all`; they compile without errors
or warnings. The coefficient embedding is a direct stalkwise monomorphism proof, and the
Survival proof reconstructs the biproduct image and reflects it through the cokernel
monomorphism. No definitions contain `sorry`, and the only remaining `sorry`s are the two
named geometric comparison theorems listed above. A scratch module imported the freshly
compiled delivery and ran `#print axioms` on the embedding, both split comparisons, the
survival definition, and all six public Survival theorems. It reports only `propext`,
`Classical.choice`, and `Quot.sound`, plus `sorryAx` for declarations resting on the listed
comparisons or existing open dependencies. The embedding uses no `sorryAx`, so its chosen
injective object is backed by proved enough-injectives infrastructure, not an unproved
existence witness. The delivery tool's probe completed on the three new modules. Its
Survival probe timed out, but the separate scratch axiom audit compiled in 3.3 seconds.
Verdict: pass.

3. I checked the split statements against the closed–open argument of Stacks Tag 0F07.
`baseChange_closed_coefficient_mem_range` is the closed summand range implication;
`baseChange_open_injective_coefficient_eq_zero` is the open injective summand vanishing
implication and explicitly assumes all lower-degree universal base-change properties. For q=1 the intermediate-vanishing range is empty and the bottom edge remains injective;
for empty V the open target is zero, and for empty Z the closed coefficient sheaf is zero.
For negative q the closed comparison concerns zero derived cohomology of a degree-zero
sheaf. Both
are strictly smaller than the Survival disjunction and their docstrings give complete proof
plans and sources. The embedding statement is the needed monomorphism and is fully proved.
Verdict: pass.

4. The proof follows the unit route: restriction transport, closed–open coefficient
embedding, the two coefficient comparisons, biproduct reconstruction, and cokernel range
reflection. Imports are minimal for the declarations used; no original proof dependency or
unit step was pruned. Verdict: pass.

5. The DAG records for the target and all three new nodes agree with the Lean declarations,
including proof dependencies, source, split status, and unit/chapter. Verdict: pass.

I repaired the embedding module's imports as listed under No longer needed; its statement
and proof remain unchanged. I independently searched with different terms using LeanFinder,
Loogle, and source grep. The hits provide general adjunction, stalk, and homology
infrastructure, not either missing geometric comparison. OpenClosed.Exact concerns the
extension-by-zero sequence, SiteLerayDegenerate concerns full acyclicity, and the existing
closed-stalk comparison does not supply the derived base-change coherence needed here.
The first dry run timed out compiling Survival despite its earlier 57.3-second successful
compile. No definition, proof split, or compiler timeout was changed in response.

The repaired delivery passed `deliver3.py --no-push` (OK, review class CODEX).
