## What changed

Replaced `coherentIntegralFiltration_generic_step`'s sorry by a complete compiling
proof, without changing its signature. The proof constructs the reduced integral
closed subscheme of T, identifies its generic point with ξ, uses the already proved
generic ideal inclusion, applies support induction to its coherent cokernel, and
concatenates the two filtrations with the existing extension theorem.

Added `CoherentIdealSumCokernelReduction`, with a complete proof of
`coherent_ideal_sum_cokernel_reduction`: finite-sum and finite-pushforward coherence,
coherent cokernel closure, strict support containment using stalk surjectivity and
local invertibility, and nonvanishing of the ideal using its affine sections.
This lemma only needs a locally Noetherian ambient scheme and a closed immersion;
it needs neither integral source nor a globally monic map.

Added `CoherentIntegralFiltrationIdealSum` for the remaining summand-chain argument.
Added proof-only imports and updated the item's DAG proof and proof dependencies.
All three modules compile together using lcompile.py.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_generic_step`
(node `lem-weil-pbc-coherent-integral-filtration-generic-step`).

Also proved the new
`AlgebraicGeometry.Scheme.Modules.coherent_ideal_sum_cokernel_reduction`
(node `lem-weil-pbc-coherent-ideal-sum-cokernel-reduction`).

Added exactly one hole:
`AlgebraicGeometry.Scheme.Modules.coherentIntegralFiltration_ideal_sum`
(node `lem-weil-pbc-coherent-integral-filtration-ideal-sum`). Its statement has no
support-induction hypothesis, generic point, target module F, or annihilation
hypothesis: it is solely the finite summand filtration of an already specified
ideal pushforward. This delivery is a decomposition, not an unconditional proof
of the original result. Existing dependencies with sorry remain their own items,
including `coherentIntegralFiltration_of_shortExact` and
`RingedSpace.coherent_kernel_cokernel_sum`; this delivery does not modify them.
The delivered modules have no other sorry.

## No longer needed

None. No original imports were removed, and no entire module or node is claimed
as pruned. The original node had no proof dependencies to remove. The reduced
subscheme and restriction arguments reuse proved source-library declarations;
no duplicate geometric construction lemma is introduced.

## Where the brief, the DAG or earlier work was wrong

The original node's proof was a single generic placeholder with empty proof_deps,
although its Lean docstring gave a substantial argument. It now records the
actual inclusion, cokernel reduction, finite-sum filtration, and extension steps.
No statement dispute, interface change, target change, or forced adaptation.

The literature checkout is absent locally; the source was read online at Stacks
Tags 01YF and 01YE. The LeanSearch service returned HTTP 500, recorded as
unavailable, not as a failed mathematical search. LeanFinder, Loogle, Mathlib
rg, source-library rg, DAG search, and blueprint search were also run.

A transient cache refresh briefly removed CoherentIntegralFiltration.olean;
compilation resumed after the prescribed cache restored it. No tool workaround
or modification was used.

Edge cases: the summand-filtration statement includes r=0, requiring the empty
chain and no quotients. For the cokernel lemma, r=0 or I=0 would make the source
stalk zero, contradicting its local isomorphism with a nonzero target stalk.
The support argument proves strictness by the explicit missing point x; it does
not require a nonempty cokernel. An empty ambient scheme cannot satisfy the
nonzero-stalk hypothesis, and an integral closed source cannot map into it.
The unit route remains unchanged.

The previous attempt was blocked by a missing `refuse_missing` delivery-tool
function. That function is now present. The first retry temporarily failed the
Mathlib source inventory, although the prescribed Mathlib source files exist.
The configured source roots subsequently recognized them and the unchanged dry
run advanced. No delivery tool or repository file was edited or bypassed.
This retry recompiled all three sandbox modules successfully (exit code 0).
The prescribed `deliver3.py --no-push` printed OK: compilation and preflight
passed except for the second reading reserved for the next worker. Nothing pushed.

## New nodes

`lem-weil-pbc-coherent-ideal-sum-cokernel-reduction` records the proved geometric
cokernel and ideal-nonvanishing lemma in its own module. Its proof is independent
of the filtration predicate and of support induction.

`lem-weil-pbc-coherent-integral-filtration-ideal-sum` records the sole remaining
hole, with a complete natural-language construction by finite partial summands,
including coherence, quotient identifications, and the zero-summand case.

No change records are needed: all existing statements and definitions are unchanged.


## Second reading by R1

1. **Visible interface: PASS.** Read all three delivered modules and diffed the
   original module and node against the repository. The only existing Lean
   declaration, `coherentIntegralFiltration_generic_step`, has its signature and
   docstring byte for byte unchanged. Its edits are six plain proof imports and
   its proof body. The two other modules and nodes are new. There are no changed
   definitions, public imports of the existing module, or forced adaptations.
   Relevant change records were searched; none changes this interface.

2. **Proof and axioms: PASS as a decomposition.** All three modules compiled in
   import order through `lcompile.py`, without errors or warnings. Scratch copies
   with `#print axioms` for each of the three declarations compiled too: each
   reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is expected: the sole delivered direct hole is
   `coherentIntegralFiltration_ideal_sum`, and the reduction also uses existing
   open dependencies, including coherent closure and filtration extension.
   Neither the original theorem nor the new cokernel theorem is claimed to be
   axiom-free. The source scan found exactly the reported named-theorem hole and
   no forbidden declarations or hollow definitions. In particular, J is the
   actual vanishing ideal and Z its actual reduced subscheme. Existential ideal
   inclusion witnesses are eliminated inside a theorem proof; no data definition
   chooses an arbitrary witness from an unproved existence theorem.

3. **Split statement: PASS.** Read the definitions of the filtration predicate
   and the closed-pushforward ideal module, and read Stacks
   [01YF](https://stacks.math.columbia.edu/tag/01YF) (final paragraph) and
   [01YE](https://stacks.math.columbia.edu/tag/01YE) (inclusion).
   The remaining ideal-sum statement isolates the source filtration alone; it
   has no target F, support induction, generic point, or annihilation hypothesis.
   It is strictly part of the original argument. For r=0 the source is zero and
   the chain has length zero; for r=1 the chain is bottom then top, with quotient
   i_*I; for larger r the partial summands give the stated quotients. Coherence
   and the integral nonzero-ideal witness supply every predicate clause.
   Its complete docstring construction and node are present. Independently
   searched LeanFinder for finite biproduct subobject chains, Loogle for
   Subobject/biproduct, launcher grep for cokernelBiproduct/fromSubtype, and
   repository rg for summand filtrations and the exact filtration predicate.
   Search found useful biproduct components, but no already proved theorem with
   this scheme filtration conclusion. Completing the subobject transport and
   quotient identifications is not a few-minute repair; the honest hole stays.
   The cokernel lemma is also true without a mono or integral-source assumption:
   stalk surjectivity of the cokernel projection gives support containment,
   and local bijectivity at x kills its stalk and proves strictness. I=bottom
   contradicts the nonzero target stalk; r=0 does likewise. Empty support and
   empty ambient schemes cannot satisfy that nonzero-stalk premise.

4. **Route and pruning: PASS.** The proof constructs the integral reduced
   subscheme, identifies its generic point by uniqueness, applies the existing
   inclusion, obtains coherent smaller-support cokernel, invokes support
   induction and the source summand filtration, and concatenates via the
   existing short-exact extension theorem. Every added proof import supplies
   a used theorem or construction; public imports supply signature vocabulary.
   No shorter ready-made scheme filtration theorem was found. The original
   node had empty proof_deps, so the report's `No longer needed: None` is
   complete. Read `dag/units/sk-thm-p1.json`, including all `realized` entries:
   this is a lower-level coherent-sheaf reduction, not a replacement of a unit
   realization or its curve/PBC route; all those entries remain unchanged.

5. **DAG: PASS.** The original node changed only its proof, proof_deps and
   proof_origin. Its four steps match the actual reduced-subscheme construction,
   inclusion, cokernel/source filtration reduction, and extension application.
   Each new node has the required source, self-contained statement, dependency
   lists, searches, blueprint ancestry, creation and verbatim Lean record.
   The cokernel node cites precisely coherent closure, finite pushforward and
   stalk exactness used in its proof; the summand node records the complete
   construction still to formalize. No statement change record is needed.

**Second-reader changes:** appended this independent review and fresh search
records to the two new nodes. No Lean proof or statement needed repair. Removed
all temporary axiom-probe source copies before delivery. The one closed original
hole and one added lower hole remain a decomposition with net zero direct holes;
no module is claimed pruned.
