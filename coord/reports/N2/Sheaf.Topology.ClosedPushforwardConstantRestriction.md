## What changed
Replaced the original sorry of `TopCat.closed_pushforward_constant_restriction` by a
reduction to the existing `TopCat.inverse_image_closed_pushforward_constant` theorem.
The proof transports its comparison through Mathlib `TopCat.Sheaf.pullbackIso`, proves
adjunction-unit compatibility using `Adjunction.unit_leftAdjointUniq_hom_app`, and builds
an explicit equivalence of locally constant maps on the two intersection subtypes.
The existing signature and all original public imports are unchanged. Added two plain
proof imports: `Sheaf.Topology.InverseImageClosedPushforwardConstant` and
`Sheaf.Topology.ClosedPushforwardConstantPresheaf`.

## Proved and sorry left
`TopCat.closed_pushforward_constant_restriction` has no remaining sorry. The delivery
contains one module and proves its one originally open theorem, adds no declarations
and no split-off statements. Its imported existing inverse-image theorem is still open;
therefore the target's axiom closure still includes `sorryAx`, and this is a reduction,
not a claim of complete closure under the three allowed axioms.

## No longer needed
Removed the proposed new core module and node, which merely restated the item using a
bijective function instead of an equivalence. Restored the original public imports and
removed the now-obsolete import change record. No existing module is asserted globally
pruned. Every old direct proof dependency is replaced in this node's proof record:
`def-weil-pbc-topological-inverse-image`, `def-weil-pbc-category-colimit`,
`lem-weil-pbc-filtered-colimit-sets-elementwise`, `def-weil-pbc-sheafification`,
`lem-weil-pbc-sets-inverse-image-stalk`, and
`lem-weil-pbc-sheaf-sections-determined-by-germs`. Their relevant mathematical content
is handled by the existing inverse-image theorem or Mathlib's sheaf pullback comparison;
they may remain transitively needed elsewhere. The new direct dependencies are the
existing inverse-image theorem node and section-presheaf definition node.

## Where the brief, the DAG or earlier work was wrong
The first worker and the previous review claimed that a bijective function is a strictly
weaker substatement than an equivalence. These formulations are interchangeable by
`Equiv.ofBijective`; the core transferred the entire unproved item to a new sorry and
was not progress. The prior second-reading pass verdict (including my initial appended
pass before noticing this fault) was incorrect and is superseded by this report.
A real reduction was available in the library's inverse-image theorem. No existing
statement or definition was changed. No change record is needed.

## Second reading by N2
1. Compared the final delivered module with the repository using diff. The existing
   theorem signature and docstring are byte-for-byte unchanged, as are its original
   public imports. Only its proof and two plain proof imports changed. Verdict: pass.
2. Compiled the final module locally through lcompile.py, checked for forbidden
   constructs and direct sorries, and probed its axioms. The proof has no direct sorry;
   axioms are propext, Classical.choice, Quot.sound, and sorryAx from the already open
   imported inverse-image theorem. No new axiom or definition is introduced. Verdict: pass
   as a reduction to an existing open statement.
3. Rejected and removed the equivalent core restatement. There are no new or split-off
   statements in the final delivery. Checked empty Z, empty Z', empty S, and Z'=X:
   all transports are subtype comaps, impose no inhabitance, and the general inverse-image
   theorem applies without extra hypotheses. Searches via leanfinder, loogle, grep, and rg
   found the relevant existing library theorem and Mathlib comparison/unit declarations.
   Verdict: pass.
4. Read the proof top downward. It uses the existing general theorem, then supplies the
   explicit sheafification/unit and subtype transports needed by this exact statement.
   Both added imports are plain proof imports, with no core module public re-export.
   All six replaced old direct dependencies are listed above. Unit sk-thm-p1's realized
   statement/step nodes are untouched; this is a reduction below the unit level. Verdict: pass.
5. Synchronized the existing node's proof, proof_deps and proof_origin with the final Lean
   proof. The existing section-presheaf definition and inverse-image nodes have the exact
   declarations used; no new nodes remain. Verdict: pass.

Second reading changed the proof completely to remove the circular-in-substance core
reduction, deleted the duplicate core module/node and import change record, restored
public imports, and corrected the report and target-node proof route.
