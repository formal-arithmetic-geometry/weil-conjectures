# Stage-1 report: def-nagata-sheaf-rees-algebra

## Files written

- dag/nodes/sec-nagata-compactification/def-nagata-sheaf-rees-algebra.json: definition, split into existing dependencies; Mathlib searches find only ring-level Rees algebras and direct-sum algebra structures.
- citations.json: nine verbatim quotation entries for the construction steps.
- searches.jsonl: six actual searches, retained exactly as logged by msearch.py.
- report.md: this report.

New DAG nodes: 0. New Mathlib leaves: 0. No unit record is changed: this is not the unit's key statement.

## Attachments

None. In particular, no renewed ATTACH claim is made. I read the live RelativeProj/Rees.lean: reesData, powMulMap and reesMonomial_mul_reesMonomial provide affine-basis algebra data and affine multiplication formulas. They do not directly construct the categorical direct sum algebra object in sheaves of O_X-modules required by this item. The prior rejected attachment therefore cannot close this item.

## WANTED

None. All sources used are in the read clone.

## Corrections and route

The imported definition named only the associativity lemma. Its module-sheaf coproduct, ideal powers, tensor product, algebra-sheaf notion, and quasi-coherence closure were implicit. I made those dependencies explicit and spelled out the local convolution formula and its algebra laws. The statement retains every original clause, including the direct sum in sheaves, degree-zero unit, grading, quasi-coherence, and absence of an injectivity hypothesis. No statement dispute or weakening is needed. The current main-20261015 blueprint_update was followed; the old import/source fields and bypassed flag are preserved.

The chapter and unit were read. This realizes the unit's instruction to use the Rees algebra before Proj; it changes no blow-up proof route. The generic coproduct description, tensor universal property, and quasi-coherent coproduct closure are declared tool uses in split_report. No lemma about blow-ups is substituted for the unit's route.

## Mathlib and duplicate searches

I searched the project Lean by the blueprint id and Rees terminology, read RelativeProj/Rees.lean lines 137-178 and 200-286, searched the entire DAG by the notions and titles, and ran blueprint_refs.py searches for “Rees”, “sheaf Rees”, “direct sums of quasi”, “coproduct”, and “ideal sheaf powers”, as well as ancestor for the item. “sheaf Rees” finds only this blueprint item. Relevant existing notions/results were reused; no new node is proposed.

The six logged Mathlib searches use two semantic phrasings, Loogle, and two source grep queries. I read all returned hits, RingTheory/ReesAlgebra.lean lines 32-75, and Algebra/DirectSum/Algebra.lean lines 38-58. reesAlgebra is a subalgebra of a polynomial ring; DirectSum.GAlgebra and Submodule.galgebra concern ordinary modules over one ring. Turning either into the requested global sheaf algebra is not a one-line specialization. The source grep for sheaf Rees/graded objects found only freeSection substring hits. The malformed file/line split in the single-file grep result is described in the search record; no Mathlib match or leaf is asserted from it. No searches were invented, and no compilation was run.

## Review by Q141

I checked the definition against the current blueprint file, including the explicit injunction that the direct sum is in sheaves of modules and that multiplication maps need not be injective. I also read Stacks divisors.tex, section-blowing-up / definition-blow-up (Tags 01OF/01OG), which uses the same direct sum of ideal powers. For the construction ingredients I read sites-modules.tex, lemma-limits-colimits (03DB), and its tensor-product bilinear universal property, together with schemes.tex, lemma-colimit-quasi-coherent (01ID). The latter is stated for affine schemes, so the actual node used for general X is the existing global coproduct-closure lemma, whose statement explicitly covers every scheme. I did not apply the affine lemma globally without that cited result.

Step 1 uses def-sbc-ideal-sheaf-powers for the actual ideal powers and their quasi-coherence, def-weil-presheaf-modules-sheafification for module sheafification, and lem-pur-module-sheaf-coproduct-local-support for the explicit sheaf of tuples and its coproduct universal property. I opened and read all three statements. The index is the small set N; the open-set site of a scheme is small after the usual universe choice, its fibre products are intersections, and the sheafification requirement is exactly the one provided by the cited construction. This is an explicit object, not arbitrary data selected from an existence theorem.

Step 2 uses the entire associative/unital multiplication statement of lemma-nagata-sheaf-ideal-powers-assoc, the tuple description from the same coproduct node, the actual bilinear-to-tensor bijection of lem-pc-sites-sheaf-tensor-bilinear-universal, and ideal multiplication from def-sbc-ideal-sheaf-powers. I read each statement and verified each quoted part in citations.json against it. The sum has locally finite support, since a product of finite support sets gives only finitely many degrees. On overlaps the formulas restrict term by term. Associativity is the displayed comparison of the finite triple sums, term by term; the unit comes from degree zero; commutativity follows from the ambient commutative structure ring. These finite-sum calculations are elementary once the cited pairing and coproduct results are available; the universal property is not silently replaced by ring-level tensor algebra. The step is under 2000 characters and hides no independently needed lemma.

Step 3 uses def-sbc-ideal-sheaf-powers and lem-weil-pbc-quasi-coherent-module-coproduct-closure. The latter literally asserts closure for any small family on any scheme, which is precisely the conclusion used. It needs no finite generation, Noetherian, qcqs or flatness assumption. This check corrected the original missing quasi-coherence dependency without manufacturing a new clause-sized lemma.

I checked small cases: the zero ideal gives O_X in degree zero and zero in positive degrees; the unit ideal gives the polynomial-type graded algebra with O_X in every degree; for a square-zero ideal the higher pieces vanish but degree one can remain nonzero, so the construction does not infer injectivity of tensor multiplication. On the empty scheme all sheaves and formulas still make sense. On a non-quasi-compact open sections are only locally finite-support tuples, and the definition does not substitute a sectionwise finite direct sum. These cases test the principal distinction from the rejected affine attachment.

Against delivery-errors B–E: the item is self-contained with cited notions; TeX has single decoded backslashes; no new statement-only node, duplicate, clause relabelling or unsplit proof is introduced; every non-elementary ingredient is cited by its actual statement; citations are verbatim; no citation uses the proof of a node; no SGA source or new route is used. There are no new-node tag pairs to justify and no proof step over 2000 characters. Existing metadata is retained.

## Unfinished work

None within this stage-1 item. The existing dependencies remain their own items or finished nodes; their proofs are not duplicated here.
