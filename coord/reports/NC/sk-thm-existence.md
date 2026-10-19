# Stage-1 report: sk-thm-existence

## Files written

- `dag/nodes/sec-six-functors-basics/sk-thm-existence.json`: retained statement, repaired five-step split; zero new nodes and zero Mathlib leaves.
- `report.md`: retained initial findings, corrected review and explicit landing-return repair.
- `citations.json`: eleven complete, verbatim current-node statement quotations, one for every citation in the five steps (local delivery evidence).
- `searches.jsonl`: actual Mathlib search records, retained as local evidence; the item's searches contain exactly these queries and results.

## Attachments

None. The earlier attachment search found no exact declaration. I rechecked `WeilConjectures/` in the read-only slopmaster2 checkout for the exact tag `sk-thm-existence` and for exceptional-inverse-image notions. `SixFunctors/ProEtale/ExceptionalAdjoint.lean:151` states an ambient left-adjoint result under an extra uniform-cohomological-dimension datum and has `sorry` at line 153. It neither supplies this theorem nor justifies an attachment. The integral, finite and field localizing-category clauses must all remain in the DAG split.

## WANTED

None.

## Initial findings retained

The imported proof omitted the integral restriction citation from its dependency list and mentioned several compactness results without putting them in `uses`. The earlier delivery repaired that by citing existing statements for compact generation, existence and the three coefficient restriction cases. Its theorem statement was retained exactly, including arbitrary finite rings and the integral/rational consequences. This repair retains that statement and those citations rather than restarting the split.

## Landing return repaired

The return says: `NOT MERGED sk-thm-existence: fix dag/units/sk-thm-existence.json: not a file of the delivery (a fix only adds a NEW statement node; it never touches another node)` and asks for rebasing against the current DAG and rereading changed citations.

The retained sandbox already has no `dag/units/` file. I keep that exclusion explicit: this delivery contains only the item's node and its report; it does not submit a unit-record fix, alter unit metadata, or change any other existing node. Unit realization bookkeeping belongs to maintenance if still required. The required initial dry run passed at `18271831d8`; I did not treat that success as a repair by itself. I reread all six previously cited statements against the retained quotations: those quotations still match the current statements. The current item remains imported, and the retained statement agrees byte for byte with it. The delivery command constructs the repaired commit on the current server DAG automatically.

The substantive repair also closes gaps found during that rereading. The old step 1 did not cite a statement supplying lower-shriek preservation of `Dctf`, and did not name compactification comparison coherence. The old step 2 wrongly said the integral and field restriction statements themselves assert `Dctf=Dbc`; they do not. It also left implicit the identification of the integral right adjoint. The five revised steps cite the existing statements that actually provide those facts. The report and quotation evidence are updated accordingly, so this is not an unchanged re-push.

## Review by NC

I read the current item, its chapter and unit records, and the main-20261015 sources `_section.md`, `sk-thm-existence.proof.md`, `det-existence-localizing.proof.md` and `det-existence-restriction.proof.md`. The statement agrees with the unit clause by clause, and the repaired proof keeps the unit's compactness, compactification, Brown and geometric-restriction route. It invokes the existing geometric preservation theorem rather than introducing an alternative purity argument. No forbidden SGA source is used. Since these blueprint proofs are agent-written, I corrected `proof_origin.by` to `agent`.

For step 1 I opened `sk-lem-brown-hypotheses`: its statement supplies compactness of every object, essential smallness, and generation by any small skeleton for every listed coefficient. Its standing field and separated finite-type hypotheses match the item; it is not being used as a mere definition of compactness.

For step 2 I opened `lem-weil-pbc-qcqs-over-affine`, `sk-thm-nagata-compactification`, `det-sf-comp-coherence-single` and `det-sf-comp-coherence-cocycle`. The first explicitly includes separated finite-type schemes over a field, so it verifies qcqs for both schemes before Nagata and before the other two applications. The single-compactification statement explicitly supplies exactness, sums and preservation of `Dctf`; the cocycle statement supplies comparison independence and coherence. I read the two compactification lemma source files and the Stacks `schemes.tex` passages `lemma-quasi-compact-affine` (01K4), `definition-separated` (01KK), `lemma-affine-separated` (01KN) and `lemma-separated-permanence` (01KU) supporting the qcqs lemma. These are assertions of the cited nodes, not facts inferred from their proofs.

For step 3 I reread `sk-prop-sf-existence`. It gives the exact right adjoint and natural Hom bijections for the same chosen compactification, ordinary ambient localizing closures and module-object coefficients. The preceding steps establish exactly its compact-generation and compact-support inputs. No second integral Brown application is inserted.

For step 4 I reread `sk-prop-sf-rf-shriek-preservation`, `sk-thm-int-restriction` and `sk-thm-restriction`, and additionally opened `det-prop-int-brown-adjoint` and its main-20261015 source. The finite theorem explicitly uses the general existence adjoint in the identified module-object categories and covers any finite commutative ring killed by a power of ell. The integral identification theorem explicitly identifies its adjoint with the integral instance of the general one, so the integral restriction theorem now applies to the correct functor. The field theorem also explicitly refers to that general adjoint. Taking E=Q_l covers both Z_l and Q_l. Each cited restriction statement includes the restricted adjunction.

For step 5 I opened `det-def-localizing-closure-ctf-equals-bc` and its source in `sec-proetale-coefficients/sk-def-localizing-closure/`. Part (2) gives both the equality of full categories and equality of their localizing closures for exactly the five non-finite coefficients. Its qcqs hypothesis was verified in step 2. Hence this step proves the final Dbc consequences without claiming that a restriction theorem asserted those equalities. No finite-ring equality is used.

The qcqs lemma and coefficient-category equality are generic tools from other units, used only to verify hypotheses and interpret the final categories. The integral-adjoint identification is explicitly required by `det-existence-restriction.proof.md`. The compactification lemmas implement exactly `det-existence-localizing.proof.md` clause (2), whose umbrella imported references no longer exist as node files. I request that maintenance record tool uses if its route check requires them; I have not set maintainer-owned `tool_uses` fields.

The B--E audit creates no new statement, elementary placeholder, duplicate or clause-restating child. All uses are existing statements; all eleven quotations are verbatim. Step lengths are 334, 936, 509, 824 and 507 characters, so none hides a long inline lemma. The identity and empty-source cases give identity and zero adjunctions respectively. For finite nonregular coefficients, F_l over Z/l^2 is not assumed to have finite Tor amplitude, while the perfect two-term complex [A --ell--> A] remains admissible; this checks that no accidental Dctf=Dbc claim or regularity assumption entered the finite case. The E=Q_l specializations cover the stated integral/rational boundary cases.

No completed search log existed in the retained sandbox before this repair. I ran and read two semantic phrasings, LeanSearch, Loogle and two source-grep searches with the required msearch command. Loogle finds categorical right-adjoint exactness, whose source at `Mathlib/CategoryTheory/Triangulated/Adjunction.lean:60` assumes the adjunction; it does not prove this complete geometric theorem. The semantic hits concern ordinary module pushforwards, t-structure bounds or unrelated exactness, and the grep hits are author-name coincidences. None gives the item as a Mathlib leaf. Every query and actual result is recorded; no unavailable service is described as absence.

## What could not be finished

Nothing in the split. No Lean files were written and no compiler, Lake or build tool was run.
