## Worker report

Q42 split `lem-sfb-polynomial-adequacy-nil-base-change` at stage 1. The statement and its statement dependencies are unchanged. The four-step proof uses existing nodes throughout; there are no new nodes or Mathlib leaves in this delivery.

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-adequacy-nil-base-change.json`: item, status split, four proof steps, actual additional Mathlib searches, blueprint comparison and one generic tool use.
- `citations.json`: eight entries, one for each step/node occurrence, with verbatim text from the cited statement.
- `report.md`: this report and signed review. `searches.jsonl` is the search command's original log.

Attachments: none. Searches of `lean/WeilConjectures/` for the exact blueprint tag, adequacy, polynomial power lifting and nil kernels found no declaration stating the item. The unrelated formal-polynomial, purely inseparable and nilpotent coefficient results do not give its arbitrary-ring hypotheses and both conclusions. No Lean was written or compiled.

WANTED: Jarod Alper, *Adequate moduli spaces and geometrically reductive group schemes*, local file `literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf`, Remark 3.2.2 (printed p.496), Lemma 3.1.4 (p.495), and the spectral argument of Proposition 3.3.5 (p.498), for `lem-sfb-polynomial-adequacy-nil-base-change`. The local PDF is absent. I read the [published primary PDF](https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf) online. The proof is marked agent-written: it expands that calculation and assembles the locally available Stacks statements.

What needed work: the imported item was statement-only. Its description of the conclusion is correct. In particular the full adequate-homeomorphism equivalence in Alper Proposition 3.3.5 has an extra rational-kernel condition; I do not apply that equivalence to this item. The proof only needs the single-map spectral conclusion, stability of spectral surjectivity, and polynomial evaluation. No statement correction or dispute is needed.

Nothing remains unfinished in this split. All newly written proof steps are shorter than 2000 characters; the entire assembly is shorter than 3000 characters. Validation and delivery use the prescribed server tools.

## New nodes

None. No auxiliary claim is moved out of the item's proof.

## Existing-node and blueprint searches

I read `coord/brief-stage1.md`, stages/1-dag.md, delivery-errors B--E, the three-level rules in SETUP.md, GOAL.md, the chapter and unit records, and the latest blueprint unit and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The current blueprint pointer records main commit `7284bb09daf97437d544c51882b325f9c52cd345`. This is a commutative-algebra prerequisite below the inherited adequate-comparison chain; I changed no unit or chapter. The ancestor command reports the existing null blueprint ancestor, which is preserved rather than rewriting a maintainer-owned ancestry field. The exact supporting place remains specified in the inherited `blueprint.from.place`, and split_report explains the four steps' roles.

`tools/blueprint_refs.py search` for `integral surjective`, `power lifting`, `polynomial`, and `adequate`, together with whole-DAG statement/key-word searches, found the existing spectral and tensor inputs. No imported blueprint statement gives this item. I opened the statements of all six cited nodes. The neighboring `lem-sfb-polynomial-power-lifting-universal-homeomorphism` assumes injectivity and concludes a universal spectral homeomorphism; it does not assert this item's universal elementwise power-lifting conclusion, and its injectivity hypothesis is absent here. I therefore use the foundational nodes directly, leaving the actual calculation in this item's proof. No duplicate is introduced.

## Mathlib searches

The item's prior search records are retained. Five additional queries are recorded verbatim from Q42's searches.jsonl: LeanFinder with two different descriptions of the polynomial-to-arbitrary-base-change criterion, Loogle with `"TensorProduct", "IsNilpotent"`, grep with the adequacy/IsPRadical/power-lifting/homeomorphism patterns, and LeanSearch with a polynomial power-lifting description. All five services returned results successfully; Loogle returned zero hits. The full query text and actual logged top hits are in mathlib_searches.

I read `Mathlib/RingTheory/Spectrum/Prime/Homeomorph.lean:39`: `PrimeSpectrum.isHomeomorph_comap` proves the single-map spectral conclusion and is already the match of `lem-pur-all-element-powers-spectrum-homeomorphism`. Its purely inseparable tensor corollary assumes a field extension. The other power-lifting hits likewise assume fields or a prime-power radical property in fixed characteristic. Polynomial-law lift results present an element over a finite polynomial algebra; they do not establish power lifting from the item's hypotheses or its nil-kernel conclusion. The map_pow/evaluation identities are elementary parts of the calculation. None states the complete item or specializes to it in one line, so the item is split, not a Mathlib leaf. No unrun search is recorded.

## Tool use

`lem-weil-pbc-spec-surjective-base-change` is an existing, reviewed generic ring-theoretic tool from `sk-thm-p1`. Its statement is precisely stability of spectral surjectivity under arbitrary scalar extension, with no finiteness or flatness assumption. It supplies step 2 and does not replace the unit's geometric argument. This is declared in `split_report.tool_uses`; no top-level maintainer-owned tool_uses was written.

## Review by Q42

I reviewed the actual node statements against Stacks `algebra.tex` labels `lemma-powers` (0BR8), `lemma-surjective-spec-radical-ideal` (00FI), and `lemma-Zariski-topology` (00E0, especially item (7)). For the polynomial argument I read Alper Remark 3.2.2 online and the tensor and polynomial definition nodes themselves. The published remark asserts exactly the polynomial-test criterion; its compressed argument is expanded here by a finite sum and two evaluations. There are no new nodes whose source or hypotheses need a separate review.

Step 1 uses `def-weil-pbc-mv-polynomial-ring` for zero variables: its finite monomial construction with empty variable set has only constant monomials. The hypothesis at n=0 is therefore the all-elements positive-power hypothesis of `lem-pur-all-element-powers-spectrum-homeomorphism`. I checked that this existing node accepts a noninjective commutative ring map and an elementwise nil kernel, exactly what is assumed here. Its conclusion gives spectral surjectivity; no part of its proof is borrowed.

Step 2 uses clause (1) of `lem-weil-pbc-algebra-tensor-pushout-universal-property` for the multiplication, unit, and left/right algebra maps on D. Its statement explicitly supplies those maps, so no ring structure is inferred from a mere module definition. I checked `lem-weil-pbc-spec-surjective-base-change` word for word: it assumes only the already obtained spectral surjectivity and applies to every ring map R to E. Thus E need not be finite type, flat, Noetherian, or reduced. This is the only off-unit nonleaf tool use.

Step 3 uses the exact radical-intersection formula in `lem-weil-pbc-zero-locus-eq-iff-radical-eq`. A prime of D over a given prime of E comes from the preceding step. Every element killed by g belongs to that contracted prime, hence to every prime of E. Specializing the stated formula to the zero ideal proves an individual positive power is zero. The exponent is allowed to depend on the element; no claim that the entire kernel ideal is nilpotent occurs.

Step 4 uses the generation assertion of `def-weil-pbc-module-tensor-product`, the evaluation and uniqueness assertions of `def-weil-pbc-mv-polynomial-ring`, and multiplication and algebra maps from clause (1) of the tensor-pushout node. Each of these appears in the cited statement, not merely its proof. Absorbing a scalar into e_i is tensor balancing. The one polynomial b=sum s_i t_i captures the whole finite tensor sum, so there is no invalid claim that separately lifted powers of summands suffice. The evaluation sends b to z by the displayed multiplication formula. On each coefficient r the identity 1 tensor u(r) = r_E tensor 1 proves that evaluating u_m(a) equals g evaluated on a; the two polynomial maps also agree on every variable, so the cited uniqueness assertion applies. The resulting equality z^N=g(a(e_1,...,e_m)) proves the whole second clause. This step is elementary substitution from those cited statements and the item's hypothesis; it hides no independent comparison lemma.

I checked the small cases explicitly. With no variables, step 1 is precisely the original map. For an empty tensor sum choose exponent 1 and lift 0. For E=0 every element is zero, so both conclusions hold; the empty prime-intersection formula is consistent with the zero ring. If S=0, the hypothesis forces 1_R to be nilpotent and hence R=0, so no exceptional nonzero algebra is overlooked. For a surjection R to R/I with a nil ideal, every polynomial already lifts with exponent 1, and every extension has kernel IE, elementwise nil; this agrees with the argument. The example Q[epsilon]/(epsilon^2) to Q, with E=R, has a nonzero rational kernel and satisfies the hypotheses, verifying why the omitted characteristic-zero clause must not be imported. Finally R=Q[x_i : i>=1]/(x_i^2) to Q tests a nil kernel with no uniform nilpotence exponent: each element involves finitely many generators, but arbitrarily long products of distinct generators survive. The proof only uses individual nilpotence and remains valid.

I checked B--E against the files: every non-elementary input is an existing cited statement; each of the eight citation quotes is a literal substring of that statement; all proof uses are in proof_deps; no new definition, duplicate node, clause-restatement node, or citation cycle is needed. The item and its statement hypotheses were preserved. The repair made during self-review was to cite the algebra tensor-product clause explicitly for both evaluation maps and to write out their coefficient compatibility, avoiding an unsupported identification of the module tensor product with a ring pushout.
