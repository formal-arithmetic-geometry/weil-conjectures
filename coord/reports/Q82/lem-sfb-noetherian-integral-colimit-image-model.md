# Q82: lem-sfb-noetherian-integral-colimit-image-model

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-integral-colimit-image-model.json`: existing statement, now split in six steps. Its statement and statement dependencies are unchanged. The item is not a Mathlib leaf: neither semantic phrasing nor the pattern/local searches found the varying-base image-subalgebra conclusion.
- `citations.json`: one verbatim statement quotation for every node used in every step.
- `searches.jsonl`: actual searches made through the required msearch command; the original Q156 searches inside the item are retained, followed by the Q82 records.
- `report.md`: this report. The sandbox also contains the task-specific generation script `write_split.py`; it is not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. All non-elementary inputs already have DAG nodes with Mathlib matches. No Lean was written or compiled.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by integral/Noetherian/colimit terminology. Read the nearby `FiniteMapColimitDescent`, `IntegralElementsColimitDescent`, and `FlatFinitePresentationModel` declarations: these descend properties of fixed tensor models, rather than constructing the finite image-subalgebra demanded here. They do not state this item.

## WANTED

None. All source material used is present.

## Corrections and dependencies

The item was genuinely unsplit: it had no proof. Its statement is true as written, and no STATEMENT-DISPUTED correction is needed. The source expressly labels its image-subalgebra refinement as agent-written; the proof remains marked `proof_origin.by = agent`. No claim is made that Stacks 05N9 itself states the stronger image-model conclusion.

The existing node `lem-weil-pbc-colimit-category-fp-algebras` states only parts (2) and (3) of 05N9, concerning maps between base-changed fixed finitely presented algebras. It does not state the part (1) existence assertion or a map to the varying diagram D_i. I therefore do not cite it for either of those claims. Similarly, `lem-weil-pbc-polynomial-coefficient-tensor-quotient` concerns a conormal module, not base change of a polynomial presentation; it is not used. No dependency is taken merely from another node's proof.

The seven distinct proof dependencies are existing Mathlib leaves: finite module generators, finite type over a Noetherian ring implies finite presentation, the finite-presentation definition, the elementwise ring-colimit theorem, finite adjoin of integral elements, the algebra-tensor pushout property, and the module tensor definition. No off-unit unsplit statement is used as a tool. The five original statement dependencies remain necessary. No pre-existing proof dependency was dropped, since there were none.

Read the latest blueprint unit `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, alongside the chapter and unit DAG records. The latest proof (3) discusses preservation by proper and open direct image; it does not assert this algebra lemma. The inherited historical place and creation chain are preserved, including its null imported ancestor. Whole-blueprint searches for `image-subalgebra`, `image subalgebra`, `finite subalgebra`, and `integral colimit` found no equivalent node. A broader finite-presentation search was also inspected. The split supplies a generic auxiliary fact in the historical chain; it does not change the unit route or its realization fields.

## Not duplicates

No new nodes were created. The duplicate/tag searches for 05N9, 00GM, finite presentation over a Noetherian ring, ring-colimit representatives/equality, and finite integral adjoin identified the existing inputs used below. In particular `lem-sc-finite-generated-integral-subring` already states precisely the finite-adjoin result, so no parallel finite-subalgebra node was introduced.

## Review by Q82

I read Stacks `algebra.tex` at 05N9 (`lemma-colimit-category-fp-algebras`, especially the proof of (1)), 00GM (`lemma-characterize-integral`, including its bounded-monomial proof), 00FP (`lemma-Noetherian-finite-type-is-finite-presentation`, (3)), and 00D6/00D7 (`lemma-directed-colimit`/`lemma-zero-directed-limit`). I checked the tag-to-label table. The elementwise sources 00D6/00D7 are written for modules; the cited existing ring-colimit node explicitly states the ring version and records its Mathlib forgetful-functor proof. I rely on that node's ring statement, not on an unstated module-to-ring identification. There are no new nodes requiring separate source review.

Step 1 uses the finite-module definition to get finite algebra generators, then the exact statement of `lem-weil-pbc-finite-type-noetherian-finite-presentation` with R=S and its algebra equal to D. Noetherianity is assumed only for S, exactly where needed. The finite-presentation definition gives some finite polynomial presentation; the proof does not assume that an arbitrary preselected presentation has finitely generated kernel. Its presentation generators may differ from the module generators.

Step 2 uses clause (1) of `lem-pc-filtered-colimit-commrings-elementwise` separately for S and D. Its statement actually provides representatives of every colimit element in a ring diagram. Smallness and filteredness hold because the given index is a small nonempty directed poset. Every polynomial has finite support and the lists of variables and equations are finite. Repeated directedness therefore puts all coefficient and element representatives at one stage. Empty lists are covered by nonemptiness.

Step 3 uses clause (2) of that same node, not just its representative clause: equality of the evaluation with zero supplies a later arrow killing it. In a poset the two arrows from the original stage agree. The transition square compatibility ensures that evaluating a transported polynomial at transported generators is the transported evaluation, since evaluation is a finite sum of products. This proves actual vanishing in D_i, without an injective coprojection or a flat transition. A common upper bound kills all relations simultaneously.

Step 4 applies the full statement of `lem-sc-finite-generated-integral-subring` to the finite family x_a inside the S_i-algebra D_i. The given integrality of D_i over S_i supplies its hypothesis for every x_a. The result states finiteness of precisely the subalgebra generated by those elements, not merely the existence of a possibly larger finite subalgebra. Subalgebra means the image of polynomial evaluation and contains the structural image of S_i; no embedding S_i into D_i is assumed.

Step 5 uses the algebra-tensor pushout node for the ring structure, the multiplication formula, and the canonical map to D. The finite-presentation definition supplies the explicit quotient description of D. The module tensor definition supplies the balancing relation. I wrote out the quotient check: evaluations of all f_b vanish by the lifted equations, and a difference in the relation ideal is a finite sum of multiples of those f_b and hence evaluates to zero. This constructs the inverse directly; it does not cite a nonexistent polynomial-quotient tensor lemma or assume that tensor preserves the inclusion H into D_i.

Step 6 is elementary after those constructions. Both composites are checked on explicit generators. On H, each element is a polynomial in the x_a with coefficients from S_i by its construction, and balancing gives the needed equality on that entire polynomial. On T, every pure tensor is fixed and the module tensor node explicitly says that pure tensors generate. The cited algebra-tensor node gives the product formula used in that computation. Thus the inverse is for the specific canonical multiplication map in the statement, including its S-algebra structure, and not an unspecified ring isomorphism.

I checked delivery-errors B--E point by point. The statements of all seven cited nodes were open during the audit, and every use has a copied quotation in `citations.json`. No fact was extracted from a cited proof or Lean docstring. All new constructions and the inverse calculation are carried in the item; no clause was renamed as a new lemma. Each proof step is below 700 characters, so none exceeds the 2000-character long-step threshold or hides a general comparison theorem. The finiteness of the integral adjoin and the finite-presentation theorem are cited rather than called elementary.

Small cases checked: if D is zero, a presentation may include 1 as a relation; its lifted evaluation becoming zero forces a suitable D_i (and hence H) to be zero, so the same construction works. If S is zero then D, as a unital S-algebra, is zero and this case applies. With no variables H is the structural image of S_i; with no relations the vanishing step uses i=i_0. For a singleton index, H=D when the presentation generators generate D. Noninjective transitions are handled by eventual equality rather than cancellation. Nonflat coefficient change, for example Z to Z/2 with D_i=S_i, gives the expected scalar-extension map and uses no tensor-injectivity claim. Non-Noetherian S_i causes no problem because only integrality and finite adjoin are used there.

## Unfinished work

None in this one-level split. Independent maintainer mathematical review remains part of the delivery process.
