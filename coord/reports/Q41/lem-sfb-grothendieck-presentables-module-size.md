## Worker report

Files written, all under this item's sandbox:

- `dag/nodes/sec-six-functors-basics/lem-sfb-grothendieck-presentables-module-size.json`: item split in five steps; statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-separator-exact-module-adjunction.json`: statement, Mathlib leaf, with one named declaration per clause and the relevant instances and source lines.
- `dag/nodes/sec-six-functors-basics/lem-sfb-small-module-cardinal-colimits.json`: statement-only bounded-module presentability input; no Mathlib match, but an exact project declaration was found and is attached below. The audit state is left for the maintainer's audit tool, rather than assigning closed ourselves.
- `citations.json`: a verbatim statement quote for every citation of every item step. Search commands and their returned results are retained in `searches.jsonl` and `search-results.json`.

## Attachments

`ModuleCat.isCardinalPresentable_of_hasCardinalLT` belongs to `lem-sfb-small-module-cardinal-colimits`, `lean/WeilConjectures/Mathlib/Algebra/Category/ModuleCat/FilteredColimits.lean:76` (proof through line 90).

Its conclusion is the cardinal presentability predicate with precisely the ring and module size assumptions. The new statement uses only the uncountable regular special case. Factorization and eventual equality are the standard expression of the same Hom-colimit bijection. I read the declaration, its free-module and cokernel prerequisites in that file, and the project's `hasCardinalLT_finset` proof in `WeilConjectures/Mathlib/SetTheory/Cardinal/HasCardinalLT.lean:27`; none contains `sorry`. All other proof ingredients there are Mathlib. The declaration was not assigned to any existing DAG node by a search for its full and short names. This is an attachment for a new prerequisite, not an ATTACH disposition of the whole item: the whole item also requires the exact-localization argument and converse.

## Literature

WANTED: Hall--Neeman--Rydh, *One positive and two negative results for derived categories of algebraic stacks*, arXiv:1405.1888, Appendix A, Remark A.4 and Lemma A.5, archived under `literature/`, for `lem-sfb-grothendieck-presentables-module-size` and its bounded-module prerequisite.

I read https://arxiv.org/html/1405.1888 online, including both implications of A.5 and the opening of A.6. The archive is absent from the listed local literature. Accordingly the item's expanded proof has `proof_origin.by = agent`; no literature files were written or downloaded. The Mathlib leaf is sourced directly to its installed Mathlib source. No Stacks tag states the full module-size characterization; I did not invent one. Stacks `algebra.tex`, `lemma-characterize-finite-presentation-hom`, is only the finite-presentation analogue, not a substitute source for the arbitrary regular-cardinal assertion. No SGA source is used.

## What needed correction

The initial item had an empty proof. Its statement agrees with HNR: for each allowed rho take the paper's infinite mu to be max(aleph_0, |R|), which is less than rho. There is no statement dispute or alteration of hypotheses. The proof now spells out the adjunction comparison, the two pullback projections, the bounded replacement, and injectivity of the Hom-colimit comparison. In the source's pullback discussion the relevant image is that of the projection to N; I label it explicitly as im(p). HNR's displayed factorization argument gives surjectivity, and I supply the eventual-equality argument needed for the stated definition of presentability. The converse keeps its monomorphism argument; merely knowing that c is a retract would not yet yield the required bounded module representative by that proof.

The computed blueprint ancestor for this item's existing created-item chain is null (`tools/blueprint_refs.py ancestor`). I retained the inherited chain and null root, with the named place in `det-thm-sf-ctf-stability-direct-images` proof (3) and HNR A.4--A.5, rather than inventing a blueprint id or changing somebody else's node. The current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` was read. Its direct-image route and the unit record are unchanged.

## Not duplicates

`lem-sfb-separator-exact-module-adjunction` vs `new-stage3-gabriel-popescu-abelian-core`: the new leaf concerns a specified separator in the original Hom/module universe and includes full faithfulness of its specified Hom functor; the existing node assumes a chosen derived category and large derived coproducts and produces an existential presentation in an enlarged module universe. Its stronger hypotheses cannot be added to this item.

`lem-sfb-separator-exact-module-adjunction` vs `lem-c3-grothendieck-derived-gabriel-popescu-presentation`: the latter also assumes derived-category structures and includes a compact derived source; it does not supply the stated separator adjunction under this item's hypotheses.

`lem-sfb-small-module-cardinal-colimits` vs `lem-sfb-presentable-generator-cardinal-bound`: the latter chooses a presentability rank for a generator in an arbitrary Grothendieck category; the new input proves a specified size bound for a specified module and every allowed regular cardinal.

`lem-sfb-small-module-cardinal-colimits` vs `lem-weil-pbc-filtered-colimit-modules-elementwise`: elementwise representatives and eventual equality for individual elements do not assert factorization of linear maps from a bounded-size module. The linearity and simultaneous relations are exactly what the attached project theorem handles.

Whole-DAG statement/title searches and blueprint searches for Gabriel, submodule, filtered module, cardinal module, module presentable, and presentable cardinal found no duplicate of either new statement. Several blueprint search hits use “representable”, not “presentable”; I inspected their stated concepts. No new node carries a Stacks tag, so there is no same-tag pair to explain beyond these conceptual candidates. The new module lemma is a prerequisite in the module category alone, not either implication of the item's localization characterization. The adjunction is a genuine Mathlib leaf, not a relabelled unsplit clause. The bounded roof and the filtered union remain explicit arguments of the item; I searched the roof but created no node for that routine construction.

## Review by Q41

I checked B--E of `coord/delivery-errors.md` against the source, node statements and search results. Both new nodes introduce their rings, categories, universes and cardinals, define presentability/generator inline as needed, and cite only the notions their statements actually use. They carry statement-only data, complete blueprint fields, and the actual search queries. For the adjunction I read Mathlib's tensor definition and adjunction at lines 50 and 54, GabrielPopescu.full at 118 and preservesFiniteLimits at 147, the generator-faithfulness theorem at Generator/Preadditive.lean:61, additive_coyonedaObj at Yoneda/Basic.lean:100, left_adjoint_additive at Adjunction/Additive.lean:42, and the counit instance at Adjunction/FullyFaithful.lean:97. Each clause has that declaration or the inferred instance specified in the match. For the other new node I read the project theorem and its actual prerequisites as described under Attachments; its closest Mathlib hits concern Type or the forgetful functor and require additional arguments, so I did not label it a Mathlib leaf.

Step 1 uses the Grothendieck definition precisely for the generator and small colimits, the new separator lemma for the adjunction/exactness clauses, and the existing left-adjoint colimit lemma for colimit preservation. End(P) is U-small by the original Hom-universe assumption; no derived structure is assumed.

Step 2 uses the definition of colimit for the module quotient construction, the left-adjoint lemma for FA, and the finite-list cardinal bound for generated submodules. The counit naturality identifies F(t) with the inverse of epsilon_x. Kernels/cokernels are killed because F preserves both. This uses only the already established finite-limit and colimit properties of F, not an unproved assertion that G preserves filtered colimits. The finite-list encoding includes coefficients and generators and the uncountability hypothesis ensures the aleph_0 term stays below rho.

Step 3 cites the bounded-module theorem exactly for the linear map M to the module colimit A. I checked that M is generated by at most |N| lifts, hence is small. Its kernel embeds in ker(t), and its cokernel is coker(p), both annihilated by F. This makes F(v) invertible. Applying the adjunction to the written equation nv = t a_i b gives the stated factorization with the inverse of F(v); I did not assume a lift of all N to Q.

Step 4 uses the same bounded-module statement, now for eventual equality of n restricted to K and zero. K is literally a submodule of N and has size less than rho. The equation F(z)=0 makes F(K to N) invertible by preservation of kernels. Cancellation after applying F therefore kills h at one later stage. Subtraction handles two maps, and ordinary filteredness handles different stages. This proves injectivity, not just the factorization half of presentability.

Step 5 uses the left-adjoint colimit lemma on the explicit union cocone. The indexing poset is a subset of the power set of Gc in U. Regularity bounds a union of fewer than rho underlying sets, and the step-2 estimate bounds its generated sum. Compatible linear maps glue on elements, so no large-index colimit existence theorem is being applied. F preserves each inclusion, so the factorization of id_c is through a monomorphism; the explicit cancellation proves it invertible.

I tested the zero category/ring and zero module, finite rings, cyclic modules, rho = aleph_1 for countable R, non-poset filtered categories, and maps with zero colimit. The index of small submodules contains zero; a rho-filtered index is nonempty. None of the argument needs the generator itself to have a separately bounded presentability rank. The proof also makes no ring commutativity assumption. All five steps are under 2000 characters; the pullback construction and converse union are written out, so no long step hides a cited lemma. Citations contain verbatim statements, not proof fragments or definition nodes used as theorem substitutes. No cycle is introduced: both new nodes have only notion dependencies. The existing generic leaves are Mathlib, and the new prerequisite is in the item's own unit, so no off-route tool approval is needed.

## Unfinished work

No part of the item's natural-language proof remains unfinished. The new bounded-module prerequisite is already stated by the recorded project declaration; its final closed audit state is for the maintainer's independent attachment/audit check. No Lean file, compiler, Lake command, repository file or launcher script was written or run. Server checks and the required delivery dry run are performed after this self-review.

The first dry run requested a numeric `mathlib_match.line` in addition to the clause-by-clause line references in `how`; I added the verified primary declaration line 147 and reran the dry run.
