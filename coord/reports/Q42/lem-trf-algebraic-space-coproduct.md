# Worker report: lem-trf-algebraic-space-coproduct

1. Files written:
   - `dag/nodes/sec-trace-formula/lem-trf-algebraic-space-coproduct.json`: item, split into five steps; no Mathlib match.
   - `dag/nodes/sec-trace-formula/lem-trf-fppf-sheaf-coproduct-partition.json`: new statement-only supporting lemma, unsplit; no Mathlib match.
   - `citations.json`: a verbatim statement quotation for every step citation.
2. Attachments: none. Searched slopmaster2 WeilConjectures for the exact blueprint tag, algebraic-space terminology and coproducts. There is no algebraic-space declaration. Master was read only as reference material; its declarations are not attachment evidence.
3. WANTED: none.
4. The imported statement's size condition said merely that the coproduct atlas was a scheme over S. Stacks 02WQ says it is an object of the chosen big site. I made this implicit site-size requirement explicit. STATEMENT-DISPUTED (size precision): a scheme outside a fixed big site's object bound cannot serve as the scheme atlas required by the site's definition, even though it is a scheme over S in a larger universe. This is a type/size issue, not a counterexample to the usual geometric assertion. The corrected statement follows 02WQ verbatim in intent and retains the original chosen atlases. I added the fppf-site, sheaf and scheme-coproduct notions to stmt_deps. No target statement is edited.
5. Nothing remains unfinished in the one-level split. The single new helper is intentionally statement-only and joins the queue. No Lean was written and no compiler, Lake or build tool was run.

## Sources and searches

Read `spaces.tex` 02WQ (lemma-coproduct-algebraic-spaces), 0F15 (lemma-coproduct-sheaves-open-and-closed), and 02WO (lemma-representable-sheaf-coproduct-sheaves). Read the affine-chart definition 02GI in morphisms.tex. The source of 02WQ omits the diagonal proof and the atlas details; these are supplied here, so proof_origin is agent. The helper records the set-indexed form of the scheme-test argument of 0F15/02WO; coproduct sheaf existence is the construction cited there, sites.tex 00WI (lemma-colimit-sheaves).

The helper is true for arbitrary sheaves, with no algebraicity or atlas hypothesis. Its future proof can sheafify the objectwise disjoint union, locally lift each section to a tagged summand, and use 0F15 to get the open-and-closed inverse image of each summand. The local lifts cover the test scheme, so the pieces cover it; disjointness gives uniqueness and the cartesian-square description. This is a non-elementary sheaf-theoretic representability result, not a clause of algebraic-space closure.

Whole-DAG searches by 0F15, 02WO, coproduct, representable diagonal, clopen partitions and fppf sheaves found no matching node. Whole-blueprint searches via blueprint_refs.py for coproduct, fppf, open and closed, 0F15, 02WO and 02WQ found no equivalent statement. Searches of Lean source found no exact declaration. Mathlib searches ran through msearch.py and their unmodified query strings and returned names were read; searches.jsonl preserves the command log. Both the item and helper were tried in two semantic phrasings, plus Loogle and grep. Read BigZariski.lean:147-160: the grep candidate compares a Zariski sheaf condition for a finite scheme cover and its coproduct, and does not represent pullbacks of summands in arbitrary fppf sheaves. The search hits on scheme coproducts, open immersions, module-presheaf generators and topological sheaf gluing do not state the helper. No Mathlib leaf was claimed.

## Not duplicates

lem-trf-fppf-sheaf-coproduct-partition vs lem-trf-set-sheaf-finite-extensivity: finite extensivity gives finite categorical disjointness and universal coproducts on an arbitrary site; it does not represent the summand pullbacks by clopen subschemes, and does not cover a set-indexed family.

lem-trf-fppf-sheaf-coproduct-partition vs lem-galois-coproduct-copies-morphisms-clopen: the existing node concerns morphisms into the scheme coproduct of copies of one base; the new node concerns arbitrary fppf sheaves, whose summands need not be representable.

lem-trf-fppf-sheaf-coproduct-partition vs lem-weil-pbc-sheaves-colimit-sheafification: the existing node is on a topological opens site; it has neither the big fppf site nor the scheme representability of coproduct summand pullbacks.

lem-trf-fppf-sheaf-coproduct-partition vs lem-trf-algebraic-space-coproduct: the item proves representable diagonal and a representable surjective etale scheme atlas from those of its summands. The helper assumes only arbitrary sheaves and supplies the clopen partition of a test scheme; the item's diagonal and atlas constructions remain in its own Steps 2 and 4.

lem-trf-fppf-sheaf-coproduct-partition vs lem-weil-pbc-sheaf-coproduct-finite-subcoproducts: the existing node proves the filtered-colimit presentation and sectionwise injectivity of subcoproducts of topological sheaves on one space; it does not concern arbitrary fppf sheaves or represent their summand pullbacks by scheme opens.

lem-trf-fppf-sheaf-coproduct-partition vs lem-trf-finite-coproduct-topos-coherent: the existing node constructs a finite coproduct of topoi from a disjoint-union site, with coherence properties; it does not represent pullbacks of summands of a sheaf coproduct on the fixed big fppf site by clopen subschemes.

## Review by Q42

I read the chapter sec-trace-formula and the unit sk-i-curve-zero. This auxiliary node serves the existing polarized-descent/etale-relation-quotient chain under the historical ancestor lem-trf-local-term-locality; it does not replace the unit's trace argument or use a purity route. The ancestor and via list are retained and the helper extends that list by this item. No SGA source is used.

For Step 1 I checked that def-trf-algebraic-space really gives a sheaf, and that the helper states the existence, injective coprojections, cartesian square, unique partition and base-change naturality used. In particular the proof never identifies the section set of a sheaf coproduct with the disjoint union of section sets.

For Step 2 I opened def-trf-algebraic-space: its representable diagonal applies to the two sections on each actual open intersection T_ii, with no separatedness or finite-type hypothesis. I checked that the helper's uniqueness forces equal tags after an arbitrary scheme pullback, including disconnected and nonreduced tests. The existing scheme-coproduct node supplies a scheme with disjoint open summands; the morphism-gluing node says exactly that maps on an arbitrary open cover glue uniquely. The cited sheaf equalizer condition makes equality local. Consequently E represents the full equality functor, not just its set of geometric points. Mixed-index pieces contribute nothing because equality forces the two partitions to coincide.

For Step 3 I checked the coproduct node's open-cover clause and the sheaf node's equalizer clause. The empty-cover condition supplies the unique empty-scheme section. Gluing the sections c_i p_i defines the actual map from U, and the preserved site-size hypothesis is used here.

For Step 4 I checked the atlas definition says that for every scheme T_i mapping into F_i the fibre product V_i is a scheme surjective etale over T_i. It does not require T_i to be affine or quasi-compact. The helper gives both the clopen scheme partitions and injectivity needed to remove c_i from the equality. The inverse maps between the tested pullback and h_V are explicitly described, and uniqueness is precisely the scheme-morphism-gluing statement. Thus this is a representability proof on all scheme tests, with no omitted descent or fibre-product theorem. All coproducts are indexed in the fixed size convention; the stipulated U remains the single allowed atlas.

For Step 5 I checked the definition node explicitly records the equivalent affine-chart characterization from 02GI. Charts of V_i to T_i are charts in V to T because both inclusions are open. Thus no unstated theorem about locality of etaleness or composition of morphisms is being invoked. Surjectivity is verified on points of every scheme test, which is exactly the atlas definition. I checked the empty-index family, all empty summands, a singleton, an infinite family with infinitely many empty pieces, and a disconnected test scheme mapping to different summands. In the empty-index case only empty tests map to F and the empty atlas meets the definition.

The helper's statement is self-contained: S, the site, indexing set, sheaves, h_T, partition, sections, and every square are introduced. It has no proof or proof dependencies. The fppf geometry in 0F15 is what is absent from the existing finite extensivity node. I checked B1-B10 and C1-C8 against the files, and D1-D5 and E1-E7 against the source: there is no restatement-helper, missing non-elementary citation, cyclic use of the parent quotient, or extra Noetherian, affine or finiteness hypothesis. Each proof step is shorter than 2000 characters. citations.json copies the relevant statements without paraphrasing. The only off-unit proof tool requested is generic scheme coproducts, declared in split_report.tool_uses; scheme-morphism gluing is already a Mathlib leaf. I corrected the size wording and filled the statement dependencies; the mathematical conclusion is unchanged.

The first dry run flagged the two further 00WI tag collisions just distinguished. I opened both complete statements: neither supplies the needed geometric representability. I also read sites.tex 00WI (lemma-colimit-sheaves) and its proof that sheafification, as a left adjoint, constructs colimits from presheaf colimits. The source citation is accurate.

The server preflight passed the completed split. In the final self-check I added def-weil-pbc-category-colimit to both statement dependency lists and identified the sheaf coproduct as the colimit of the discrete indexed diagram. I read that definition and checked its universal property; this is a definition citation and does not change either mathematical statement or the search questions. The corresponding helper quotations in citations.json were updated verbatim.
