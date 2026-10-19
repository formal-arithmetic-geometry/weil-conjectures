## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-slice-site-total-pseudofunctor.json` (statement split into three proof steps; no new nodes and no Mathlib leaves) and `citations.json` (verbatim citations for every cited step/node pair). The imported node was copied before editing; its statement, existing dependencies, source, and recorded searches were checked against the current shared DAG.

Attachments: none. I searched the read-only slopmaster2 source for the item id, its total-site vocabulary, and the blueprint tag; no sorry-free project declaration states this general theorem. Existing project declarations are specialized definitions or downstream slice-site constructions and are not attachments.

WANTED: none. The Stacks source `literature/stacks-project/spaces-simplicial.tex`, Tag 09WC, is present locally.

The statement is retained exactly. The stale imported split metadata belonged to the parent slice-site item; I updated only this item’s split report and proof to realize the current general coherent-pseudofunctor statement. No statement dispute was found. No new node was made: the three steps are the direct construction and verification from Tag 09WC, and creating nodes for the category/topology clauses would restate clauses of this item. The existing total étale definition is scheme-specific, while this item is for arbitrary sites and continuous contravariant pseudofunctors.

## Not duplicates

No new nodes were created. Whole-DAG searches for `09WC`, `total category`, `generated topology`, `pseudofunctor`, and `pullback stability` found only the existing scheme-specific total-site definition and the parent slice-site nodes; none states this general theorem. Whole-blueprint searches for the same terms found no separate equivalent blueprint node.

## Review by Q89

I read the item and its two statement dependencies, including the complete definition of a site and the continuity condition in `def-weil-pbc-sites-and-cohomology`. I read the full proof of Stacks Tag 09WC, Case A, at `spaces-simplicial.tex` lines 580–624. Step 1 checks the object and arrow orientation against the source: for `α:i→j`, the contravariant functor has source `C_j` and target `C_i`, and composition inserts the compositor; the unit and pentagon hypotheses in the item are exactly what the source’s strict identities use. Step 2 checks that vertical fibre coverings are the declared generators and that the site axioms are inherited from the fibre sites; the cited site definition explicitly supplies identity covers and transitivity. Step 3 checks the pullback object in the source: applying `u_α` to the fibre cover and pulling back along `f` gives the displayed fibre product, and the continuity statement supplies both covering preservation and the canonical pullback comparison. The item additionally assumes preservation of the fibre products used in this calculation, so no hidden existence hypothesis is introduced. The same site axioms give the generated topology and its isomorphism-sieve clause.

I tested the statement on a terminal one-object site with the identity pseudofunctor (the total site is the index category with only identity vertical covers), on a discrete two-object index category (no cross-degree arrows), and on a constant site with all `u_α` identities. Empty covering families are handled by the fibre-site axiom, and an isomorphism arrow gives the required covering sieve. I checked that every use of a non-elementary site or continuity fact is a cited verbatim statement in `citations.json`; the composition coherence in Step 1 is an unpacking of hypotheses, so it is marked elementary. No Lean files, compilers, Lake, or shared project files were touched.

The four prescribed Mathlib searches were run with the item id and are preserved in `searches.jsonl`: LeanFinder found only generic pseudofunctor stack declarations, Loogle found `GrothendieckTopology.pseudofunctorOver` but no total-site construction, grep found generic sheaf/topology files, and LeanSearch found generic precoverage pullback lemmas. None states this theorem, so `mathlib_match` remains null.

## Unfinished work

None. The delivery is stage 1 only; no Lean writing or compilation was performed.
