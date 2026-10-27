## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-blowup-chart-properties.json`: item, statement; eight proof steps, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-proj-scheme-tests.json`: new statement-only node, unsplit; no Mathlib match. General relative Proj for any quasi-coherent nonnegative graded algebra on an algebraic space, representable over the base, with scheme tests and arbitrary base change.
- `citations.json`: one verbatim statement quotation for each cited node in each numbered proof step.

## Attachments

None for the item or the new node. Searches of `lean/WeilConjectures/` by the item's blueprint tag, blowup terms, algebraic-space terms and relative-Proj terms found scheme-only blowup/relative-Proj results. Those do not assert the item for arbitrary algebraic spaces. Existing scheme results are reused by their existing DAG nodes.

## Literature

No WANTED documents. I read `spaces-divisors.tex` at Tags 084B (lemma-relative-proj), 084C (definition-relative-proj), 085C (lemma-relative-proj-base-change), 085Q (definition-blow-up), 085R (lemma-blowing-up-affine), 085S (lemma-flat-base-change-blowing-up), 085T (lemma-blowing-up-gives-effective-Cartier-divisor), 085Z (lemma-blowing-up-projective), and 083S (lemma-complement-effective-Cartier-divisor). For the scheme reductions I read `divisors.tex`, Tags 0804, 02OS, 02NS and 07ZU, and the flat-base-change proof between 0804 and 02OS. I checked the tag-to-label map in `tags/tags`. I also read `spaces-morphisms.tex` Tag 083R (lemma-proper-local) and `descent.tex` Tag 05VG (lemma-equivalence-quasi-coherent-properties).

## Corrections and scope

The imported statement has no mathematical dispute. Its inherited TeX contained doubled backslashes in decoded strings; these are normalized. Added explicit references for relative Proj and the chart-ring notation. No mathematical clause or hypothesis is weakened, and zero ideals and empty centres remain allowed. No Lean was written or compiled, and the shared repository and launcher were not modified.

There was no previous item node, report, or search log in this sandbox. The current item was copied and its source, original searches and inherited blueprint metadata retained. No released repair note exists. The item is not already split or Lean closed in the read clone. This is a supporting node, not a unit key theorem: no unit realization fields were changed. `blueprint_refs.py ancestor` returns `None`; the new node preserves this null ancestor and the inherited via chain with the item prepended. The inherited unit record is `sk-thm-sf-ctf-stability` (whose recorded chapter differs from this node's supporting chapter); the corresponding path is absent from the latest blueprint. I retained the supplied route and metadata rather than inventing an imported ancestor. The chapter/unit records and current available blueprint were searched.

## Searches and Not duplicates

Every recorded Q68 Mathlib query was executed through `batch2/msearch.py`; results are retained in `searches.jsonl` and recorded under exactly the tool and query returned. Both the item and the new node were searched with LeanFinder in two phrasings, LeanSearch, Loogle and grep. All services answered. Hits were scheme Proj, its standard-open overlap isomorphisms, properness of scheme Proj and the ring Rees algebra. I read the actual definitions of `AlgebraicGeometry.Proj` in `ProjectiveSpectrum/Scheme.lean` near line 855, `Proj.pullbackAwayιIso` in `ProjectiveSpectrum/Basic.lean` near line 256 and `reesAlgebra` in `RingTheory/ReesAlgebra.lean` near line 39. They do not give the algebraic-space construction or the item's package. There are zero new Mathlib leaves.

I searched all `dag/nodes/` by the relative-Proj and blowup notions, by 084B/085C and related tags, and by prospective declaration names. `blueprint_refs.py search` was run for blowup, Proj, relative proj, the literal phrase `relative Proj`, 084B and 085C. The scheme relative-Proj nodes were opened and are scheme-only. Before writing the new node I found no algebraic-space general relative-Proj node.

## Not duplicates

lem-sfb-space-relative-proj-scheme-tests vs lem-sfb-space-blowup-chart-properties: both cite 084B, but the new node is a general construction for arbitrary graded quasi-coherent algebras and arbitrary base change; the item treats a Rees algebra, flat identification with another blowup, properness, Cartier boundary and density. The new node does not state these blowup-specific conclusions.

lem-sfb-space-relative-proj-scheme-tests vs lem-sfb-space-blowup-embedding-extension: both cite 084B, but the latter extends an immersion after modifying a space and merely takes the blowup calculus as a prerequisite. It does not construct relative Proj for general graded algebras or state its scheme-test comparison.

lem-sfb-space-relative-proj-scheme-tests vs lemma-nagata-relative-proj-exists: the existing node constructs a scheme over a scheme, through def-nagata-relative-proj; the new node has an arbitrary algebraic-space base and proves representability of the structural map on all scheme tests.

lem-sfb-space-relative-proj-scheme-tests vs lemma-nagata-relative-proj-base-change-arbitrary: the existing node is a scheme-base theorem in the same scheme-only context. It does not construct the algebraic space over a non-scheme or identify its arbitrary scheme tests.

lem-sfb-space-relative-proj-scheme-tests vs prop-nagata-relative-proj-functoriality: the existing relative-Proj construction and its coefficient algebra are on a scheme; the new node supplies the algebraic-space base and arbitrary algebraic-space base-change comparison. The scheme theorem cannot specialize in one line to that base.

## Review by Q68

I reviewed the split against B–E of `coord/delivery-errors.md`, with the item, new node, sources, and every cited node's statement open. This is the direct-delivery worker's self-review; no second worker was used.

The new node agrees with 084B and 085C: the coefficient algebra is quasi-coherent degree by degree, no finite-generation or flatness hypothesis is imposed on the base change, and scheme tests use the Zariski/small-etale equivalence. Representable means representable by schemes, not just by algebraic spaces. Its graded-isomorphism clause is the ordinary functoriality of the same functor: on scheme tests it changes coefficients by that algebra isomorphism. Its uniqueness is only uniqueness preserving the specified comparisons. It contains no proof steps, proof sketch, or proof dependencies. All objects and sites are introduced and their definitions cited. It is not a new node for each clause of the item: its content is independent of blowing up, and steps 2 and 4–8 still carry the Rees-algebra, properness and boundary arguments.

Step 1 uses exactly the chart-calculus clauses computing images and tensors and detecting finite type on every affine etale chart. Its induction constructs ideal powers; the separate kernels/colimits node explicitly permits arbitrary small direct sums. The general Proj node then applies to the actual resulting algebra. Thus finite type on the small etale site is not silently identified with finite generation of chart rings. No Noetherian or global quasi-compactness hypothesis is introduced.

Step 2 uses the fibre-product/covers statement to obtain chart refinements, the morphism-property definition to make the scheme map flat, the chart-adjunction statement for the actual local tensor formula and its compatibility, and the scheme etale/Zariski comparison for ordinary scheme pullback. I read both the Rees map definition and the theorem that this map is a graded equivalence: the latter is used only for flat scheme maps, not for arbitrary maps. Pullback quasi-coherence is stated by its own cited node. The local formula fixes the map on overlaps; inverse uniqueness and the sheaf gluing axiom prove it is an isomorphism globally, without assuming that all global sections are pure tensors.

Step 3 uses the new node's arbitrary-base-change and algebra-isomorphism clauses to turn the precise Rees equivalence into the blowup comparison. Open restriction is handled directly as restriction of ideals and products. The coefficient equivalence supplies the Zariski ideal, and the exact-finiteness comparison explicitly supplies preservation/reflection of finite type; the plain equivalence alone would not have been a sufficient citation for this. Finite generators of the original ideal map to generators of its extended ideal. The ordinary scheme blowup and its affine local model have the same Rees Proj, so comparison is by canonical restriction-compatible chart identifications, not a new choice of blowup.

Step 4 uses the existing affine properness theorem with its finite-generation hypothesis checked in step 1. Scheme and space properness agree by the cited morphism convention. I did not apply the scheme-target fppf criterion directly to the arbitrary space T: for each scheme test W I first use the pulled-back etale scheme cover, proper base change, and the scheme-target locality theorem, and then apply the arbitrary-scheme-test criterion to T. Every theorem invoked is in the cited node's statement; no properness claim is borrowed from the proof of another node.

Step 5 uses the finite-generator covering theorem, the chart isomorphism theorem and its map definition. The two latter nodes together identify the target D_+(at), so an isomorphism with an unnamed open is not substituted for the asserted chart. The finite covering is contained in the family of all a in K. Pulled-back etale covers and open refinements give covering charts on the source; open inclusions are locally identities and hence etale.

Step 6 uses the affine complement isomorphism under exactly its hypotheses. Uniqueness of inverses gives agreement on overlaps; the sheaf axiom glues an inverse, with both compositions checked locally. Neither topological density of U nor quasi-compactness of U is needed.

Step 7 uses the ideal/closed-subspace correspondence, whose statement explicitly identifies the ideal under arbitrary algebraic-space base change. The two scheme-chart lemmas say precisely KC=(a) and injectivity of multiplication by a on R[K/a]. These are enough to assert the inline effective Cartier condition, and identify the zero subspace scheme-theoretically. The generator is not assumed regular in R.

Step 8 proves the sheaf monomorphism on all small-etale objects. The cited etale-flat theorem applies to affine maps of schemes, and the flat-tensor theorem applies to the injective C-linear endomorphism multiplication by a. Thus regularity remains true on the etale refinement B. The equation defining zero in B_a gives a^n s=0; induction on n gives s=0. Scheme-test permanence ensures the refinements really are etale over the chart, and the structure sheaf's separatedness completes the argument. This proves schematic rather than only topological density. It also explains the details suppressed in the source's reduction to the scheme case.

For the item I checked K=O (empty centre, identity blowup, empty Cartier divisor), K=0 (Proj has no positive-degree points and the source is empty), nilpotent K (empty Proj), and R=k[epsilon]/(epsilon^2), K=(epsilon). For a nonempty example with a zero divisor, R=k[x,y]/(xy), K=(x): the x-chart kills y after passing into R_x, x is regular there, and its D(x) complement is schematically dense. For the new node I tested a grading concentrated in degree zero (empty Proj), O_X[t] (relative Proj is X, represented scheme tests are W), a polynomial algebra with two degree-one generators (a projective line bundle), an empty base, and a nonflat scheme test such as R→R/(f). The new base-change theorem retains the pulled-back graded algebra; it does not falsely replace that algebra by the Rees algebra of an image ideal for such a nonflat map.

I corrected the initial draft to make the finite-type coefficient comparison explicit, inserted the scheme/space properness agreement, and expanded the density check to affine etale refinements. All proof steps are shorter than 2000 characters. The only new node has complete hypotheses, normal TeX, real logged searches, explicit blueprint provenance, no maintainer fields, and statement-only status. Off-unit generic chart/descent tools are declared in split_report.tool_uses; they do not change the inherited unit route. citations.json was checked against the literal statements, not the proofs. No other node was edited.

## Unfinished work

None within this one-level split. The one new generic theorem is intentionally statement-only and queued for its own future split. Validation and delivery use only the prescribed server tools.
