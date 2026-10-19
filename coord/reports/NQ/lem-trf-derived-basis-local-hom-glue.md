# Stage-1 report: lem-trf-derived-basis-local-hom-glue

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-local-hom-glue.json`: existing statement retained, split into five steps. No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-local-ext-sheaf.json`: new statement-only, unsplit, general ringed-space basis criterion of Stacks 0D66(2). No Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-derived-basis-open-subcollection-map.json`: new statement-only, unsplit, scheme specialization of Stacks 0D5Q. No Mathlib match.
- `citations.json`: a verbatim statement quote for every step/node citation.

## Attachments

None. Searches by item id, blueprint tag, local negative Hom/Ext gluing, and the Stacks lemma names in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration giving the complete item or either new input. Upstream master was treated only as reference material. The item has no recorded Lean declaration to attach.

## Wanted literature

None. Both source files and the tag/label mapping are available locally.

## Corrections and unfinished work

The item was a statement-only, unsplit node, not an attempted proof. Its mathematical statement is correct and was not changed. Its existing metadata, original blueprint ancestry and via list are retained. The supporting quotient-map result is stated only for underlying spaces of schemes, which suffices for this item; the source proves it for arbitrary topological spaces. The other new node retains the general ringed-space hypothesis because the auxiliary space Y need not be a scheme or locally ringed.

The first server DAG check found missing chapter/unit metadata in the two new files; both now inherit sec-trace-formula/sk-i-curve-zero. The first delivery dry run found missing definition citations in their statements. Those have been added, after opening the definition statements. The proof now explicitly defines the auxiliary ring sheaf and its structural map. No Lean was written or compiled. The two new nodes intentionally remain unsplit, as required for a one-level split. Nothing in the assigned split remains unproved except these separately stated external inputs.

## Review by NQ

I read Stacks `cohomology.tex`, lemma-vanishing-and-glueing (0D66), part (2), and lemma-uniqueness (0D68), including the construction of the auxiliary ringed space in its proof. I read `topology.tex`, lemma-create-map-from-subcollection (0D5Q), including its proof by equivalence classes of indistinguishability under the chosen open collection. These are the sources of the item and both new nodes. I checked the tag/label pairs in `literature/stacks-project/tags/tags`. I also read the assigned chapter and unit records and retained the inherited BBD supporting route. This is not a new proof of the trace-formula unit or a change of its route.

Step 1 uses exactly the covering/refinement hypotheses of the new 0D5Q input and takes exactly its continuity, open-image, inverse-image, and basis conclusions. The claim about a union O follows by taking unions of the identities f^{-1}f(U)=U. Although the lemma's conclusion does not separately say surjective, its basis images cover Y, so it implies surjectivity even for the empty family.

Step 2 supplies the ringed-space hypothesis required by 0D66: O_Y(V)=O_X(f^{-1}V), with restrictions and rings inherited from O_X. Inverse images preserve covering unions and intersections, so the sheaf equalizer axiom in def-weil-pbc-sites-and-cohomology applies literally. The identity ring map is precisely a structural map under def-weil-locally-ringed-space-morphism, whose statement I opened and checked. This proves the needed construction in a few lines and creates no extra node.

Step 3 uses the new 0D66 statement, not its proof: its inputs are the ringed map of Step 2, the basis of Step 1, and the global objects M,N. On a basis open f(U) its preimage is U, so every local cross negative Hom group in its hypothesis is exactly a group assumed zero by the item. The outputs are negative Hom vanishing on all preimages of opens of Y and the sheaf F(V)=Hom(M|_{f^{-1}V},N|_{f^{-1}V}). The definition references in the new statement define ringed maps, derived categories with shifts, module sheaves, and the sheaf axiom; I read all four statements. Restriction and topological basis are specified inline.

Step 4 is the elementary sheaf-axiom argument, expanded rather than left as a hidden comparison lemma. Saturation gives f(U) intersect f(V)=f(U intersect V). The given W inside each intersection therefore cover the image intersection. Inclusion compatibility identifies both restrictions with a_W on every such member; separatedness identifies the restrictions on the whole overlap, and existence glues the family. Restriction of a global section gives the inverse operation. This uses exactly the sheaf assertion from 0D66 and the equalizer definition in def-weil-pbc-sites-and-cohomology, with the topological properties of 0D5Q.

Step 5 uses the all-open vanishing clause on f(O), together with f^{-1}f(O)=O. The empty-cover sheaf axiom supplies the singleton Hom set on the empty open; this handles both an empty indexing family and one containing the empty open. If X and C are empty, the basis-cover conclusion forces Y empty, so no nonemptiness assumption enters. The same tests apply to the supporting statements: the empty basis on the empty space is allowed; a singleton cover {X} reduces to the assumed vanishing and a sheaf on a one-point auxiliary space. I also tested a non-basis collection consisting of disjoint covering opens: the quotient is discrete, so no assumption that C is a basis of the original topology has been silently added.

I searched the full DAG for both Stacks tags, their labels and negative-Ext/sheaf or quotient-cover concepts, and searched the full blueprint using blueprint_refs.py for 0D66, negative, vanishing-and-glueing, and create-map-from-subcollection. The tag hits were the item and its BBD parent; the other negative-Ext hits concern specialized Koszul or coefficient computations and do not state these tools. The supporting statements are not clauses renamed from the item: 0D66 is the general morphism-over-a-basis criterion, while 0D5Q is the purely topological construction needed to use it on a family which need not be a basis.

For each new node I ran LeanFinder, LeanSearch, Loogle and source grep through msearch.py and read the returned declarations. Each has two natural-language phrasings. The initial Loogle patterns were rejected for unknown identifiers; I retained that result as an invalid query and then ran valid patterns. The derived-Hom query returned no criterion. Topological hits concern already-given topological bases, quotient topologies and open maps; they assume a basis in the domain, whereas our cover is only intersection-refining and the required codomain topology must be constructed. I read the candidate basis criterion in Mathlib/Topology/Bases.lean; it does not supply that quotient construction in one line. All recorded searches are actual logged calls; no failed service was treated as evidence of absence.

Every cited statement has a literal quote in citations.json. No proof step exceeds 2000 characters. The new nodes carry only statements and definition dependencies, not proofs or proof sketches. The split has no new definition or SGA source and does not identify any coefficient categories. No statement dispute or missing hypothesis was found.

## Not duplicates

- lem-trf-derived-basis-local-ext-sheaf vs lem-trf-derived-basis-local-hom-glue: 0D66 treats a general morphism of ringed spaces and a basis of its target; the assigned item instead has a possibly non-basis open family on a scheme and requires the explicit inclusion-compatible-family bijection, proved by the quotient construction and overlap calculation.
- lem-trf-derived-basis-local-ext-sheaf vs lem-trf-derived-basis-bbd-descent: the new statement concerns morphisms between two already-global objects; the parent constructs objects from local derived descent data and proves their uniqueness. The parent's 0D66 citation explains its local-Hom input and is not a statement of 0D66.
- lem-trf-derived-basis-open-subcollection-map vs lem-trf-derived-basis-local-hom-glue: the new statement constructs a continuous map and a target basis from open-set refinement; it contains no derived objects, negative Hom vanishing or morphism descent conclusion.
- lem-trf-derived-basis-open-subcollection-map vs lem-trf-derived-basis-bbd-descent: the new statement only constructs the topological auxiliary space, whereas the BBD parent constructs and compares derived objects.
