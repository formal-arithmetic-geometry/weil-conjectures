Files written:

- `dag/nodes/sec-picard-framework/lem-sp-cart-eilenberg-left-exact-cohomology.json`: statement item, split proof, three Mathlib searches plus unavailable LeanSearch record; no new nodes.
- `citations.json`: six verbatim statement quotes covering every cited dependency in the three proof steps.
- `report.md`.

Attachments: none.

WANTED: none.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Source error

The imported node cited Lemma 015I, but the source at `/home/ubuntu/c1-stacks-review/derived.tex` shows that 015I (`lemma-cartan-eilenberg`) is the existence lemma. The split-differential argument used by this item is in Lemma 015J (`lemma-two-ss-complex-functor`), in its proof under “Computation of the second spectral sequence” (around line 7240). I corrected the item's source and each step's source place to 015J; the mathematical statement is unchanged.

## Review by H1

I read the source definition and proof around lines 7085–7260 of `derived.tex`, including the Cartan–Eilenberg conditions, the existence lemma 015I, and the proof of 015J. The target statement agrees with the 015J argument: for each degree, cycles, boundaries, and cohomology are injective, so the relevant short exact sequences split and a left exact additive functor preserves the resulting cohomology comparison. The source-label correction above was made because the imported 015I citation named the wrong lemma.

Step 1 uses the definition of an abelian category for kernels, cokernels, and exact short sequences, and the injective-object definition for splitting the monomorphisms `B^q(C) -> Z^q(C)` and `Z^q(C) -> C^q`. Both cited statements say exactly these hypotheses. The step is elementary once those definitions are expanded. I checked the indexing at the lower bound and for a complex concentrated in one degree.

Step 2 uses the definition of an additive left exact functor: additivity preserves the split maps, and preservation of kernels identifies the transformed cycles. The injective definition is retained because the split maps originate in Step 1. The image identification follows from the split factorization of each differential, so no unlisted exactness fact is being used.

Step 3 uses the same abelian and left-exact definitions to identify cohomology as the quotient of transformed cycles by transformed boundaries. The split short exact sequence gives the canonical quotient isomorphism, and its construction is the comparison induced by the cycle and quotient maps in the item statement.

I searched the whole DAG and blueprint for this statement and for split cycle/boundary lemmas; no existing node states this comparison. The mandated searches were run for the item: LeanFinder returned only general homology-preservation declarations, Loogle returned no match, Mathlib grep returned no match, and LeanSearch was unavailable. Small checks used the zero complex and a complex concentrated in one degree; both reduce to the identity comparison. No new node was needed, and no cited node is circular or used for a claim absent from its statement.

## Second reading by H1

- Item statement: checked against Stacks `derived.tex`, Lemma 015J (`lemma-two-ss-complex-functor`), proof under "Computation of the second spectral sequence"; the source assumes injectivity of terms, kernels, images, and cohomology, while this auxiliary comparison uses only injective kernels and images. The latter suffice for the two splittings. The zero complex and a one-term complex give the identity comparison.
- Step 1: checked against `def-sp-abelian` and `def-sp-injective-resolutions`, and the split-differential sentence of 015J. The two exact sequences exist in an abelian category, and extending each identity across its monomorphism gives a retraction. Verdict: valid, including the lower bounded degree where the preceding boundary is zero.
- Step 2: checked against `def-sp-left-exact-additive`, `def-sp-abelian`, and `def-sp-injective-resolutions`, and the sentence in 015J after applying the functor. Additivity preserves both retraction equations; preservation of kernels gives the cycle identification, and the split factorization of each differential gives the image identification. Verdict: valid.
- Step 3: checked against `def-sp-left-exact-additive` and `def-sp-abelian`, and 015J's displayed identification of the second spectral sequence's first page. The cokernel of the transformed boundary inclusion is the transformed cohomology object by the split exact sequence, with the canonical comparison map. Verdict: valid.
- New nodes: none. The proof uses only three existing definition nodes; their statements were read and the quotes in `citations.json` checked against them. The independent LeanFinder search for preservation of homology of a split short exact complex returned generic exactness and splitting declarations, with no exact leaf for this item.
- Changes: corrected the stale 015I reference in `split_report.summary` to 015J. The imported `created.item` is maintainer-owned metadata and is retained by delivery packaging.
