## What changed

Completed and checked the earlier sandbox attempt. The existing signature and docstring of
`AlgebraicGeometry.Scheme.etale_of_flat_quasiFinite_depth_two_boundary` are unchanged.
The proof imports `Sheaf.RingTheory.DepthLeSupportDimension` and the new proof-only module
`Sheaf.AlgebraicGeometry.Morphisms.QuasiFiniteFlatCodimensionOneEtaleNeighbourhood`.

The proof bounds every source stalk depth by its Krull dimension. At a boundary point this
makes the local dimension positive. Every dimension-one generalization belongs to W, since
otherwise its depth would be at least two and at most one. On W etaleness implies formal
unramifiedness. The pointwise branch-locus criterion supplies an etale neighbourhood of
each boundary point. Together with W these neighbourhoods cover X, and Mathlib's
`IsZariskiLocalAtSource.of_iSup_eq_top` assembles `Etale f`.

Both modules compile cleanly through lcompile.py. The DAG records this reduction and the
new pointwise criterion. No definitions, existing signatures or public imports changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etale_of_flat_quasiFinite_depth_two_boundary`
(node `lem-sbc-flat-quasi-finite-depth-purity`). No sorry remains in the item's module.

Added one named hole:
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_flat_of_quasiFiniteAt_of_codimension_one`
(node `lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood`). Its proof is exactly
`:= by sorry`; its docstring gives the complete discriminant argument of Stacks 0BJH.

This is a decomposition, not an axiom-free proof of purity: one upper hole closed and one
lower hole added. The lower statement is a pointwise criterion with a local-dimension and
unramifiedness hypothesis, and no open W or depth hypothesis. The depth-to-dimension,
dimension-one membership and global open-cover assembly are proved in the original module.
The existing depth-dimension dependency is already proved; this delivery does not add a
hole there. No arbitrary witness data is selected from the remaining hole: the neighbourhoods
are used solely to prove the proposition `Etale f`.

## No longer needed

None. No original import or proof-dependency node is removed. The depth-dimension lemma
remains necessary. All added proof imports are used. The finite-only criterion
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatCodimensionOneEtaleNeighbourhood` was examined
but not imported: the item assumes local quasi-finiteness, not finiteness. It was never an
item dependency, so this is not counted as pruning that module elsewhere.

## Where the brief, the DAG or earlier work was wrong

The original DAG's second step names no Lean declaration for the branch-locus argument.
The new node isolates exactly that step; it does not restate the depth-two global conclusion.
The earlier attempt supplied Lean files but no node records or report, so it was not deliverable.
Its new module also cited 0BVH for the discriminant criterion; this is corrected to 0BJF.

Read Stacks 0BJH, 0BJG, 02LK, 0BJF and 00ON against the new statement. Positive stalk
dimension excludes generic points; at dimension one the hypothesis includes x itself.
Zero-dimensional points are excluded explicitly, and an empty source has no x. The original
proof handles empty X and W = X via the source-open cover. No normality, dominance or
separatedness hypothesis is introduced. The unit's depth-two extension route is preserved.

LeanFinder and Loogle found no matching pointwise criterion. Grep found Zariski main's
etale finite localization and the finite-only Sheaf criterion, which require further descent
and local-dimension transport to apply. LeanSearch was unavailable (Internal Server Error),
as recorded in the new node's search results.

## New nodes

`lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-quasi-finite-flat-codimension-one-etale-neighbourhood.json`,
records the pointwise flat, quasi-finite-at-x criterion from Stacks 0BJH. Its new module is
`lean/Sheaf/AlgebraicGeometry/Morphisms/QuasiFiniteFlatCodimensionOneEtaleNeighbourhood.lean`.
It retains the original chapter, unit and blueprint ancestry. Its statement is tested on
empty sources and local dimensions zero and one; the complete proof in words reduces to
finite etale localization, the discriminant branch locus and the dimension-one contradiction.
There are no change records or forced adaptations.

## Second reading by G1

1. Compared the existing module with the repository using diff. Its existing
   declaration signature, docstring, visibility and definitions are byte-for-byte
   unchanged. Only two proof-only imports and the proof body changed. The second
   module is new. No change record or forced adaptation is required. Verdict: pass.
2. Compiled both modules in import order using lcompile.py. Both compile cleanly.
   Scratch copies with #print axioms show exactly propext, Classical.choice,
   Quot.sound and sorryAx for both declarations. The sole direct sorry is the
   named pointwise criterion listed above; there are no definitions, forbidden
   declarations or arbitrary witness constructions. The choice of neighbourhoods
   occurs only inside a proof of Etale f. Verdict: pass as a decomposition, not
   an axiom-free proof.
3. Read the new criterion against https://stacks.math.columbia.edu/tag/0BJH
   and its discriminant and local-dimension argument against Tags 0BJG and 0BJF.
   Positive stalk dimension is precisely the nongeneric-point condition; locally
   finite type converts the supplied formal unramifiedness to unramifiedness.
   Dimension zero is excluded, dimension one includes x itself, and the empty
   source has no x. Nonseparated schemes are allowed by the cited criterion.
   Repeated searches with different words: LeanFinder query "purity of ramification
   locus finite flat map codimension one unramified" returned ring-theoretic
   unramified-locus and ramification-index results; Loogle query
   "AlgebraicGeometry.FormallyUnramified" returned the property and its
   composition, base-change and diagonal facts. Grep for ramification, branch
   locus, codimension_one and discriminant in the library and Mathlib found no
   usable general criterion. Read the finite-flat specialization: it requires
   IsFinite, which this item does not assume. No short proof of the new hole was
   found. Its complete proof docstring and matching node are present. Verdict: pass.
4. Read the proof from the original theorem downward: depth at most support
   dimension supplies the local-dimension inequalities; a dimension-one boundary
   point gives the contradiction 2 <= 1; the pointwise criterion supplies the
   remaining neighbourhoods and the source-local open-cover theorem assembles
   them. Both added proof imports are used; the new module's public imports
   provide notions in its signature. The old proof_deps contained only the
   depth-dimension node, which is retained, so No longer needed is complete.
   Read the unit's depth-two extension step: this reduction retains its purity
   route. The unit record is untouched. Its existing realized fields are empty
   (statement and all seven steps), an upstream bookkeeping gap, not a route
   established or changed by this delivery. Verdict: proof route passes.
5. Compared the existing node with its repository version: only proof,
   proof_deps and proof_origin change. They describe the Lean reduction exactly.
   The new node's Lean statement matches its declaration verbatim and its
   source, ancestry, chapter, unit, creation and search fields are present.
   The pointwise statement is strictly the branch-locus part of the original
   argument, not a renamed depth-two boundary theorem. Verdict: pass.

Second reading changed only this report: recorded the independent checks, the
additional searches and the pre-existing empty unit realization fields. No Lean
proof or statement repair was needed. One original hole is closed and one new
hole is added, so the net hole reduction is zero; no module is pruned.
