## What changed

Replaced the first worker's factorization/bijectivity split by the separate kernel
and image computations of the same local trivialization argument. The existing
`AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist` signature,
visibility, definitions, and original public imports are unchanged. Its proof now
uses Mathlib's `imageSubobject_mono` and `Subobject.isoOfMkEqMk` to construct the
required isomorphism, then `appLinearEquivOfIso` for bijectivity on each open.
The two new modules are imported privately by the item. Each states a named hole
with a source and a complete natural-language proof. No new data definitions.

## Proved and sorry left

Hole closed syntactically in the existing module:
- `AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist`
  (`lem-sc-closed-immersion-disjoint-ideal-twist`).

Holes added and left open:
- `AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist_mono`
  (`lem-sc-closed-immersion-disjoint-ideal-twist-mono`).
- `AlgebraicGeometry.Scheme.Modules.closedImmersion_disjointIdeal_twist_image`
  (`lem-sc-closed-immersion-disjoint-ideal-twist-image`).

This is a decomposition, not a completed proof: one upper hole replaced by two
strictly smaller lower holes, net -1 in the relevant import closure before any
ledger-specific baseline effects. The image statement omits disjointness and
computes only an image; the mono statement computes only injectivity of the
ambient restriction, without the target product or tensor comparison e.
The discarded factor/bijective statements are not delivered.

## No longer needed

No existing library modules are pruned and no original public imports removed.
The parent no longer directly uses its old proof dependencies:
`def-sbc-closed-immersion-ideal-sheaf`, `def-weil-closed-immersion`,
`def-pc-module-pullback`, `def-sc-invertible-module`,
`def-pur-sheaf-tensor-product`. They remain needed in the lower kernel/image
arguments and in public signatures; they are not claimed as globally pruned.
The first worker's new Factor and Bijective modules and nodes were removed from
the proposed delivery, replaced by Mono and Image.

## Where the brief, the DAG or earlier work was wrong

The first worker's two lower nodes cited the parent in `proof_deps`, producing a
circular proof plan, and their one-line docstrings did not give proofs in words.
Their DAG statements were not self-contained, and they inherited irrelevant
review metadata from the parent. The parent DAG was not updated to the actual
Lean reduction. These faults are repaired. Searches found Mathlib's generic
image/subobject machinery, which removes the need for an additional factorization
or sectionwise-bijectivity hole. The scheme-specific kernel/image calculations
remain open; they cannot be closed merely by those generic lemmas.

## New nodes

`lem-sc-closed-immersion-disjoint-ideal-twist-mono`, in
`lean/Sheaf/AlgebraicGeometry/ClosedImmersionDisjointIdealTwistMono.lean`, is the
zero-intersection kernel calculation, followed by sheaf separatedness.
`lem-sc-closed-immersion-disjoint-ideal-twist-image`, in
`lean/Sheaf/AlgebraicGeometry/ClosedImmersionDisjointIdealTwistImage.lean`, computes
the quotient ideal image without any zero-intersection hypothesis.
Both have complete docstring proofs and self-contained statements. Neither cites
the parent. There are no change records because existing interfaces are unchanged.

## Second reading by J3

1. Compared the item with the repository using `diff`: only private proof imports
   and its proof body changed. The existing theorem signature is byte-for-byte
   unchanged. No other existing module, statement or definition is adapted.
2. Compiled the complete three-module set in import order with `lcompile.py`.
   The existing theorem contains no sorry; the two new named theorems contain
   exactly one each. No axioms, unsafe/opaque/extern declarations or hollow data
   definitions occur. Scratch copies with `#print axioms` check all three names;
   only standard axioms and the disclosed `sorryAx` are permitted. This remains
   a decomposition, not an axiom-clean proof of the parent.
3. Read Stacks Remark 09NW and Lemma 09NX at their official tag pages (the local
   `literature/stacks-project/varieties.tex` is absent). Checked the calculation
   K -> (K+J)/J: its kernel is K intersection J; its image is the quotient ideal
   for all K,J, without disjointness. In particular A=Z, K=(2), J=(3) demonstrates
   why the image fact must not imply injectivity; and A=k x k, K=k x 0,
   J=0 x k tests a nonzero disjoint pair. K=0, J=0, J=A with K=0,
   empty schemes/opens and m=0 cause no exception. Arbitrary linear e preserves
   an ideal product using e and e.inv; changing adjunction transports its unit by
   a natural isomorphism and leaves the adjoint ideal image unchanged.
   Repeated searches with different wording via leanfinder, loogle, grep and
   LeanSearch (unavailable, recorded). Read `IdealTensorImageComparison`,
   `ModulePullbackIdealProductImage`, `AffinePushforwardIdealProduct` and
   `IdealModuleProductStalk`: they provide related representations, not either
   exact kernel/image statement. The first three results concern extended products
   or different ambient modules; none alone supplies restriction of the source
   product. Mathlib's imageMonoIsoSource and IsImage.isoExt are generic tools;
   isoOfMkEqMk is the shorter reconstruction used here.
4. Checked the top-down reduction: monicity plus equality of image subobjects
   gives the isomorphism by Mathlib; no new factorization or bijectivity assertion
   hides the parent. Mono has no target-product data, and Image has no kernel-zero
   hypothesis or bijective conclusion, so each is strictly a part of the argument.
   All new public imports serve their signatures; the item uses the new imports
   only in its proof. The unit `sk-thm-curveestimate` has statement realized by
   `thm-sc-proper-cohomology` and no step records; neither the unit route nor its
   realized field changes. Pruning is fully described above.
5. Read each delivered node against its Lean declaration. The new verbatim
   signatures, sources, searches, creation/blueprint records and chapter/unit
   agree. The parent's two proof steps cite Mono and Image; lower proof steps
   cite only their underlying definition nodes and never the parent, so the
   original cycle is removed. No unowned reviewed fields are copied into new nodes.

Changes made in this second reading: replaced the shallow cyclic split by
kernel/image lemmas; reconstructed the actual morphism as an isomorphism using
Mathlib; supplied complete proof docstrings and self-contained new nodes; updated
the parent's proof/dependency records; corrected accounting to a decomposition.
