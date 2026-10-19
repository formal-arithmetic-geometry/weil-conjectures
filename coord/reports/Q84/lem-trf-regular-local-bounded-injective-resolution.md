# Stage-1 report: lem-trf-regular-local-bounded-injective-resolution

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-local-bounded-injective-resolution.json`: statement, now split into six proof steps; no Mathlib match.
- `citations.json`: ten step/node entries, each quoting the exact cited statement. No new nodes and no Mathlib leaves.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only scratch, not a delivered DAG file.

## Attachments

None. Searched `WeilConjectures/` in the prescribed slopmaster2 checkout for the item tag and for regular local rings, global dimension, injective dimension, and bounded injective complexes. Its regularity theorems and bounded-below derived-functor machinery do not assert the item. The item has no recorded Lean declaration or open audit frontier to attach. The read-only master source is not used as proof evidence.

## WANTED

None. All sources used are in the supplied Stacks checkout.

## Findings and changes

The statement is correct and is retained verbatim, with its three statement dependencies unchanged. There is no statement dispute. The imported node had an empty proof. Its source, Stacks 0AWX (`dualizing.tex`, `lemma-regular-gorenstein`), proves exactly the required injective-dimension assertion before discussing Gorenstein rings: regular-local finite global dimension, then Ext vanishing, then the injective-amplitude criterion. Thus no definition of Gorenstein or of dualizing complex is needed to state or prove this item.

The finite-global-dimension and projective-dimension/Ext facts already exist as `lem-weil-pbc-regular-local-finite-gl-dim` and `lem-weil-pbc-projective-dimension-ext-characterization`. I reused them. Instead of creating a general injective-amplitude node, I wrote out the kernel argument in 0A5T: injectivity of an existing resolution term supplies an extension, the explicit Ext cocycle/boundary comparison supplies a correction, and Baer's criterion shows that the last kernel is injective. This is a direct calculation with two already cited statements; it does not hide a new unproved dimension-shifting or comparison lemma. The bounded complex and its quasi-isomorphism are written out, including dimension zero.

Read the chapter and unit records (`sec-trace-formula`, `sk-i-curve-zero`) and the current blueprint ancestor `lem-trf-local-term-locality`. The item's existing ancestry identifies this as a generic algebraic auxiliary input for the regular-local Cohen-presentation step in complete-local coherent duality, not a replacement of the geometric unit route. The blueprint ancestry and its precise place are preserved; `same_as` remains `[]`. Whole-blueprint searches for injective dimension, bounded injective complexes, injective resolutions and regular local rings found no blueprint node asserting this item. Whole-DAG searches by 0AWX, 0A5T, injective-amplitude, bounded resolutions, and the key notions found the reused tools rather than a duplicate of the item. No node was created.

Mathlib searches were actually run with `msearch.py` and their command-log records appended to the existing search records. Both phrasings of the generic bounded-resolution query and the regular-local query return Ext-defined dimension classes and generic resolutions; Loogle gives the dimension predicates and localization/Baer APIs; grep identifies the relevant dimension and resolution files. I read `CategoryTheory/Abelian/Injective/Dimension.lean` and `CategoryTheory/Abelian/Injective/Resolution.lean`. An Ext-defined dimension predicate does not itself construct the bounded injective complex required here. None of the hits states finite self-injective dimension of a regular local ring. The existing searches in the imported node were retained, not rewritten as new searches.

## Not duplicates

No new node was created, so there are no new/existing same-tag pairs. The item reuses existing nodes rather than duplicating the regular-local global-dimension theorem, projective-dimension/Ext characterization, enough injectives, resolution existence, resolution computation of Ext, or Baer's criterion.

## Review by Q84

I read Stacks 0AWX (`dualizing.tex`, `lemma-regular-gorenstein`) in full, the definition 0A5S and proof of 0A5T (`more-algebra.tex`, `definition-injective-dimension`, `lemma-injective-amplitude`), and the actual statements of every node cited below. No new node requires a separate source check.

Step 1 takes the all-modules projective-resolution bound from `lem-weil-pbc-regular-local-finite-gl-dim`; its statement really covers every module, and its regular-local hypothesis is exactly the item's. I checked its source 00O7 (`algebra.tex`, `proposition-regular-finite-gl-dim`, last assertion). The bound is a finite nonnegative integer, so its use at n=d in the next step is legitimate.

Step 2 takes implication (1) to (2), including all degrees i>=d+1, from `lem-weil-pbc-projective-dimension-ext-characterization`. I checked 065R (`algebra.tex`, `lemma-projective-dimension-ext`). Its first module is arbitrary and its second module can be A. This is important: the proof needs the bound for A/T and does not erroneously replace the all-modules theorem by the finite-module Ext-vanishing node. `def-pc-ext` provides the derived-category convention. No negative Ext degree occurs in this proof.

Step 3 uses the abelian and enough-injectives assertion of `lem-weil-pbc-ring-modules-enough-injectives` and only clause (1) of `lem-weil-pbc-left-exact-injective-resolution-degree-zero`. I read 01DD (`more-algebra.tex`, `lemma-injectives-modules`) and 013K (`derived.tex`, `lemma-injective-resolutions-exist`). The latter node's statement supplies the nonnegative support, augmentation, and exactness, rather than merely defining what a resolution is. Defining J as the kernel is elementary module algebra. For d=0, exactness says A maps isomorphically onto J; no differential in degree -1 is needed.

Step 4 uses the extension property actually stated in `def-sp-injective-resolutions` for the inclusion T into A and the injective term I^d. The statement of `lem-weil-pbc-ext-via-injective-resolution`, checked against 06XR (`derived.tex`, `lemma-compute-ext-resolutions`), explicitly computes Ext as cocycles modulo boundaries, with differential given by postcomposition. I verified the quotient factorization h, the cocycle identity using the surjectivity of pi, and the boundary g. Thus d(f-g pi)=0 and the correction vanishes on T. This proves the ideal-extension condition without any unquoted Ext^1 dimension-shifting theorem. The comparison applies in degree d+1>=1 to the resolution of A obtained in step 3.

Step 5 uses exactly the ideal-extension implication of `lem-sf-baer-criterion`. I read 0AVF (`more-algebra.tex`, `lemma-characterize-injective-bis`) and checked that the DAG statement gives this implication, not only an Ext reformulation. A is commutative as required by that node, J is an A-module, and all objects live in the same module universe. This establishes injectivity of the final term.

Step 6 uses only the existing definitions of injectivity and derived localization, along with earlier results. I checked the corestriction of the last differential, the square-zero relation, the top cohomology J/im(d)=0 when d>0, and the degree-zero augmentation. All other terms are original injectives or zero, which is injective directly from the extension definition. The quasi-isomorphism therefore becomes the required isomorphism in D(A). For a field (d=0), the construction is J[0] with A isomorphic to J; for d=1, it is I^0 to J in degrees 0 and 1. These cover the truncation boundary cases. The ideal tests T=0 and T=A cause no problem: the quotient map or its target is zero as appropriate, and the same formulas apply. A zero ring is excluded by the usual regular-local definition, which requires a local ring with maximal ideal; nothing uses it as an illicit extra case.

I checked delivery-errors B through E: every object in the retained item is introduced; TeX escapes are unchanged and written once; source places name actual tags and labels; no new statement-only node or unsupported leaf is introduced; every non-elementary input is a cited node and all quotes are verbatim; no proof of a cited node is used for a stronger conclusion; no relabelled clause or circular input was introduced; the route-tool declarations explain the generic off-unit uses; and every step is under 2000 characters. The central correction is explicit, not an unspecified transport or compatibility. I retained the original statement and blueprint fields. All changes are confined to the sandbox and no Lean or build command was run.

## Unfinished work

None for this one-level split. Its cited open nodes remain independent DAG items; this delivery does not claim their Lean proofs are finished.
