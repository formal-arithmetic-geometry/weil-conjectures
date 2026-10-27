# Stage-1 delivery: lem-sfb-trait-line-section-generic-germs-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-line-section-generic-germs-extension.json`: statement, split into six steps; not a Mathlib leaf. No new nodes, no Mathlib leaves added.
- `citations.json`: eleven step/node pairs, quoting the live statements verbatim.
- `report.md`: this report. The search command generated `searches.jsonl`; every new search record in the item is copied from that log.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, trait line sections and integral generic germs found no declaration of the whole item. Related Hartogs declarations and existing quasi-coherent localization declarations do not state the item. The latter are used through their existing DAG nodes, rather than attached as a proof of the whole item.

## WANTED

None. The proof uses available Stacks sources and existing DAG statements.

## Corrections and route

The statement is retained word for word. The imported statement is true, including its arbitrary-open injectivity, auxiliary open W, two depth bounds, and empty-scheme clauses. There was no previous sandbox item, proof or report to discard. The source's tag 0E9I supplies extension only after establishing depth; it is not itself a proof of the curve depth bound or integral-germ spreading.

The existing reviewed `lem-sfb-flat-curve-line-depth` supplies Noetherianity, uniformizer regularity and depth at closed special points. Its global injectivity assertion is NOT applied to an arbitrary open, since such an open need not satisfy the finite-type hypothesis. Step 2 proves the stronger restriction statement affine locally instead. Likewise the existing Hartogs node requires finite sections on every affine open. Step 6 applies it to the structure sheaf on trivializing affine charts, where those finiteness conditions are tautological, rather than silently adding a theorem about finite sections of every line bundle.

The blueprint ancestor command returns null, as in the inherited item. Its long recorded provenance is kept, with the precise old nodal-pullback steps being realized. I read the current latest blueprint's `sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md` and the current `det-pd-dual-stratum-extension.proof.md`; the old identifier det-thm-sf-ctf-stability-direct-images survives as a reference, not as a separate current proof file. Searches across blueprint nodes for Hartogs, depth and line section found no replacement statement. The unit's alteration route is preserved: this is only the local line-section extension tool below its marked-curve rigidity input. No chapter/unit record is modified.

The three off-unit generic tools are declared in split_report.tool_uses: generic-fibre affine ring models; affine quasi-coherent basic-open localization; and depth-two Hartogs restriction. These supply scheme-local operations, not an alternative to the unit route. Definitions are used as notions. No new tool_uses field is set by this delivery.

## Not duplicates

No new nodes. In particular, I reused rather than duplicated `lem-sfb-flat-curve-line-depth`, `lem-sbc-depth-two-hartogs-restriction`, and `lem-weil-pbc-affine-module-basic-open-localization`. The first overlaps two clauses of this item, but does not extend sections from integral generic germs. The Hartogs node assumes depth and does not derive it from a reduced curve fibre.

## Review by Q129

I read delivery-errors B--E in both copies, the full statements of all eight distinct cited nodes, divisors.tex lemma-depth-2-hartog (Tag 0E9I), algebra.tex lemma-criterion-reduced (031R) and lemma-apply-grothendieck (0337), schemes.tex lemma-spec-sheaves (01HV), and sheaves.tex section-stalks (0078). I also read the existing source-library quasi-coherent localization declarations at Modules/Tilde.lean:112 and :150, and the Hartogs declaration and its hypotheses in DepthTwoHartogsRestriction.lean. I did not compile or write Lean.

Step 1 takes precisely Noetherianity, injectivity of multiplication by the uniformizer on stalks, and depth at CLOSED special points from flat-curve-line-depth, with m=1 for M and m=0 for O. The DVR, flatness, finite type and reduced pure-one-dimensional special fibre hypotheses match exactly. It does not assume a regular, integral or normal total space.

Step 2 uses the affine-generic-ring node for the actual localization restriction, whose reduced-special-fibre hypothesis is present. Basic-open localization clause (2) kills a section by a power of pi. Step 1 cancels that power on stalks. The module-stalk definition explicitly says equality of germs becomes equality after shrinking; hence sheaf uniqueness finishes, and arbitrary affine covers give arbitrary-open injectivity. No affine-intersection or quasi-compactness assumption on V is needed.

Step 3 uses the invertible-module definition for local rank-one trivializations, basic-open localization clause (1) for a numerator a and denominator pi^n, and module-stalk for representatives and equality on a neighbourhood. I wrote out the formerly implicit denominator argument: pi^n b_eta-a_eta maps to zero after inverting pi, so a power of pi kills it, and stalk regularity cancels it. This is the elementary definition of localization equality. Represent b_eta and then shrink so the actual equation holds, rather than claiming an unspecified extension from a germ. Compatibility with the generic fibre uses the same affine-local localization model as Step 2.

Step 4 uses no extra theorem: equality on each overlap follows from the already proved arbitrary-open injectivity, and the sheaf gluing axiom constructs s_W. Intersections need not be affine. Integral lifts at generic points are unique by stalk regularity.

Step 5 cites the two dimension definitions and gives the short chain argument itself. A non-generic point in a pure one-dimensional component has zero-dimensional closure; a strict further specialization would produce a length-two chain. Thus it is closed in the special fibre, exactly the condition in Step 1. The ambient scheme may be nonseparated or reducible. The T_0 property used to distinguish closures is part of the scheme topology; 01IS is recorded as its source. This is not an unproved dimension formula or a normality criterion.

Step 6 uses invertible-module solely to choose the bases and Hartogs restriction solely for the structure sheaf. I checked each hypothesis: local Noetherianity is inherited from Y, the structure sheaf is quasi-coherent, its sections on every affine open and all its stalks are rank-one modules over themselves, and boundary depths were proved in Step 5. Evaluating the unit isomorphism extends the coefficient c_T, then the chosen basis gives a local section of M. Their overlaps agree by Step 2 on the generic fibre, as do the resulting section and s_U. This also proves uniqueness. The statement's M-depth bound was already supplied in Step 5, even though only the ring-depth bound is needed for this form of Hartogs.

I tested the empty scheme, an empty special fibre (then U=Y), U=Y, the zero section, and Y=Spec R[t] with the trivial line bundle. The forbidden pole 1/pi fails the integral-germ hypothesis. A reducible example R[x,y]/(xy) is flat with reduced curve special fibre and has persistent generic singularities; the argument still uses only pi-regularity and closed-special-point depth. The example R[x,y]/(xy-pi) has a nodal special fibre and satisfies the same input. The generic point of the special fibre in Spec R[t] has depth one, so it was essential to spread there before Hartogs, not to demand depth two everywhere in the special fibre. Removing reducedness, flatness or the curve dimension assumption would invalidate inputs; none is removed.

I checked that proof_deps is exactly the union of uses, all cited nodes are existing and unmerged, every citation quote is a literal substring of its statement, and each new search record matches searches.jsonl. Search results concern generic-function-field injectivity, local fraction representations or affine denominators; none states this extension theorem, and a second semantic phrasing was tried. No elementary fact was promoted to a node, no clause was merely renamed, and no new node or source proof was hidden inline. All six steps are below 1000 characters, hence below the 2000-character long-step threshold. Every non-elementary step cites the result carrying its substantive argument.

The server review_split check passed before this report was written. The required complete delivery dry run and push follow.

## Unfinished work

None in the authorized stage-1 split. Existing dependency nodes retain their own proof obligations.
