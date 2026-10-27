# Worker report: Q85

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-relative-h1-immersion-universal-koszul.json`: the item, statement unchanged, eight complete proof steps, status split; Mathlib searches found no exact theorem.
- `dag/nodes/sec-six-functors-basics/lem-sfb-h1-flat-quotient-ambient-flat-neighbourhood.json`: new statement-only lemma, Stacks 063V(1) in affine principal-neighbourhood form; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-koszul-h1-flat-quotient-base-change-surjective.json`: new statement-only lemma, Stacks 063Q including its canonical cycle map; no Mathlib match.
- `citations.json`: every step/use pair, with the cited statement copied verbatim. `searches.jsonl` and the saved search outputs record the actual msearch invocations.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by H1 regularity, Koszul regularity, and regular immersions. The existing project has the Koszul and H1 regular sequence definitions, flat Koszul base change, and regular-to-Koszul theorems; none is the item or either new input. A declaration containing sorry was not treated as an attachment. `lean/Sheaf/` was also searched for the proposed new inputs.

## Literature wanted

None. Read `literature/stacks-project/divisors.tex`, labels `lemma-flat-relative-H1-regular` (063V), `definition-relative-H1-regular-immersion` (063S), `lemma-relative-regular-immersion-flat-in-neighbourhood` (063U), `lemma-relative-regular-immersion` (063R), `lemma-regular-ideal-sheaf-scheme` (063G), and `lemma-fibre-quasi-regular` (063W); and `more-algebra.tex`, labels `lemma-base-change-H1-regular` (063Q) and `lemma-relative-regular-immersion-algebra` (0CEP). Tags were verified against tags/tags. The current blueprint is `literature/blueprint/latest/`; its direct-images proof, headed `of = det-thm-sf-ctf-stability-direct-images`, was read together with the unit and chapter records.

## Problems found and corrections

The item itself is true and needs no statement correction. Its source is 063V(2) with the weaker but faithful Koszul consequence made explicit. In particular the ambient scheme need not initially be flat. A naive use of the existing relative-regular-equations theorem would miss that hypothesis; step 2 now obtains it from the genuinely separate first assertion of 063V. The source's second assertion is not moved wholesale into a new lemma.

The inherited blueprint ancestor is null. Running `tools/blueprint_refs.py ancestor lem-sfb-relative-h1-immersion-universal-koszul` prints `blueprint.from.node = None`. Its long `from.place` and `via` trace the intended direct-image/alteration and relative-Hilbert route, and are retained. The new nodes extend that same ancestry with the item in front of `via`, rather than inventing an imported ancestor. Searches of the entire blueprint for H1, Koszul, 063V, 063Q, and flat neighbourhood found no blueprint statement of either new lemma. The current latest blueprint's direct-images assembly is shorter than the inherited supporting chain; no chapter or unit record was changed.

The original Mathlib searches supplied with the item are preserved. New searches for the item and both new nodes used all four msearch modes, and a second semantic formulation for each. All returned successfully. The ambient-flatness hits assume smoothness or already-given flatness, or state localization/descent. The first-homology hits concern Kahler differentials and naive cotangent homology, which do not state Koszul H1. Read Mathlib `RingTheory/Regular/Flat.lean` (especially 34–60), `RegularSequence.lean` (21), and `Extension/Cotangent/BaseChange.lean` (142–190): none is a one-line specialization of either input. Saved full result files were read, not just hit counts.

## Unfinished work

None at the requested level: the two new inputs are deliberately unsplit statements, and the item's proof uses their statements. No Lean was written, and no compiler, Lake, build, or local DAG/preflight checker was run.

## Not duplicates

lem-sfb-h1-flat-quotient-ambient-flat-neighbourhood vs lem-sfb-relative-h1-immersion-universal-koszul: the new algebra statement asserts only existence of an ambient flat principal neighbourhood (063V(1)); the item asserts positive Koszul acyclicity after every parameter base change (063V(2)). Ambient flatness is not a clause of the item's statement and does not itself prove its conclusion.

lem-sfb-h1-flat-quotient-ambient-flat-neighbourhood vs lem-pur-relative-regular-equations-base-change: the existing theorem assumes an already flat ambient algebra and an already regular sequence; the new lemma derives ambient flatness from H1 regularity and flatness of the quotient, and asserts no base-change regularity.

lem-sfb-h1-flat-quotient-ambient-flat-neighbourhood vs lem-trf-flat-lci-presentation-base-change: the latter starts with Noetherian polynomial ambient charts and regular equations and includes cotangent/determinant data; it does not provide the missing flat ambient neighbourhood for a general finitely presented ambient algebra.

lem-sfb-koszul-h1-flat-quotient-base-change-surjective vs lem-pur-quasi-regular-flat-quotient-base-change: 063Q states a surjection on possibly nonzero first Koszul homology, whereas 0CEP(1) preserves the associated-graded polynomial isomorphism of quasi-regular sequences. Neither gives the other as an elementary specialization. No other live node has source tag 063Q. DAG keyword searches and blueprint searches were made before creating either node.

## Review by Q85

I checked sections B through E of delivery-errors with the actual node statements and Stacks source open. Both new nodes introduce all rings, maps, sequences, ideals, and module hypotheses; definitions are cited for precisely those notions. They contain no proof, no proof dependency, and no proof sketch in the statement. Their sources use the tag and source label. The item keeps every original hypothesis and conclusion, including lack of ambient/base-change flatness and all non-Noetherian cases.

For step 1 I checked that the immersion definition contains the affine quotient description and the locally-finite-presentation definition supplies a finitely presented affine neighbourhood. Principal restrictions have the written presentation with an extra inverse variable. The Koszul scalar-extension isomorphism and exactness of localization identify the complexes at the restricted rings and preserve the stated H1 vanishing. The affine flatness criterion explicitly applies to all pairs of affines, so gives flatness of the quotient algebra from flatness of the source; this is not inferred from a definition of module flatness. The chart can be restricted around the fixed point, without assuming intersections of affine opens are affine.

For step 2 the new 063V(1) statement supplies exactly h outside Q and flatness of B_h. The localization-flatness lemma applies to both ambient modules and quotient modules, and the Koszul/localization statements preserve H1 regularity. Finite presentation is checked by the explicit presentation, so every later flat ambient hypothesis is now justified.

For step 3 the new 063Q statement is used only for its surjection, with A' the residue field and B/I flat over A. A zero source therefore gives zero H1 on the fibre, without claiming arbitrary homology commutes with nonflat base change. The fibre is finitely generated over a field, exactly the hypothesis of lem-wf-affine-noetherian-components. I checked the fibre prime by localization followed by quotient, not by confusing B/pB with the residue-field fibre.

For step 4 the localization-noetherian theorem is applied to F, already proved Noetherian. Exact localization and the Koszul scalar-extension isomorphism give H1 vanishing in the fibre local ring. The full statement of lem-per-h1-koszul-quasi-regular gives the polynomial-to-associated-graded isomorphism there. That is exactly the hypothesis of lem-pur-quasi-regular-noetherian-local, with a nonzero local ring and all elements in its maximal ideal. I deliberately did not cite lem-per-noetherian-local-koszul-criterion for H1 alone: its statement assumes all positive homology vanishes. This was an important potential C4 error avoided by using the two existing exact statements instead.

For step 5 I matched every hypothesis of lem-pur-flat-quotient-fiber-regular-sequence with steps 1–4. It asks for a finitely generated ideal, flat finitely presented ambient algebra, flat quotient, and a regular fibre-local ideal. Its statement provides a principal localization with a regular list generating the localized ideal. Quotient and ambient flatness survive this localization by the explicitly cited lemma. It does not require the new regular list to equal the initial H1-regular list.

For step 6 the relative-regular-equations node is used with exactly those new regular generators, flat ambient algebra of finite presentation, flat quotient, and an arbitrary ring A'. It only asserts regularity at primes containing the pulled-back ideal, and the proof only takes that conclusion at those primes. Regular-to-Koszul acyclicity is separately cited rather than assumed from the definition. Step 7 covers the other primes by the displayed exterior-wedge contraction and proves detection of zero modules by prime localization using the annihilator argument. Thus no assertion that a regular list remains regular on a zero quotient outside its vanishing locus is made. Localization-exactness and Koszul scalar extension are cited again for the homology comparison.

For step 8 the open fibre-product statement gives the actual neighbourhood in the pulled-back ambient scheme, the affine-spectra fibre-product statement gives its ring, and the quotient-tensor theorem gives the equations of its closed source. I wrote the tensor reassociation maps and their inverse, so this identification is compatible with the source map rather than merely an abstract ring isomorphism. The result applies point by point for every parameter base change, including the identity.

Small cases were checked. Empty sequence means I=0 and B is already flat by the quotient hypothesis; the flat-neighbourhood lemma allows h=1 and every Koszul complex is degree zero. If I is the unit ideal the flat-neighbourhood assertion is vacuous. If B or a pulled-back quotient is zero, there is no source point. For a nonflat parameter change take A=Z, B=Z[t], f=t and A'=F_2: the conclusion still gives the regular equation t. The ambient-flatness lemma is not claiming global flatness away from V(I). Its H1 hypothesis is essential: A=Z, B=Z[x]/(2x), f=x has A-flat quotient Z but nonflat ambient ring at (2,x); H1=Ann(x) is nonzero, so this example does not satisfy the lemma. For 063Q, the empty sequence gives the zero-to-zero map, and f=0 over a flat B makes the comparison visibly the scalar extension of a free degree-one module. The proof never adds flatness of A' or a Noetherian assumption on A.

All non-elementary uses are explicit nodes, with verbatim quotations in citations.json. The off-unit algebra and affine-scheme results are declared in split_report.tool_uses as generic tools supporting the source route; no top-level tool_uses field is set. None of the eight steps exceeds 2000 characters. The contraction, quotient tensor maps, principal-localization presentation and zero-detection argument are the routine elementary calculations inside those steps; no independent hidden geometric comparison is being left as “transport”. No SGA source is used. The two new nodes are acyclic leaves at this stage, so neither can depend back on the item.

Final content check: the first dry run passed at 570ffc6ebb3. Before pushing I made the affine chart argument more explicit: local generation and H1 vanishing imply their affine-module versions by the annihilator/localization argument, so no uncited affine-cohomology equivalence is being used. The citation set is unchanged. The first step is still below 2000 characters. The final dry run below checks this revised version.
