## Files written

- `dag/nodes/sec-six-functors/lem-sf-native-adic-mayer-vietoris-triangle.json`: existing statement node, now split into eight proof steps; statement and statement dependencies unchanged. Retained all inherited provenance, source and Mathlib searches, and added the five searches actually run for Q32.
- `citations.json`: 27 verbatim cited-statement records, one for each step/node pair.
- No new nodes; no new Mathlib leaves. The item is not a Mathlib leaf: its closest search hits are free abelian sheaf Mayer–Vietoris squares, Ext-defined sheaf cohomology, the generic short-exact-complex triangle, and structure-sheaf restriction adjunctions. None states the derived triangle for these native pro-etale coefficient modules.
- `report.md`: this report. `prepare.py` is sandbox-only preparation, not a project tool or a delivery file.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, the item id, adic/Mayer–Vietoris terminology, and triangle declarations. Read the native files `SixFunctors/ProEtale/Adic/MayerVietoris.lean` and `LowerStar.lean:175–243`, and `AlgebraicGeometry/DerivedMayerVietorisTriangle.lean:74–152`.

`AlgebraicGeometry.ProEtale.finiteLowerStar_of_openCover` states a conditional bounded-constructibility consequence, with additional hypotheses, and does not state this triangle or its two maps. `AlgebraicGeometry.ProEtale.isIso_Q_map_unit_of_isZero` states a supported-object consequence. `AlgebraicGeometry.schemeDerived_mayerVietoris_triangle` concerns ordinary structure-sheaf modules on the Zariski site, with qcqs and quasi-coherence hypotheses. None is an exact attachment. The item has no upstream declaration recorded in its node.

## WANTED

None. All proof inputs were available in the local Stacks source, the existing DAG, or the project source.

## Problems in the imported item or brief

The item was statement-only, with no proof steps. Its statement is true as written and is unchanged. The native source named in its source field proves the finiteness consequence by a cone argument rather than declaring the displayed triangle. I supply the triangle by the injective-term proof of Stacks Tag 08BV (`cohomology.tex`, `lemma-exact-sequence-j-star`), adapted explicitly to the pro-etale ringed site and evaluated after ordinary direct image. Because that adaptation is written here and not literally a theorem of the ringed-space source, `proof_origin.by` is `agent`.

The localization node's constant-ring comparison is not a statement about the native sheaf B. Step 1 uses only its site equivalence, and proves B_T restricted to Z equals B_Z by evaluating the very same continuous functions on the same underlying space. This avoids identifying the native coefficient ring with a discrete constant sheaf.

The source label in `lem-pur-kinjective-restrict-localized` says `lemma-restriction-K-injective`; the actual Stacks label in the source is `lemma-restrict-K-injective-to-open`, Tag 08FI. The statement itself is the needed localized K-injectivity assertion. The proof-step source uses the actual label; the existing cited node was not edited.

The item's inherited blueprint ancestor is null. `tools/blueprint_refs.py ancestor` confirms this. Retained the inherited provenance and via chain, and explained the relevant two-open Cech step in `split_report.blueprint`; no ancestor was invented. The item is not the key node of `sk-thm-sf-package`, so no unit realization record was edited. The chapter and unit routes are unchanged. The supplied brief's stage-1-only and sandbox-only instructions govern over historical stage-2 settings in SETUP.

## Unfinished work

None for this one-level stage-1 split. No Lean was written and no compiler, Lake, build, or local project validator was run. The delivery dry run and push are the authorized final checks.

## Not duplicates

No new nodes were created, hence there are no new/existing same-tag pairs to distinguish. The related ringed-space and qcqs structure-sheaf triangles were read and reused only through their existing generic ingredients, not renamed as new native nodes. Whole-DAG and whole-blueprint searches for Mayer–Vietoris, K-injectivity, restriction and the corresponding Stacks tags located the existing tools cited by the proof. `blueprint_refs.py search 'Mayer'` and `search 'Mayer Vietoris'` found no imported blueprint statement equal to this native-coefficient triangle.

## Review by Q32

I read the worker brief, the stage-1 rules, the three blueprint levels in SETUP, GOAL, the chapter and unit records, and both copies of delivery-errors B–E. I read the item against its two native Lean sources and the Stacks proof of 08BV, including the sectionwise short exact sequence. For the ingredients I read Stacks 079P in `injectives.tex`, 093X and 08FI in `sites-cohomology.tex`, and 0152, 070I, 070Y, 070K and the derived adjunction discussion in `derived.tex`. There are no new-node sources to review. I opened every cited DAG statement; the citation file copies actual text from those statements.

Step 1 uses the weakly-etale localization statement for its site equivalence, the ringed-site restriction statement for exactness, and the localized-ringed-site definition for relocalization. The coefficient equality is verified directly and does not borrow the lemma's constant-coefficient clause. A common enlarged universe accommodates the chosen small representatives, coefficients and modules, so the localization theorems apply without a size change in the mathematical objects.

Step 2 writes out the ordinary open adjunction: extension of a map on the localized site is restriction to P times_T Z followed by that map, and evaluation on objects already over Z is its inverse. These operations are inverse by naturality. The localized-site and module-sheaf definitions give their section values and semilinearity. This is a short explicit calculation, marked elementary, and not a hidden unproved adjunction theorem.

Step 3 takes exactly what `prop-pur-kinjective-resolutions-exist` states: an unbounded K-injective resolution whose terms are injective. `lem-pur-kinjective-restrict-localized` gives K-injectivity on each of the three slices, with its zero-map condition verified sectionwise. Its coefficient-universe convention is met by using the common enlarged universe for the category presentation as well. Exact restriction preserves the quasi-isomorphism. This distinguishes K-injectivity from mere termwise injectivity for unbounded complexes.

Step 4 is the mathematical exactness argument, not a citation to a desired Mayer–Vietoris theorem. Weakly-etale base change puts P times_S T and its open restrictions in the correct small pro-etale site. I also cite the existing Mathlib leaf `lem-weil-pbc-open-immersion-base-change` for openness of the pulled-back inclusions; its statement covers arbitrary base change, and I read its source Stacks 01JY in `schemes.tex`. This citation was added during the final review rather than leaving open-immersion stability implicit. Two open immersions covering a scheme form a pro-etale cover: on every affine target object their inverse images have a finite affine refinement covering it. Sheaf gluing gives injectivity and equality of the kernel with the image. The injective-mono restriction node applies to P_W into P_U, a monomorphism between actual objects of T_proet, with I^n injective there. It gives a lift x of any overlap section c, so (x,0) maps to c. Thus exactness is proved sectionwise, before sheafification. The module-category statement gives sectionwise kernels and sheafified cokernels, so the asserted sequence of complexes is degreewise short exact. No claim that g_* preserves arbitrary short exact sequences is used.

Step 5 uses the total derived existence/computation statement, along with the stated derived-functor normalization, to compute the four objects on precisely the resolutions already chosen. The source module categories have the required K-injective resolutions by the same small-site theorem. Direct image is additive sectionwise. The finite sum is preserved by the additive localization. No composition theorem requiring a flat pullback along arbitrary g is invoked.

Step 6 checks the first map rather than merely naming a comparison. The open restriction functor is exact and has the right adjoint constructed in step 2; hence the cited right-adjoint preservation lemma really applies to j_* and I_Z. The K-injective Hom bijection on both sides identifies the derived open adjunction with the degreewise one. The identity on I_Z transposes to the restriction unit. Naturality of the derived comparison computes its Rg_* image on the K-injective complexes I and j_*I_Z. Ordinary composite direct images agree sectionwise, including the coefficient action, so the comparison used here is the one determined by this same model. This does not assume that arbitrary g_* preserves K-injectives.

Step 7 repeats this calculation only for the nested open W into U or V. The cited right-adjoint and Hom-bijection statements have precisely the same hypotheses there. Associativity of precomposition identifies both overlap targets; the difference is literally x restricted to W minus y restricted to W. Composing with the diagonal restriction is zero, with no sign change hidden in a derived comparison.

Step 8 invokes the existing arbitrary-complex short-exact-sequence triangle, not the single-degree sheaf variant. Its abelian-category hypothesis follows from the module-category statement on the small site S_proet. The first two arrows are the localized maps from the short exact sequence already constructed, so transporting the triangle gives exactly the requested arrows. The boundary is transported with the shifted first-object isomorphism; no claim of uniqueness of an arbitrary cone is needed.

I checked the empty scheme, U empty, V empty, U=V=T, disjoint opens, the zero complex, g the identity, and a general unbounded complex. For U=V=T the sequence is 0 to I by the diagonal into I direct-sum I by (1,-1) into I to 0. For one empty open it reduces to an identity and a zero term; for disjoint opens the overlap term vanishes and gluing gives the direct sum. The empty-site sheaf condition makes every section at the empty object zero. None of these tests requires a Noetherian hypothesis, a bound on cohomology, or constructibility. The image of an open in arbitrary g need not be open in S; the proof uses only its base change to each site object P, so it never assumes otherwise.

Against B–E: no statement-only new node contains a hidden proof, no clause of the item was repackaged as a lemma, and no duplicate node was created. Every non-elementary input is an existing cited statement, and all remaining sectionwise maps and gluing arguments are written out. All eight steps are shorter than 2000 characters. Search entries were retained or copied from actual Q32 command results; services returned successfully, and no unavailable service was recorded as absence. The five declared tool uses are generic localization, restriction, injective and derived-functor tools, and replace no unit route. No prohibited SGA source is used. I corrected the potentially misleading coefficient and source-label interpretations described above, without changing any statement or any other node.
