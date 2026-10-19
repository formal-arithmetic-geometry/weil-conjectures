# Worker report: lem-amb-etale-sum-stalks

## Files written

- dag/nodes/sec-smooth-purity/lem-amb-etale-sum-stalks.json: statement, split into five proof steps; no Mathlib match for the whole assertion.
- citations.json: verbatim statement quotations for every step citation.
- No new nodes; zero new Mathlib leaves. Existing Mathlib leaves supply sheafification on stalks, module sheafification, etale composition/cancellation, stalks and the colimit universal property.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 checkout by blueprint id, by stalk/shriek and sum/stalk patterns, and inspected SixFunctors/Etale/LowerShriek/EtaleMap.lean. Its introductory prose states the formula, but its declarations construct etaleLowerShriek, its adjunction, exactness, and preservation of injectives, not the stalk isomorphism with its germ clause. The finite-etale and open-immersion comparison files only address special cases. No exact complete project declaration was found. The upstream master checkout is reference only.

## WANTED

None. All literature used is present.

## Findings and changes

The imported statement is correct as written; there is no STATEMENT-DISPUTED correction. Its hypotheses allow an arbitrary commutative ring and an arbitrary etale morphism; separatedness, finite type and a finite coefficient ring are unnecessary. The original node had no proof. I expanded the two regrouping equalities in Stacks Tag 0710 into explicit inverse maps on germs rather than introducing a new lemma restating the formula. The item is not itself a Mathlib leaf: the six newly run msearch queries are appended exactly, including LeanSearch's unavailable result. LeanFinder returned affine tilde stalks, free sheaves and generic point-fibre definitions, not slice extension by zero with the geometric indexing and section formula. Loogle and both source greps returned no hits.

I read the chapter and unit records. This is the auxiliary stalk calculation requested by the first paragraph of lem-amb-etale-adjoint-locality; it does not change the compact-support base-change unit's coefficient typing or route. Blueprint searches for geometric stalk etale sum, stalk, jshriek, sum extension and 0710 found no other blueprint node stating the whole item. The ancestor is lem-amb-etale-adjoint-locality and the existing exact provenance sentence is retained. DAG searches by 03S5/0710 and sheafification/stalk, and opening the candidate statements, supplied the existing nodes. No new node, duplicate, clause-node or unsplit proof sketch is introduced.

## Unfinished work

None for the one-level split. The second reader must review and deliver; this worker does not push.

## Review by NV

I read etale-cohomology.tex Tag 03S5, proposition-describe-jshriek, including its final formula on (V, v, phi, s), and sites-modules.tex Tag 0710, lemma-stalk-j-shriek, including its proof. The former gives exactly the lifts Spec Omega to U of the fixed geometric point, not just the image points in the scheme fibre. The latter works for modules over a ringed site, and its proof takes the stalk of the sheafified direct-sum presheaf and regroups by the value of the point functor on phi. Our maps e and i explicitly implement this regrouping. I also read Tag 03CY, lemma-sheafification-presheaf-modules, and morphisms.tex Tags 02GN, lemma-composition-etale, and 02GW, lemma-etale-permanence. These are the substantive supporting results, all already represented by cited nodes.

In step 1, def-weil-pbc-etale-sum-extension gives precisely P and its restrictions. def-weil-presheaf-modules-sheafification explicitly takes abelian sheafification and gives its linear unit. lem-weil-pbc-sheafification-geometric-stalk gives the isomorphism induced by that unit for a geometric point on the small etale site; it is not applied to a topological-space or pro-etale stalk. def-weil-pbc-category-colimit supplies the cocone convention and universal property. I explicitly checked why the resulting inverse is A-linear. The small presentation/universe is fixed before taking these colimits, so no large diagram is passed to a small-colimit result.

In step 2, clause (3) of lem-weil-pbc-etale-composition-cancellation says every X-map between schemes etale over X is etale. Both V and U meet that hypothesis; consequently (V,a) really is an object where F is evaluated. The extension definition supplies restriction into the ah-summand. def-weil-pbc-geometric-stalks and the colimit definition give the germ equality under a pointed refinement: (ah)v'=av. The finite-sum construction is A-linear and involves no infinite summation.

In step 3, clause (2) of the same composition/cancellation node applies to W to U to X, so every representative of a stalk at z is also a legitimate pointed neighbourhood over X. The cited extension definition sends a summand b to bh under every U-refinement. This verifies the cocone equation before descending to F_z by the two cited colimit/stalk definitions. No assertion about a hidden cofinal subcategory or uniqueness of etale lifts is used.

Step 4 is elementary from those definitions: on each F(W,b) coprojection the first composite is the stated summand inclusion; on each F(V,a) summand the second composite is its original class, with exactly the same pointed neighbourhood. The universal property, explicitly stated in the cited colimit node, extends these equalities to the stalks. This avoids an uncited theorem about commuting a filtered colimit with a varying direct sum. Step 5 checks the generator formula and naturality by writing both images as the germ of alpha(s), then uses the same universal property; module-sheafification functoriality is explicit in the cited definition. Each node used in every step was opened, and citations.json quotes its statement, not its proof.

For edge cases I checked U empty, an empty set of lifts, F zero, the zero coefficient ring, u the identity, an open immersion, and an infinite disjoint union of copies of X. The inverse-map equations still hold in all cases. In particular if there are no lifts, any pointed V has no map V to U (such a map would produce av), so P(V)=0; and infinitely many lifts require only finitely supported sums, not a finiteness hypothesis on u. Nonseparated etale u is allowed: the proof never uses a closed diagonal or injectivity of maps of sections. I corrected the planned colimit argument to use mutually inverse cocones, so no new finite-refinement lemma, generic slice-stalk formula, or restatement of the item is needed. There were no changes to the statement or its statement dependencies, no external downloads, no Lean writing and no compilation.

## Second reading by NV

- Item statement: checked against etale-cohomology.tex Tag 03S5 (proposition-describe-jshriek) and sites-modules.tex Tag 0710 (lemma-stalk-j-shriek), hypothesis by hypothesis; the arbitrary etale map, commutative coefficient ring, geometric point, direct-sum indexing, and germ clause agree, including empty and zero cases.
- Step 1: checked each cited definition and lemma statement; the presheaf colimit, module sheafification, and stalk invariance under abelian sheafification provide exactly the claimed linear map. The fixed small presentation addresses colimit size; no unsupported fact is used.
- Step 2: checked composition/cancellation, sum-extension restrictions, geometric-stalk colimit, and cocone compatibility. The refinement equation $(ah)\\bar v' = a\\bar v$ is explicit, so the map is well-defined and finite-sum linear.
- Step 3: checked the cited statements for a pointed neighbourhood over $U$; composition gives an etale neighbourhood over $X$, and restriction sends the $b$-summand to the $bh$-summand. The cocone and induced map are stated rather than inferred from a cited proof.
- Step 4: checked both composites on every stalk representative and coprojection against the colimit universal property. It is elementary from the cited definitions and does not assume filtered colimits commute with variable direct sums.
- Step 5: checked the generator formula and naturality against the sum-extension, stalk, colimit, and module-sheafification statements. Both sides send a generator to the same germ, and finite sums plus the universal property complete the argument.
- New nodes: none; B1--B7 and duplicate/Mathlib-node checks were vacuous. Existing dependencies were searched by tag and keywords and their quoted statements in citations.json were checked verbatim.
- Edge cases: checked empty $U$, no lifts, zero $F$, zero coefficient ring, identity and open-immersion maps, infinite disjoint unions (finite-support sums), and nonseparated etale maps; every construction and inverse identity remains valid.
- Changes made: none to the item, proof, dependencies, or citations; this section records the independent second reading required by the delivery contract.
