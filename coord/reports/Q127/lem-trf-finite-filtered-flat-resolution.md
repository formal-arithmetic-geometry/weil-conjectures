# Worker report

Item: lem-trf-finite-filtered-flat-resolution. Group: Q127. Stage 1 only.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-filtered-flat-resolution.json: retained and checked the inherited proof, set status split, and expanded the localization comparison into three explicit steps. The complete statement, source, existing blueprint ancestry, historical reviews and Lean metadata are retained.
- dag/nodes/sec-trace-formula/lem-trf-full-quotient-cylinder-localization.json: statement, Mathlib leaf; exact match CategoryTheory.Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders, Mathlib/CategoryTheory/Localization/OfQuotient.lean:78–90.
- citations.json: verbatim statement excerpts for every cited node in every numbered proof step.
- searches.jsonl: actual search-command results, retained without editing. The inherited Mathlib search history in the item was retained and the searches of this run appended.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item id, blueprint tag, finite_filtered_flat_resolution, filtered.flat.resolution and split.flat; no declaration states this item. Also checked the exact upstream master source for the id and declaration. Its inherited lean record concerns a later Sheaf module, not a closed declaration of the read-only slopmaster2 project. No compilation or Lean writing was performed. Searching the source for the new leaf's declaration found applications of the Mathlib criterion, not a project theorem stating the generic criterion.

## Sources and blueprint route

Read dag/chapters/sec-trace-formula.json and dag/units/sk-i-additivity.json. The unit is geometric localization trace additivity; this auxiliary item supplies the filtered tensor models used in lem-trf-filtered-operations-hom, rather than replacing the unit's geometric route. Read its parent's tensor-model steps and the current main-20261015 lem-trf-trace-triangle-compatibility text. The blueprint ancestor command returns lem-trf-trace-triangle-compatibility. Whole-blueprint searches for filtered flat, homotopy localization, cylinder, localization quotient, full essentially surjective, and localization cylinder found no node stating this item or the new criterion. No unit or chapter was changed.

Read Varshavsky §5.2.1(b): filtered tensor and Hom are referred to Illusie V §2. It does not itself assert this fixed-flag resolution theorem. As the inherited source record correctly says, the resolution proof is an agent adaptation, based on the ringed-site ingredients in Stacks, not an attribution of the theorem verbatim to Varshavsky. Read Stacks sites-modules.tex Tag 03EW (lemma-module-quotient-flat), Tag 03ER (definition-flat), Tag 03DB (lemma-limits-colimits), and Tag 03EO (lemma-internal-hom-adjoint-tensor); sites-cohomology.tex Tags 077J (lemma-resolution-by-direct-sums-extensions-by-zero), 06YQ (lemma-bounded-flat-K-flat), and 06YN (definition-K-flat); derived.tex Tags 0GSL (lemma-localization-subcategory), 05RG (lemma-construct-multiplicative-system), 05S1 (lemma-filtered-acyclic), 05S2 (definition-filtered-derived), 05RT (lemma-acyclic), and 013N (lemma-make-injective); homology.tex Tag 0117 (lemma-long-exact-sequence-cochain); categories.tex Tags 04VG (lemma-properties-left-localization) and 04VK (lemma-properties-right-localization); dga.tex Tags 09QJ (situation-ABC), 09QU (lemma-cone-homotopy), and 09QY (proposition-ABC-homotopy-category-triangulated). No SGA source is used.

WANTED: Illusie, Complexe cotangent et déformations I, V §2, for the filtered derived tensor construction motivating lem-trf-finite-filtered-flat-resolution. The explicit proof here is marked proof_origin.by = agent pending that reference.

## Not duplicates

lem-trf-full-quotient-cylinder-localization vs lem-weil-pbc-localization-universal-property: the existing node gives the universal property of a functor already assumed to be a localization; the new Mathlib criterion proves that a full essentially surjective functor is a localization from explicit cylinder witnesses.

lem-trf-full-quotient-cylinder-localization vs lem-weil-pbc-complex-mapping-cylinder-split-factorization: the latter constructs a particular cochain factorization with a split injection and homotopy equivalence; it does not give the generic quotient localization criterion.

lem-trf-full-quotient-cylinder-localization vs lem-weil-pbc-bounded-below-cochain-localization: the latter is an abelian bounded-below quasi-isomorphism localization theorem; the new criterion works for arbitrary categories and arbitrary morphism classes satisfying its stated cylinder hypothesis.

lem-trf-full-quotient-cylinder-localization vs lem-trf-filtered-cone-localization: that node concerns a triangulated localization of bounded-below filtered homotopy categories, not identification of a quotient functor as a localization.

lem-trf-full-quotient-cylinder-localization vs lem-coef-simplicial-localization-essential-image: the exact Mathlib name occurs only among that node's search results; its statement is essential surjectivity of a derived simplicial localization unit, not the general cylinder criterion.

The new node carries no Stacks tag, so there is no same-tag collision. Exact declaration-name, cylinder and full-quotient statement searches covered the whole DAG. It is not a clause of the item: it contains no ringed site, filtration, flatness, cochain bound, tensor, or model-resolution equivalence assertion.

## Review by Q127

I read all cited node statements, not merely their proof plans. The item has no statement discrepancy or extra hypothesis to repair. I checked the finite-flag construction on a one-point site with ring Z, a=b, M=0, and a nontrivial two-step flag. Covers are taken of filtration steps themselves, so the construction does not assume flat modules are projective or that a quotient splitting lifts. All lifting language is interpreted by epimorphic pullbacks in the abelian sheaf category, never by global surjectivity on sections.

Steps 1–3: def-weil-sheaf-of-modules-category explicitly states abelianness for a small site, which the item assumes. The functorial-flat-cover node states a flat epimorphism for every module sheaf, exactly what is applied to each F^jE and F^jT^n. The direct sum cover contains B_p, ensuring strict surjectivity even when the original flag is nonsplit. For p<a and p>b the bounds give respectively the whole object and zero. The filtered-subquotient node defines the actual steps and grades used. The cycle-pair pullback T^n projects epimorphically because of the induction's cycle epimorphism, and the maps x↦(x,0) supply the next cycle invariant. I checked the initial invariant at N+1 and the induction parameter N−n. Step 2 is elementary kernel/pullback arithmetic in this abelian category; its proof is written out.

Steps 4–5: the pair (0,z) forces acyclicity of every F^p kernel; strict surjectivity supplies the short exact sequences used. The cited long-exact-cohomology node has precisely the termwise short-exact hypothesis. The second application uses both F^pK and F^{p+1}K acyclic, after the strict graded kernel calculation, and thus proves every graded quasi-isomorphism rather than only an underlying quasi-isomorphism. No five-lemma or unexplained filtered exactness theorem is invoked.

Step 6: flatness is tensor exactness by def-pc-flat-sheaf-modules; the tensor-closed node explicitly supplies additivity. A finite sum of exact functors is exact by the finite kernel/image calculation written in the step. The bounded-above-flat-kflat-site statement then applies to P and every grade, since all vanish above the same N. Its source metadata elsewhere incorrectly says 06YS for bounded-above K-flatness; I used and read the actual Tag 06YQ without changing that other node.

Steps 7–8: the dg ABC node actually concludes triangulation from the three displayed hypotheses. The proof checks zero/sums, the shifted Hom differential and signs, and the cone splitting with boundary f[1]; all objects retain the fixed interval and bounded-above condition. The underlying category is small after a universe enlargement. Taking grades commutes with this direct-sum cone and filtered homotopy. The long-exact sequence gives closure of the graded-acyclic subcategory, and quasi-iso-cone-acyclic is applied to ordinary graded complexes in the abelian module category. The cone-system node states right calculus without requiring saturation or retract closure; that is exactly what step 9 needs.

Step 9: the right-fraction-dense-subcategory statement requires a full subcategory, the right calculus, and a denominator from that subcategory to every object. Fullness is by the defined split-flat homotopy subcategory, the calculus is step 8, and the denominators are steps 1–5. This is not the stronger unlocalized K-projective assertion. Its generic categorical proof is already an existing node; I created no duplicate.

Steps 10–11: I extracted the general cylinder criterion that the old 2320-character comparison step hid. I read the full Mathlib declaration at OfQuotient.lean:78–90 and also Precylinder at Cylinder.lean:51–61 and LeftHomotopy at LeftHomotopy.lean:45–51. The new node expands all their data; it is exactly the theorem, with no model-category axiom. For the actual quotient q, equality means filtered chain homotopy. I checked d²=0 for I(X), both section/projection identities, the contraction h(x,y,z)=(0,−z,0), and the H chain equation with sign f−g−kd−dk. The cylinder may extend the upper bound from N to N+1, which is permitted because bounded-above is existential; it does not change [a,b]. The quotient is full and object-surjective by definition, and it inverts homotopy equivalences. The new criterion therefore proves q is a localization. V⊂W follows grade by grade from the explicit homotopies. The localization universal-property node includes the natural-transformation clauses (not only objectwise factorization), so the two successive factorizations in step 11 identify the derived category as claimed.

Step 12: inclusion of intervals uses zero summands in the new grades, preserving the same filtered maps and W. The existing localization node's unique-lift clause gives the commuting square and coherent comparisons. No functorial choice of flat replacement is asserted or needed.

Step 13: the ringed-site-Grothendieck-abelian statement explicitly supplies all small colimits and exact filtered colimits. The countable sum is the filtered colimit over its small finite-subset poset, of finite direct sums of the given exact sequences. This proves its exactness and permits the graded quotient passage; W need not be bounded in cochain degrees.

Steps 14–16: tensor-closed states additivity and symmetry, and the tensor-complex node states the direct-sum convention and its Koszul differential. Flatness makes tensoring the filtration inclusions monic and computes their quotients. Expanding the split first factor gives exactly the convolution grade, with only finitely many j; countable cochain sums are handled by step 13. Off-diagonal d_P blocks increase j and therefore die modulo F^{r+1}; the remaining differential has the stated Koszul sign. The K-flat definition tensors an arbitrary acyclic complex with the K-flat complex second; the explicit signed swap in step 16 supplies that order before invoking it in step 15, so there is no circular acyclicity use. Both signs in the swap chain equation were checked modulo 2, and the swap carries (p,q) to (q,p), preserving total filtration. Empty/zero summands and a=b cause no exception.

New-leaf edge cases: the identity functor with V consisting of identities satisfies the hypothesis using I=X and equal maps; an empty source can be essentially surjective only onto an empty target. Without fullness, essential surjectivity, or the cylinder witnesses the criterion is not being asserted. The leaf statement contains only introduced objects and hypotheses, no proof sketch, and no extra claim of saturation. Search commands for LeanFinder, Loogle, grep and LeanSearch all ran and their hits were read. Loogle plus grep found the exact theorem; the semantic searches returned broader localization results. No service failure was recorded as absence.

I checked delivery-errors B–E against these files: no extra unsplit proof node, no unintroduced filtered object, no duplicate or renamed item clause, no altered target, no source-route substitution, and no uncited non-elementary theorem. All elementary portions are explicit calculations from the cited statements or definitions. No step now exceeds 2000 characters; this was achieved by citing the actual general Mathlib cylinder theorem and separating its application from the universal-property composition, not by hiding a comparison in prose. Every uses edge has an exact excerpt in citations.json. The new leaf's source has no Stacks tag because it is a direct generic Mathlib theorem. No existing maintainer-owned record was edited.

## Unfinished work

None in this stage-1 split. The named generic dependencies remain separate DAG work. Illusie is wanted as above. Required server dry run and delivery results follow below.

## Server validation

The required deliver.py --no-push completed with exit 0: `OK (not pushed) deliver/Q127/lem-trf-finite-filtered-flat-resolution at a0e6931e67: preflight passed`. This includes the delivery tool's server preflight and DAG/review checks. Only the two node JSON files and this report are delivered; sandbox helper scripts and the search/citation logs are validation inputs.
