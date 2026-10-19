# Repair of lem-trf-filtered-derived-hom-calculus

## Files written

- dag/nodes/sec-trace-formula/lem-trf-filtered-derived-hom-calculus.json: repaired split, seven proof steps; statement, stmt_deps, Lean record and steps 1, 2, 4, 5, 7 preserved verbatim against the returned/current shared version.
- dag/nodes/sec-trace-formula/lem-trf-filtered-hom-complex-invariance.json: one new statement-only node, unsplit, no Mathlib match. It states concrete homotopy and graded quasi-isomorphism invariance, rather than existence or any clause of the derived bifunctor in the item.
- citations.json: a verbatim statement quotation for every use in every proof step.
- report.md: this repair report and mathematical review.

The retained lem-trf-bounded-filtered-localization-embedding.json is byte-for-byte mathematically identical to the current shared node; it was already landed, is cited as existing material, and is not a new node in this repair.

## Attachments

None. Searches of WeilConjectures/ for the blueprint tag, filteredDerivedHomCalculus, filtered Hom, filtered quasi-isomorphisms and the related homology notions found no declaration proving the item or the new helper. The item's retained Sheaf stage-2 record is a statement, not an attachment of a finished upstream proof; it is unchanged.

## WANTED

None for this repair. Varshavsky and the Stacks sources used here are available locally. Varshavsky cites Illusie V.1.4, but this split expands the argument independently and retains proof_origin.by = agent; it does not assert that the unarchived Illusie proof was read.

## What was wrong and what changed

The return requires extraction of the hidden arguments in the old 2412-character step 3 and 2577-character step 6, with no statement or Lean-record change. I continued the retained partial repair instead of restarting it. There was no report.md or citations.json in the retained sandbox. I read its searches.jsonl and reused the recorded results; no search result was fabricated or silently promoted from unavailable to no match.

Step 3 now takes the finite split-flag assertion from the existing lem-trf-injective-graded-filtration-splits. The hidden semiorthogonality argument is supplied by existing nodes: the universal Hom bijection and graded-truncation formula of lem-trf-filtered-unbounded-truncation, and the fully faithful comparison in lem-trf-filtered-bounded-localization-comparison. These replace the old implicit replacement by representatives in restricted filtration intervals. The cone calculation is retained explicitly, and the existing lem-weil-pbc-triangle-morphism-extension supplies precisely the two triangle-comparison assertions. Thus the original route (split flags, cone triangle, support vanishing, unique triangle comparison) is preserved. No new restatement of a truncation clause is introduced.

Step 6 moves the signed Hom-complex homotopy calculation and the graded quasi-isomorphism argument into the new lem-trf-filtered-hom-complex-invariance. The step then applies localization's functor and natural-transformation universal properties one variable at a time and composes with the filtered-injective equivalence. It still constructs the bifunctor and descends the comparisons; that construction was not moved into a node merely restating the item's conclusion.

Current non-elementary step lengths are 947, 1299, 1595, 1811, 1577, 1495 and 1387 characters. The long-step repair is mathematical extraction, not just paragraph reformatting. I checked all seven steps, including those retained unchanged.

## Not duplicates

lem-trf-filtered-hom-complex-invariance vs lem-trf-filtered-localization-injective-model: both mention 05TY, but the existing statement supplies resolutions, a Hom-set bijection and an equivalence for filtered-injective complexes; the new lemma concerns the concrete shift-filtered complex of abelian groups and maps/homotopies on that complex, including graded quasi-isomorphism invariance in the contravariant variable.

lem-trf-filtered-hom-complex-invariance vs lem-weil-pbc-dplus-injective-representative: both mention 070J, but the existing statement gives ordinary K-injective representatives; it has no shift filtration on a Hom complex and no map of filtered Hom complexes.

lem-trf-filtered-hom-complex-invariance vs lem-trf-filtered-derived-hom-calculus: the item constructs a derived bifunctor, triangles, graded comparisons and morphism identifications; the new lemma states invariance of explicitly defined complexes before localization, without constructing a derived functor.

lem-trf-filtered-hom-complex-invariance vs lem-trf-filtered-operations-hom: the existing statement is a geometric filtered six-operation package and derived Hom conclusion, not a concrete chain-level invariance theorem, and its proof already depends on this item.

lem-trf-filtered-hom-complex-invariance vs prop-trf-trace-formal-laws: the whole-blueprint search for filtered Hom found this blueprint node, but its statement concerns categorical trace laws, not Hom-complex invariance.

I searched all dag/nodes for the tags 05TY and 070J and the key notions, and used tools/blueprint_refs.py search for filtered Hom, 05TY, filtered injective cone quotient, Hom complex descent localization and filtered orthogonality. No blueprint statement supplies the new chain-level lemma. The existing filtered truncation and split-flag nodes are reused rather than duplicated. The two new citations in step 3 have no dependency path back to this item (checked the whole statement/proof-dependency closure, including the 1009-node comparison closure).

## Mathlib searches and hits read

The new node retains the exact recorded LeanFinder queries (two phrasings), Loogle query, Mathlib grep and unavailable LeanSearch entry from searches.jsonl. I read the logged result names and the likely relevant source. Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean:485 (CochainComplex.HomComplex.δ_comp) and :536 (δ_ofHomotopy) give ordinary Hom-complex differential identities; they do not concern finite flags or a shift filtration. Mathlib/Algebra/Homology/DerivedCategory/KInjective.lean supplies Qh_map_bijective, quasiIso_iff and the cohomology-class comparison for ordinary complexes. Those ordinary facts do not specialize in one line to graded quasi-isomorphisms of shift-filtered Hom complexes; that additionally needs the graded Hom comparison and the filtered homotopy calculation. The other logged hits concern ordinary localization, complex shapes or homotopy equivalences. The grep returned no filtered-Hom quasi-isomorphism declaration. The unavailable LeanSearch result is recorded as unavailable. Later retained whole-source searches found only ring filtrations, not the required categorical filtered-complex statement. No new Mathlib leaf is claimed.

Additional searches during this continuation for filtration-support orthogonality returned ordinary cochain-support vanishing results (DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE and related t-structure statements). Cochain support and filtration support are different, so these are not used as matches. No orthogonality node was created: the existing truncation Hom bijection already suffices.

## Proof notes for the statement-only helper

These notes are for the next splitter, not a split proof in the new node. For a degree n family f set d(f)=d_I f-(-1)^n f d_P. Direct expansion gives d^2=0. A chain map s or u commutes with the appropriate differential, so pre- and postcomposition are chain maps; they preserve F^r because s,u preserve all filtration steps. They commute by associativity.

For s-t=d_Ph+hd_{P'}, put S(f)=(-1)^n f h in degree n-1. In dS(f)+S(df), the d_I f h terms cancel and the remaining terms are f(hd_{P'}+d_Ph)=f(s-t). For u-v=d_Jk+kd_I, put T(f)=kf; the f d_P terms cancel in dT(f)+T(df), leaving (d_Jk+kd_I)f. Both S and T preserve each F^r. Thus they are filtered homotopies, and filtered homotopy equivalences induce filtered homotopy equivalences.

For the quasi-isomorphism assertion, the target graded objects are injective. Stacks 05TP splits every target flag termwise. Taking associated graded of the shift-filtered Hom complex gives the canonical map to the finite sum of ordinary Hom complexes from gr^a P to gr^{a+r} I. Its kernel is F^{r+1}. Surjectivity follows by extending a map from gr^a P^i to the injective object gr^{a+r} I^{i+n} across gr^a P^i -> P^i/F^{a+1}P^i, and including the corresponding target split summand. The lift kills F^{a+1}, hence has precisely the required filtration shift; summing over a gives the prescribed graded maps. Differentials commute with this canonical comparison. This is the same explicit algebra as item step 5 and is natural, since the splittings are used only for surjectivity. Each graded target complex is bounded below and termwise injective, hence K-injective by 070J. On cohomology, precomposition by gr^a s is therefore precomposition by an isomorphism in D(A); it is bijective in every degree. The sum is finite, so the induced map in each grade is an ordinary quasi-isomorphism.

Bounded source terms are essential here: only finitely many i occur in each sum. If P is zero above v and I zero below w, then C(P,I) is zero below w-v. If source filtration grades lie in [a,b] and target grades in [c,e], then F^{c-b}C=C and F^{e-a+1}C=0. No finite injective dimension or bounded-above resolution is assumed. Enough injectives is not needed for this helper because its target injectives are supplied as hypotheses.

## Source error retained from the original split

Varshavsky 5.1.1(c) reverses the adjoint directions: F^r is right adjoint to the high-filtration inclusion, while the quotient is left adjoint to the low-filtration inclusion. For a field k, put M=k in filtration grade 0 and L=k in grade 1. At r=1, Hom(M,L)=k but Hom(F^1M,L)=0, contradicting the printed left-adjoint assertion. This does not change this item's statement, which is correct and states neither erroneous adjunction. Its uniqueness proof uses the correctly oriented Hom bijection of the existing unbounded-truncation node.

## Review by Q22

I read Varshavsky pp.39–41, 5.1.1–5.1.5 and Lemma 5.1.4, for the item, and Stacks derived.tex 05TP (lemma-filtered-injective), 05TY (lemma-morphisms-into-filtered-injective-complex) and 070J (lemma-bounded-below-injectives-K-injective) for the new helper. I checked the tag-to-label mapping in tags/tags. The new node is deliberately statement-only and its supporting computations are recorded above. The unit sk-i-curve-zero, chapter record and current blueprint locality proof keep the same open–closed trace-additivity route; none is edited. No SGA source is used.

For step 1 I read def-weil-abstract-derived-category for the cone matrix and ordinary localization, def-sp-filtration and def-sp-filtered-complex-subquotients for filtrations and graded complexes, and lem-weil-pbc-localization-universal-property for the functorial universal property. I checked the cylinder differential squares to zero, the homotopy-induced H is a chain map, and the graded projection has the contractible identity-cone kernel. This works for bounded and bounded-below inputs and keeps a uniform filtration interval.

For step 2 I read the complete statements of lem-trf-filtered-localization-injective-model and lem-trf-bounded-filtered-localization-embedding. The former explicitly provides the exact equivalence, ordinary-injective underlying and graded representatives, and resolutions in the same fixed filtration interval; the latter explicitly provides a fully faithful exact bounded-to-plus comparison. The item assumes enough injectives, as required for the model. I checked that the truncated graded maps are either the original maps or maps of zero complexes, and that truncation, grading and forgetting commute with the finite-sum cone matrices. The localization universal property supplies descent of functors and natural transformations, not any missing exactness theorem.

For step 3 I read the statements of all nine cited nodes. The split-flag node really supplies an isomorphism identifying each filtration step with the high-index sub-biproduct, not merely an informal definition of injectivity. The subobject and quotient grades are the original injective grades or zero; their complexes remain bounded below. The explicit cone-to-quotient map is a graded quasi-isomorphism by the displayed contraction. For the support argument the unbounded-truncation statement really supplies both the graded formula and the Hom bijection for support in the derived category. Taking M=R[q] makes t_{>=r}M graded-acyclic, hence zero after localization; the bijection gives Hom(L,R[q])=0. The bounded-localization-comparison statement supplies full faithfulness into that unbounded category. It has no enough-injectives requirement, its filtrations are uniform, and its dependency closure does not use this item. The triangle-morphism-extension statement supplies existence when the composite is zero and uniqueness when Hom(L[1],R_1)=0; both are exactly furnished by the support vanishing. Reversing the comparison proves the isomorphism assertion rather than just existence of a triangle morphism. This is the repair of the first long step.

For step 4 I checked the explicit differential, the lower cochain bound and the two filtration bounds. The cited model theorem states that the underlying and graded injective representatives are ordinary termwise injective. The cited dplus-injective-representative statement part (2) gives K-injectivity of every bounded-below complex of injectives; kinjective-hom-derived gives the ordinary derived Hom bijection. I checked the degree-q cocycle/chain-map equation and the sign h=(-1)^q g for boundaries. The injective-resolutions and filtration definition nodes supply the terms used, not additional unstated acyclicity results.

For step 5 I checked the kernel F^{r+1} and the injective-extension surjectivity calculation explicitly. The definition of injective in def-sp-injective-resolutions really is the extension property across every monomorphism, so applies to gr^a P^i -> P^i/F^{a+1}P^i. The target split-flag identification has been obtained in step 3 from the existing node, not assumed from a definition. There are finitely many a and i, so the sums and the resulting isomorphism of complexes need no infinite-product exactness assumption. The canonical comparison is independent of splittings and commutes with differentials. The K-injective statements cited in steps 4–5 have the required hypotheses for each graded target. The index is target minus source.

For step 6 I checked that the new helper's statement gives precisely the filtered chain maps, commuting actions, homotopy invariance and source quasi-isomorphism invariance which the step takes. It does not require the second target J to be injective for homotopy invariance, but quasi-isomorphism invariance is used only with I termwise filtered injective. Parts (1), (2), (3) of localization-universal-property respectively supply the descended functor, transformations preserving identity/composition, and equality of descended transformations. The equivalence of the model theorem supplies the quasi-inverse in the second variable; two representatives become inverse up to filtered homotopy. The bounded-below output and natural comparisons are those constructed in steps 4–5. This is the repair of the second long step.

For step 7 I checked that F^0 cocycles are exactly filtered chain maps and its boundaries exactly filtered null-homotopies. The model theorem and bounded embedding give the stated filtered-derived Hom set. The filtration definitions identify F^0 with the high truncation and F^0/F^1 with grade zero. The ordinary K-injective comparison identifies inclusion with the forgetful map. The canonical graded map already constructed in step 5 sends the very same chain map to its componentwise graded maps, so the final projection equation and naturality hold, with no hidden change of coefficient category.

Small cases checked for the helper and repaired steps: the zero source or target, identity maps, a one-grade filtration (ordinary Hom-complex invariance), two distinct pure filtration grades (the Hom filtration is in target grade minus source grade), r outside filtration support, and graded-acyclic rather than literally zero excluded grades. The latter is exactly why I used the existing derived Hom bijection in step 3. These tests also show why ordinary cochain t-structure vanishing hits are not valid substitutes. I checked B–E against the actual files: complete hypotheses, definition citations, noncircular dependencies, no new clause-restatement node, exact Stacks labels, searches actually logged, verbatim citation coverage, and unchanged item statement and Lean record.

## What remains

No unresolved mathematical issue in this stage-1 repair. The one new helper remains unsplit by design and goes through the ordinary subsequent stages; no Lean was written or compiler, Lake or build command run. The server dry run and delivery are the final required operations.
