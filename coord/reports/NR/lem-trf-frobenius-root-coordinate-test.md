# Stage-1 delivery: lem-trf-frobenius-root-coordinate-test

## Files written

- dag/nodes/sec-trace-formula/lem-trf-frobenius-root-coordinate-test.json — item, statement, split into seven proof steps. Original statement preserved verbatim; added its algebraic-closure notion to stmt_deps.
- dag/nodes/sec-trace-formula/lem-trf-first-root-tensor-reduced-test.json — one new statement-only unsplit algebraic lemma, not in Mathlib under the searches performed; no proof or proof dependencies.
- citations.json — every step/node pair, with the cited statement copied verbatim.
- searches.jsonl — actual msearch.py results, retained without alteration.

One new node; zero new Mathlib leaves. No Lean files written and no compiler, Lake, local preflight/check_dag/review_split, or git command run. All edits are in this item's sandbox.

## Attachments

None. Searched the live library under lean/WeilConjectures for the blueprint tag, root coordinates, weak stability, weak cartesianness and the first-root/reduced-tensor criterion. No declaration states the item. GeometricallyReducedExtensionSeparable.lean states the distinct implication from geometric reducedness to separability and does not state the new first-root test. Mathlib hits are not project attachments.

## WANTED

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, archival PDF, Theorem 3.5.3/1 and preceding remark, printed p.154 (scan p.162), for lem-trf-frobenius-root-coordinate-test; also Lemma 3.5.1/1 for the already existing spectral uniqueness input. The node's named local PDF is absent. I read the primary scan's indexed text at https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf through web search; fetching the full PDF through the browser failed with the content-size limit. I did not download or modify literature. The proof is marked agent-written, with that limitation recorded.

## What changed and why

There was no earlier sandbox node, report or search log. The live item was unsplit with an empty proof and existing inherited search records, all preserved. No released repair note exists for the item. No statement dispute was found. The field characteristic is necessarily prime; no new hypothesis was introduced.

BGR's printed proof uses successive Frobenius root fields and then the perfect closure. The preceding remark explicitly gives the equivalent characterization through reducedness of the first-root tensor with the completion. This is the route expanded here, at the node level: the assumed coordinate lower bounds prove injectivity into the completion of K_1; the algebraic root-tensor criterion makes every finite completed tensor reduced; its residue-field product carries a power-multiplicative norm; completeness of the base H, not K, gives coordinate continuity; existing spectral uniqueness identifies the resulting norm on L.

The sole new lemma is Stacks 030W, implication (3) to (4), for arbitrary field extensions. It has no valued-field, topology, completion or spectral-norm hypothesis or conclusion. It is a genuine algebraic input, not a clause of the item's analytic statement. The seven parent steps contain the analytic argument, so the item has not merely been relabelled or moved into a new node. The new lemma remains statement-only, as required.

The latest blueprint is main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8. I read the chapter, unit and latest lem-trf-local-term-locality statement and proof. The current unit uses contracting correspondences; the inherited BGR branch is historical supporting material below node level. Its ancestry and long via chain are retained, not used to replace any unit step. The new node's via starts with this item and its ancestor is lem-trf-local-term-locality, as blueprint_refs.py ancestor reports. Whole-blueprint searches for weakly cartesian, weak stability, Frobenius root, first root, pth root, spectral norm, geometrically reduced and 030W found no equivalent imported statement.

## Mathlib research

I read each service's hits. For the new node, the searches in its mathlib_searches are exactly the corresponding msearch.py queries and carry the original logged result objects. I used two semantic phrasings as well as Loogle and source searches. Algebra.isGeometricallyReduced_field_iff (the local source calls it isGeometricallyReduced_field_iff) tests the entire algebraic closure; it does not test the first Frobenius root field. The reduced tensor instance assumes geometric reducedness rather than deriving it from this first-root condition. I read Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:60–110. Formally unramified/separable equivalences need algebraic/essential-finite-type assumptions, and the PurelyInseparable hits describe uniqueness or existence of roots, not this reducedness test. Thus none is an exact match or one-line specialization. Every service used here returned successfully; no outage was recorded as absence.

For the item, new logged searches supplement the preserved inherited ones. SpectralNorm hits provide norm axioms, or a normed-space structure assuming CompleteSpace K; they do not supply the weak-stability conclusion over the incomplete K. I also read the existing Mathlib leaf statements used in the split; no duplicate coordinate-equivalence leaf was created, because the existing finite-dimensional continuity lemma suffices with the explicit scaling calculation of step 6.

## Review by NR

I checked the node files against delivery-errors B–E with the source statements open. For the item I read BGR's indexed p.154 theorem and its preceding completion remark, and recorded the missing local archival document and agent origin. For the new node I read literature/stacks-project/algebra.tex, label lemma-characterize-separable-field-extensions, lines 10360–10407, and checked the tag map: this is Tag 030W. Conditions (3) and (4) give precisely its implication for an arbitrary F/k, not only a finite or algebraic one. Its statement introduces k, F, E, the algebraic closure, first-root field, multiplication on the tensor and reducedness explicitly. Each notion dependency supplies the named notion.

Step 1 uses exactly the statement of lem-sfb-normed-field-completion: a normed field has a complete normed-field completion with an isometric field map. Before applying it I verify the multiplicative and ultrametric axioms of N by Frobenius, and nontriviality by restriction. The map H into H_1 is written on Cauchy representatives; no unmentioned completeness or functoriality lemma is needed.

Step 2 uses def-weil-vector-space-scalar-extension for the tensor vector space and bilinear relations; multiplication and j are explicitly supplied. For every tensor, only the finite span of its first factors is needed. The lower bound for that span passes to H-coefficients by approximating the finitely many coefficients and taking the finite maximum. If its image vanishes, every coefficient vanishes, so the tensor is zero. This proves injectivity and reducedness directly; it never assumes K_1/K finite. The empty span has zero tensor and needs no choice of a basis vector.

Step 3 uses the new lemma's actual reducedness conclusion, with k=K, F=H, E=L. The first root extension and characteristic are exactly the ones already present. The input B is reduced by step 2, and the two tensor-factor switches are explicitly the maps on pure tensors. The lemma allows H/K to be transcendental and L/K inseparable. No definition of separability is cited for a theorem about separability.

Step 4 uses the basis and dimension clause of def-weil-vector-space-scalar-extension, the Artinian conclusion of lem-weil-pbc-finite-dim-algebra-artinian, and the entire canonical residue-product statement of lem-sfb-reduced-artinian-residue-product. Its assumptions are verified: A is a commutative finite-dimensional H-algebra and reduced by step 3. A is nonzero since its dimension d is at least one. Each factor is finite-dimensional as a quotient, and its H-action is faithful since it is a unital map between fields. The residue-product lemma's zero-ring convention causes no empty-product error here. The cited statement supplies the canonical quotient factors, not merely an unspecified ring isomorphism.

Step 5 uses lem-trf-spectral-norm-algebraic-extension only over H. I checked its complete-base hypothesis here and nowhere assert K complete. Each E_j/H is finite and hence algebraic. Componentwise finite maxima give all norm identities and the power identity directly. Continuity of scalar multiplication is proved by the displayed estimate, so the topological-vector-space hypothesis needed in the next step is established.

Step 6 uses exactly the continuity conclusion of lem-sfb-finite-dimensional-linear-map-continuous, for the coordinate linear maps out of the finite-dimensional Hausdorff space A and into H. That node permits every complete nontrivially valued field, not merely the l-adic example it mentions. A common delta exists for the finitely many coordinate maps. The explicit integer-power scaling by t proves c=rho*delta is a lower-bound constant. The two inequalities defining m give the correct direction rho^(-m) <= Q(a)/(rho*delta). The upper bound is the finite ultrametric sum. C is positive since every basis vector is nonzero and d>=1. No norm-equivalence theorem with an incomplete base has been smuggled in.

Step 7 uses exactly lem-trf-product-topology-spectral-uniqueness. Its statement allows incomplete K and nonseparable L/K. The restricted M is definite by injectivity, has M(1)=1 since the product is nonempty, is ultrametric and power-multiplicative by step 5, and has the required basis bounds from step 6. Thus its conclusion M=s_{L/K} is applicable without any missing hypothesis. I checked the dependency closure of every cited nontrivial input for a path back to this item: none exists. All citations are to statements, not details inside their proofs, and citations.json copies each available statement verbatim.

Small cases: V=0 gives the zero tensor and empty maximum; L=K gives one factor and the original absolute value; complete K gives H=K and no artificial completeness requirement; perfect K has K_1=K and its first-root algebraic test reduces to geometric reducedness over a perfect field. For an imperfect k=F_p(t), F=k(t^(1/p)) does not satisfy the new lemma's premise: F tensor_k k^(1/p) has the nonzero nilpotent t^(1/p) tensor 1 - 1 tensor t^(1/p). Thus the lemma does not incorrectly treat an arbitrary inseparable scalar extension as reduced. No finite p-rank is used. Every proof step is below 2000 characters (maximum 989); none conceals a separate standard comparison lemma.

I corrected the initially missing algebraic-closure statement dependency, and avoided both the circular weak-spectral-completion-product input (which assumes the desired bounds) and any use of a separable-only tensor decomposition for arbitrary L/K. No off-unit non-Mathlib tool is used: the spectral uniqueness input and new algebraic lemma inherit this unit, and the remaining cross-unit inputs are existing Mathlib leaves. No SGA source is cited.

## Not duplicates

The following pairs exhaust existing files containing 030W at the time of the search (including files where the tag is only in a proof/review). The new node specifically assumes reducedness only after the first-root tensor and concludes reducedness after every field tensor, for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable: the existing statement concerns reduced tensor with an algebraic closure detects separability of a finite field extension; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-pc-finite-inseparable-element: the existing statement concerns a finite nonseparable extension has an inseparable element; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-pc-inseparable-tensor-nilpotent: the existing statement concerns an inseparable element produces a nilpotent after algebraic-closure base change; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-pc-proper-geometrically-reduced-global-sections-separable: the existing statement concerns separability of global sections of a proper geometrically reduced scheme; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs def-weil-pbc-separable-field-extension: the existing node defines separability and separating bases; it asserts no first-root reducedness criterion.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-field-char-p-h1-cotangent-vanishing: the existing statement concerns h_1 of the naive cotangent complex of a field over f_p vanishes; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-geometrically-reduced-extension-separable: the existing implication starts from all field tensors already reduced and concludes separability; it cannot supply the first-root-to-all-fields implication.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-make-separable: the existing statement concerns a finitely generated field extension becomes separable after finite purely inseparable extensions; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-make-separably-generated: the existing statement concerns a finitely generated field extension becomes separably generated after finite purely inseparable extensions; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-p-power-independence-separably-generated: the existing hypothesis is preservation of p-power linear independence and assumes F/k finitely generated; it does not state the arbitrary first-root tensor test.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-separably-generated-separable: the existing statement concerns a separably generated field extension is separable; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-weil-pbc-separably-generated-tensor-reduced: the existing statement concerns tensor product of a separably generated field extension with a reduced algebra is reduced; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-dvr-index-one-separable-base-change: the existing statement concerns index one and residue separability survive normalized finite base change; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-dvr-normalized-finite-stage-descent: the existing statement concerns finite-stage descent from an algebraic normalized solution; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-essentially-smooth-dvr-index-one: the existing statement concerns essentially smooth local dvr extensions have ramification index one; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-finite-georeduced-etale: the existing statement concerns finite geometrically reduced schemes over fields are etale; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-invariant-marked-generic-normalization: the existing statement concerns invariant inseparable normalization of a marked generic curve; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-invariant-separating-parameters: the existing statement concerns invariant separating parameters for a semilinear finite action; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-neron-strict-local-descent-base-change: the existing statement concerns néron lft-models under ramification-one base change and strict-local descent; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-point-blowup-fibre-defects: the existing statement concerns geometric fibre defects in regular surface point blowups; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separability-tensor-field-descent: the existing statement concerns separability descends from a tensor field after scalar extension; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separable-algebraic-intermediate-base: the existing statement concerns separable algebraic extensions remain separable over an intermediate base; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separable-field-extension-transitivity: the existing statement concerns transitivity of separable field extensions; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separable-finite-top-extension: the existing statement concerns finite separable top extensions preserve nonalgebraic separability; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separable-point-scheme-core: the existing statement concerns canonical geometrically reduced subscheme carrying separable points; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separable-residue-finite-tensor-fields: the existing lemma assumes separability of F/k and a finite second field; the new lemma derives all tensor reducedness from first-root reducedness and imposes no finiteness.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separating-basis-algebraic-diamond: the existing statement concerns separating basis construction and transfer in an algebraic field diamond; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sfb-separating-stein-generic-curve: the existing statement concerns separating function fields and the geometrically integral generic curve; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-sbc-field-hypersurface-integral-presentation: the existing statement concerns integral hypersurface presentation of a separable function field; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-trf-geometric-field-stalk-descent: the existing statement concerns a geometric field stalk descends to a finite separable field stalk; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-trf-geometrically-integral-curve-factorization: the existing statement concerns factorization with a geometrically integral generic curve; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.

lem-trf-first-root-tensor-reduced-test vs lem-trf-smooth-domain-fraction-separably-generated: the existing statement concerns the fraction field of a smooth domain is separable over the base field; its hypotheses/conclusion do not give the first-root-to-all-field-tensors reducedness test for arbitrary F/k.


The analytic lem-trf-weak-spectral-completion-product assumes the very coordinate inequalities being proved here; the new algebraic lemma assumes only first-root tensor reducedness and makes no statement about norms. The item is also distinct from lem-trf-char-zero-spectral-coordinate-topology, which assumes characteristic zero, and from the fraction-module parent, which assumes bounded separation over an integral ring rather than the first-root coordinate hypothesis.

## Unfinished work and validation

The only deliberately unsplit work is the new algebraic Stacks 030W lemma. Its statement-only format leaves that work to the queue. No blocker or statement error remains in the item. The read-only server checks check_dag and review_split passed before report preparation. Final deliver.py --no-push and push results are reported by the tool and final delivery response.
