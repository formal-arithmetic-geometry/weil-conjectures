# Q21 stage-1 report: lem-sfb-kahler-normal-holomorphic-coordinates

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kahler-normal-holomorphic-coordinates.json: item, split; unchanged statement. Four explicit steps prove the first-jet normal form.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-complex-orthonormal-basis.json: statement, Mathlib leaf, stdOrthonormalBasis, Mathlib/Analysis/InnerProductSpace/PiL2.lean:1076. No proof or proof dependencies.
- citations.json: full verbatim cited statements for steps 1 and 3.
- searches.jsonl: actual msearch.py results, retained unchanged.

## Attachments

None. The blueprint tag and normal-holomorphic-coordinate searches in lean/WeilConjectures return no declaration. Algebraic Kähler differentials and vector-space Kähler pairings do not state the item.

## Wanted literature

WANTED: Wenrui Kong, Notes on Complex Geometry (April 9, 2025), §3.3 Definition 3.18 and Theorem 3.19, printed p.7 / PDF page 7, for lem-sfb-kahler-normal-holomorphic-coordinates. There is no local PDF in the literature tree. I read the named PDF online at https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf, including §2.2 Theorem 2.8 and §3.3. No file was downloaded. Theorem 3.19 is stated without a proof. Accordingly proof_origin.by is agent, and the complete quadratic-coordinate calculation is supplied here in the item rather than attributed to Kong.

## Audit of the incoming item and route

The item had a statement, searches and no proof. Its first-linear convention agrees with Definition 3.18: omega is minus the imaginary part of h, equals g(J-, -), and has the i/2 coordinate factor. No hypothesis or conclusion was changed. No statement dispute was found.

I read SETUP's three levels, the chapter record, the assigned unit sk-thm-sf-ctf-stability, GOAL.md, and the current blueprint paragraph (3) in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md. This work supplies the analytic normal-coordinate prerequisite already selected below the parent's Kähler commutator proof, without substituting a different direct-image route. The chapter and unit records are untouched. blueprint_refs.py ancestor returns None, matching the inherited null from.node of this long created chain; the new leaf prepends this item to the inherited via list and specifies the linear-normalization place.

## Not duplicates

lem-sfb-finite-complex-orthonormal-basis vs lem-sfb-countable-normed-orthogonal-basis: the latter concerns an algebraic basis with uniform ultrametric coefficient estimates over a finite extension of Q_l, not an orthonormal basis for a finite-dimensional complex inner product space.

lem-sfb-finite-complex-orthonormal-basis vs lem-sfb-hermitian-dolbeault-orthogonal-decomposition: the latter asserts a global differential-operator decomposition of spaces of smooth forms on a compact manifold, not finite-dimensional vector-space basis existence.

lem-sfb-finite-complex-orthonormal-basis vs lem-sfb-kahler-normal-holomorphic-coordinates: the new leaf is linear algebra only, with no manifold, closedness, chart, or jet; the nontrivial coordinate construction and cancellation remain in the item.

Whole-DAG searches included orthonormal basis, stdOrthonormalBasis, exists_orthonormalBasis, positive-definite Hermitian forms, biholomorphism and inverse-function terminology. I inspected statements of candidate analytic and Hermitian nodes. Whole-blueprint searches for holomorphic, Hermitian, orthonormal basis and inverse function found no matching statement. The existing lem-sfb-complex-analytic-inverse-toolkit was found and reused; no new inverse-function node was made. No Stacks tag is appropriate to these analytic and inner-product statements, so none is invented.

## Review by Q21

I checked sections B through E of delivery-errors.md against the actual files and sources. For the item I read Kong's Definition 3.18 and Theorem 3.19 online. For the only new node I read stdOrthonormalBasis and its preceding exists_orthonormalBasis in the pinned Mathlib/Analysis/InnerProductSpace/PiL2.lean:1069–1080, including the finite-dimensional context. I read the entire statement of the existing analytic inverse toolkit and the underlying source at FDeriv/Analytic.lean:141,414, InverseFunctionTheorem/FDeriv.lean:115,127,131, and Analytic/ChangeOrigin.lean:387. Its pointwise analyticity clause alone would not establish a holomorphic inverse on a whole target; clause (4) supplies the neighbourhood, and step 3 explicitly restricts it.

Step 1 takes only orthonormal-basis existence from the new leaf. I checked that the tangent fibre is finite dimensional and positive definite, and reversed h's arguments to match Mathlib's conjugate-first convention. The invertible basis-change matrix is written explicitly. The new leaf itself uses exactly Mathlib's conjugate-first convention, compatible norm, and Fin(finrank) index. No comparison theorem is hidden in the Mathlib match.

Step 2 cites no theorem. It expands the defining form on real coordinate vectors, differentiates its coefficients, and reads the coefficient of the (2,1) wedge monomial. Closedness is a hypothesis of the item, not an unstated use of a Kähler-connection theorem. Repeated indices are handled separately, so the symmetry argument also works in complex dimension one. This is an elementary coordinate calculation and remains a step rather than a node.

Step 3 uses precisely clauses (1) and (2) of the existing analytic toolkit for the polynomial's local inverse, clause (3) for analyticity at the image, and clause (4) for analyticity throughout a smaller neighbourhood. The polynomial is defined on all of C^n, its derivative at zero is the identity, and C^n is finite dimensional and complete. I restricted the target to its intersection with the old u-chart image and the analytic-inverse neighbourhood, and then restricted the source through the actual homeomorphism. This keeps the chart domain available; an earlier draft instead put the old-chart restriction on the source, which was unnecessary and has been corrected. I verified the sign and factor 1/2 by differentiating the finite quadratic sum: symmetry gives second derivative -C, not -C/2.

Step 4 uses no uncited analytic normal-form or connection result. Its displayed tensor-transformation formula follows from the chain rule for the real coordinate tangent vectors and first-linearity of h. Differentiating that finite sum produces exactly two possibly nonzero terms: the old coefficient derivative and the quadratic Jacobian derivative. The conjugated holomorphic Jacobian contributes zero to a z derivative. They cancel entry by entry. Hermitian symmetry gives all barred derivatives, with indices exchanged before conjugation. Thus every conclusion of the item follows; no clause is moved into a new node.

I checked small cases: an already constant Euclidean metric gives C=0 and F the identity; in dimension one an arbitrary positive smooth metric has C=h_z(0) after linear normalization, and F(z)=z-C z^2/2 cancels both conjugate first derivatives. No compactness, completeness of the manifold, or real analyticity of the metric is used. Only the polynomial coordinate change is analytic. The new leaf includes dimension zero: its basis is empty, so it needs no nonempty-index assumption. Positive definiteness, unlike mere semidefiniteness, is essential to step 1 and is present.

The two non-elementary steps are under 2000 characters and cite statements that say exactly what they take. The two elementary steps are explicit finite coefficient calculations, with all indices and conjugations shown. citations.json contains the full literal statements of both cited nodes, independently read before copying. New-node searches were actually run through msearch.py, with the exact tool/query pairs recorded; the hits give stdOrthonormalBasis directly. The item's older searches are retained and supplemented by the actual new searches; no unavailable service is labelled absent.

## Unfinished work

None at the split level. The new leaf is already in Mathlib; formal Lean implementation is outside the authorized stage. Dry-run and delivery results follow below when available.

## Validation

The initial server dry run passed at b2fed802ba4. After reading the generated files again, I made the old-chart target restriction explicit in step 3 and corrected the supplementary exists_orthonormalBasis declaration line from its docstring line 1069 to theorem line 1070. The principal Mathlib match remains stdOrthonormalBasis at 1076. The final required dry run is repeated on these exact files before pushing. No Lean code or compiler was used.
