## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-fixed-support-fourier-lipschitz.json`: item, split, four proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-complex-phase-exponential-bound.json`: new Mathlib leaf, exact declaration `Real.norm_exp_I_mul_ofReal_sub_one_le`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-bochner-integral-subtraction.json`: new Mathlib leaf, subtraction and almost-everywhere congruence.
- `citations.json`: eight verbatim statement extracts for the cited nodes.

Attachments: none. I searched `lean/WeilConjectures/` for the item identifier and for fixed-support Fourier, compact-support Fourier, and Fourier Lipschitz terms; no sorry-free project declaration states the item. The source is not present locally; I read it online at the author-hosted PDF URL.

WANTED: Demailly, *Differential and pseudodifferential operators*, §2, Lemma 2.7 proof, pp.5–6, for the fixed-support Fourier equicontinuity argument (the local item source records the author-hosted PDF URL). Read online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf. The first-moment proof is an agent specialization, not a verbatim lemma of that source.

The item arrived unsplit. I retained its hypotheses and conclusion. The new nodes are the smaller unit-phase identities/estimate and complex integral subtraction/congruence; both are Mathlib leaves. Existing DAG nodes provide compact-set integrability, scalar L² Cauchy–Schwarz, and the norm bound for an integral dominated by an integrable majorant. No definition node or item clause was duplicated.

## Not duplicates

lem-sfb-complex-phase-exponential-bound vs lem-sfb-fixed-support-fourier-lipschitz: the new node is the pointwise scalar inequality $|e^{it}-1|\leq|t|$; it has no function $u$, support K, Fourier integral, L² hypothesis, or Lipschitz conclusion.

lem-sfb-complex-phase-exponential-bound vs lem-sfb-l1-l2-fourier-realization: the existing node concerns Plancherel isometry and L¹ representatives; the new node is a pointwise complex exponential estimate and is independent of Fourier-transform realization.

## Review by NB

I read the complete item node, Demailly’s Lemma 2.7 proof (printed pp.5–6), its source field, the unit `sk-thm-sf-ctf-stability`, and the current blueprint supporting text under `det-thm-sf-ctf-stability-direct-images` proof (3). The current blueprint direct-images proof (3) supplies the inherited route context, far above this analytic estimate through the alteration and harmonic-representative prerequisites. The ancestor tool reports None; the null ancestor and complete inherited via chain are preserved. No blueprint node states this analytic estimate. I also opened the statements of every cited DAG node. `lem-sfb-continuous-on-compact-integrable` says continuous functions on compact subsets of Euclidean space are integrable; applying it to 1 and |x|² supplies finiteness of v and b². `lem-sfb-real-l2-hilbert-pairing` explicitly gives the scalar L² Cauchy–Schwarz inequality used with |u|, 1_K, and |x|. `lem-sfb-integrable-majorant-estimate` explicitly gives both integrability under an almost-everywhere norm majorant and the norm bound for the integral. The phase-estimate clause is exactly Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le` at `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean:260`.

Step 1 checks the compactness, measurability, finite volume and finite second moment, then applies the cited scalar Cauchy–Schwarz statement on K. The zero-off-K hypothesis identifies the K integral with the whole-space L¹ integral. Step 2 uses the unit modulus of the exponential and the cited majorant theorem to obtain absolute convergence and the uniform bound. Step 3 rewrites the phase difference by factoring out the second unit phase, applies the new pointwise phase estimate to $-2\pi x\cdot(\xi-\eta)$, uses the elementary Euclidean dot-product inequality, and then applies the cited majorant and scalar Cauchy–Schwarz statements to obtain the stated Lipschitz constant. Step 4 is elementary: a global Lipschitz estimate implies continuity, and the constants depend only on the common L² bound and K.

I tested edge cases in the statement: an empty compact K gives v=b=0 and u=0 almost everywhere; a singleton K also has v=b=0 and hence u=0 almost everywhere; ξ=η makes the Lipschitz estimate 0≤0; and u=0 gives h=0. The phase node was tested at t=0 and at negative t, where the absolute-value statement is symmetric. No hypothesis on m beyond m≥1 was added or dropped. No long proof step exceeds 2000 characters. The mandatory LeanSearch, Loogle, LeanFinder and Mathlib grep searches were run for both the item and the new node; the item searches found only general Fourier/L² declarations, while the phase searches found the exact Mathlib theorem. No Lean files, compilers, Lake, or builds were used.


## Final citation and source audit

I added lem-sfb-bochner-integral-subtraction for the difference-of-integrals identification in step 3. Its arbitrary-measure complex statement is exactly MeasureTheory.integral_sub (Bochner/Basic.lean:261–264) and MeasureTheory.integral_congr_ae (line 299), whose source I opened. Integrability of both integrands is established in step 2 before subtraction. Its clauses do not give either Fourier bound. The phase leaf also states unit norm and exponential addition, matched to Complex.norm_exp_I_mul_ofReal (Complex/Trigonometric.lean:954–955) and Complex.exp_add (Complex/Exponential.lean:111). Those source lines were read. Each clause is an exact Mathlib match, rather than a new elementary node.

The proof now writes finite-dimensional Cauchy–Schwarz as a square-norm calculation. The spatial-moment integrability is established before applying the majorant theorem. All scalar L² applications are on explicit zero-extended real functions on R^m, so the existing whole-space node is used with exactly its stated domain. Almost-everywhere support suffices throughout. The new phase leaf's estimates imply continuity of the phase as a function of x directly, so the measurable-integrand assertion does not depend on a Fourier differentiability result. The only elementary final step is continuity from the global Lipschitz inequality and taking a common L² bound.

Demailly's online proof was read at printed pp.5–6: it treats fixed-support distributions, obtains derivative estimates and equicontinuity on balls, then uses Ascoli extraction. Our argument uses the first spatial moment to give the particular global Lipschitz constant asserted by the imported item. WANTED above asks for a local archival copy; the online text was accessible. No SGA source is used, and no Stacks tag states the analytic results here.

Whole-DAG searches used the phase/exponential wording and declaration names, and integral subtraction/integral_sub. The only integral_sub string in another candidate was a search hit inside the unrelated étale affine-translation-trace node, whose statement I opened; it cannot supply a Lebesgue-integral equality. Whole-blueprint searches for exponential, phase, integral subtraction and integrable functions found no equivalent analytic statement. The project source has no theorem giving these new statements. The new subtraction node is also tested on f=g, g=0, the zero measure and changes on a null set; integrability is required for subtraction and is not required for the congruence clause, exactly as in Mathlib.

The first dry run found that new-node searches had been executed under a proposed new id instead of the assigned item, outside the authoritative item log. I reran them under the assigned item and recorded the actual log objects, with query text unchanged. A server check also found missing chapter metadata; chapter and unit now inherit from the item. No checker or launcher was modified. All long-step checks are clear: the final step lengths are 504, 548, 775 and 259 characters. citations.json now contains full verbatim statements for all eight proof-step citations.

## Not duplicates (additional check)

lem-sfb-bochner-integral-subtraction vs lem-pur-affine-translation-trace: the new node is subtraction and almost-everywhere congruence of complex Bochner integrals; the existing node states equality of étale trace morphisms after translation. Their common search term is not a shared assertion.

lem-sfb-bochner-integral-subtraction vs lem-sfb-integrable-majorant-estimate: the new node gives subtraction and congruence of integrals, whereas the existing node gives domination, integrability and a norm bound. Neither existing statement supplies the new clauses.
