## Worker report

Files written (all relative to the sandbox):

- dag/nodes/sec-trace-formula/lem-trf-gauss-spectral-coefficient-cartesian.json: item, statement unchanged, four proof steps, split.
- dag/nodes/sec-trace-formula/lem-trf-spectral-completion-scalar-envelope.json: statement-only supporting lemma, unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-tate-finite-algebra-norming-evaluations.json: statement-only supporting lemma, unsplit, no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-norming-maps-cartesian-criterion.json: statement-only supporting lemma, unsplit, no Mathlib match.
- citations.json: verbatim statements supporting every citation in the item's steps.

Attachments: none. I searched the project WeilConjectures source for the blueprint id and the spectral-norm, norming-map and nonarchimedean orthogonal-basis concepts. Hits concern unrelated character orthogonality, algebraic Gauss lemmas and sheaf-theoretic cartesian squares; none states the item.

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Proposition 5.3.3/2, printed pp.214–215; Proposition 3.8.1/7 and the localization remark, pp.171–174; Proposition 3.8.1/10, p.174; Theorem 5.2.6/2 and Corollary 5.1.4/6, for the three new nodes. The full book is absent from literature/. I read the primary Arizona scan at the URL in the node; the sandbox contains the page images used for reading, not a new repository archival entry.

The item had an empty proof. Its statement correctly distinguishes coefficient-field cartesianness from stability of the rational-function field; I retained it exactly. The proof may not cite lem-trf-gauss-rational-function-stability, which depends on this item. In particular the spectral completion need not be a field: the scalar-envelope node explicitly allows a reduced finite algebra. No statement dispute, no new hypotheses on the item, no SGA source, and no compiler invocation.

The assembly follows BGR 5.3.3/2. Its last appeal to 3.8.1/11 is expanded into norm-attaining evaluations (3.8.1/7) and the abstract linear argument in the proof of 3.8.1/10. This isolates a genuine analytic lemma from a general linear criterion instead of moving this item's conclusion into another node. The general criterion has neither a function field nor any algebra or stability hypothesis. The finite Tate evaluation lemma has no stability hypothesis and asserts no basis conclusion. The completion comparison has no coefficient field or basis conclusion.

Nothing remains unfinished for this one-level split; the three supporting statements intentionally remain unsplit for their own workers.

## Searches

All new searches were run through batch2/msearch.py; searches.jsonl contains their actual result records. Each new node records both semantic phrasings, a Loogle query and a Mathlib grep, exactly as run. No service was unavailable. Existing item searches were retained, and four fresh searches appended.

I read the relevant hits in Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean: norm_le_spectralNorm at line 444 gives one inequality; spectralAlgNorm at 663 supplies a field-extension norm; spectralNorm_unique at 699 requires a complete base and a field target. They do not give a reduced scalar-envelope algebra inside a completion, finite residue evaluations, or exact orthogonal bases. Module.Basis.norm_isNonarchimedean at FiniteExtension.lean line 90 starts with a basis and its coordinate norm, whereas the criterion requires a basis orthogonal for an already prescribed norm. The maximum-modulus grep hits in Geometry/Manifold/Complex.lean (line 54 onward) require complex differentiability. The algebraic-basis, normal-basis, inner-product and norm-equivalence hits do not specialize to the new statements.

Whole-DAG searches included the item id, spectral norm, cartesian/orthogonal bases, norming, BGR 3.8.1/7, /10 and /11, and the three proposed new ids. Whole-blueprint searches used blueprint_refs.py for cartesian, orthogonal basis, orthogonal, finite reduced algebra, finite algebra cartesian, spectral norm, maximum modulus, norming, norming evaluations and spectral completion. No imported node states a new lemma. The only imported orthogonal results concern additive characters. I read the latest blueprint proof of lem-trf-local-term-locality and the chapter/unit records: the current unit uses contracting correspondences. The present item is an existing historical analytic descendant of that node; this split changes neither the unit proof nor the chapter route. The new nodes inherit its ancestor and prepend the item to its via chain.

## Not duplicates

lem-trf-spectral-completion-scalar-envelope vs lem-trf-weak-spectral-completion-product: the latter assumes product-topology bounds and produces a finite product over the completed field. The new node assumes no weak stability, allows an intermediate field Q inside the completion, and compares the spectral norm on its finite scalar envelope with the original norm.

lem-trf-spectral-completion-scalar-envelope vs lem-trf-power-multiplicative-algebra-norm-unique: uniqueness there requires a complete base and a field target. Here Q may be incomplete and M may have several components.

lem-trf-tate-finite-algebra-norming-evaluations vs lem-trf-affinoid-supremum-seminorm-calculus: the existing node gives a supremum and says it is the Gauss norm on the Tate algebra itself; it gives neither attainment on a finite Tate model nor equality with the generic minimal-polynomial spectral norm. Its affinoid norms may vanish on nilpotents. The new node requires reducedness and torsion-freeness and supplies precisely these missing assertions.

lem-trf-tate-finite-algebra-norming-evaluations vs lem-trf-tate-galois-trace-supremum-bound: the existing trace estimate is for normal affinoid domains in a finite Galois setting, not arbitrary finite reduced torsion-free models and their attaining evaluations. No Galois hypothesis is available here.

lem-trf-norming-maps-cartesian-criterion vs lem-trf-cartesian-subspace: the existing node assumes the ambient space already has a finite orthogonal basis. The new criterion constructs bases using contractive norm-attaining maps; U need not be finite-dimensional.

lem-trf-norming-maps-cartesian-criterion vs lem-trf-cartesian-subspace-scalar-tower: the existing node concerns subspace permanence and restriction along an isometric field extension. The new criterion concerns a family of maps which can have kernels and differing finite targets.

## Review by O2

I read BGR Proposition 5.3.3/2 across printed pp.214–215 (scan pages 220–221). Its assumptions are stability of the complete coefficient field and a finite extension of the Gauss rational-function field; it does not require a divisible value group or separability. Its conclusion is k-cartesianness, exactly the finite-subspace statement here. I also read Proposition 3.8.1/7 and its proof on pp.171–173, its localization remark across pp.173–174, and Proposition 3.8.1/10 and /11 on p.174 (scan pages 179–182). The finite-model evaluation statement uses /7 and the remark, while the criterion is explicitly an agent generalization of the linear argument in /10. The completion comparison comes from the completion diagram and both spectral inequalities in the proof on p.215. All three new files are self-contained statement-only nodes, with inline meanings for their extra notions and the appropriate existing definition dependencies. There is no new definition and no step over 2000 characters.

Step 1 cites restricted-series-gauss-completion for completeness and polynomial-truncation convergence, tate-gauss-multiplicative for multiplicativity, and the new spectral-completion-scalar-envelope for the finite reduced Q-algebra and equality on E. I opened those statements and they give exactly those assertions. The polynomial fraction inclusion in the common completion is justified in the step by the displayed inverse-denominator estimate; it does not assume Q complete, M a field or weak stability. The definition of the Tate ring is already in the completion statement and the new lemma's dependencies.

Step 2 is elementary algebra: independently multiply each finite-basis vector by a nonzero polynomial clearing its minimal-polynomial coefficients, then reduce powers by the resulting monic equations. This preserves an R-basis, produces a finite T-module, and verifies all the reducedness, injection and torsion-free hypotheses needed in step 3. Since M is reduced, its subring A is reduced. Since nonzero t in T is invertible in Q, it acts injectively on M and hence on A. Products of basis vectors stay in E, so their finite Q-span M is generated by the same integral elements; no primitive element or separability is used.

Step 3 cites the new Tate evaluation lemma for contractivity and attainment, incomplete-spectral-algebra-norm for the finite target norm axioms, stable-nonarchimedean-field for the orthogonal basis of each finite target, and the new norming-maps criterion for the finite-subspace conclusion on A. I read all four statements. In particular stability applies to finite extensions of k, not to Q or R. Positivity and attainment identify sigma on A with the supremum of these evaluations; this explicitly verifies the norm hypothesis of the criterion rather than presuming a field norm on M. Completeness and nontriviality of k, finiteness, reducedness and T-torsion-freeness are all available. The map chi_a is k-linear since it is a k-algebra homomorphism.

Step 4 chooses a denominator in k[X], not merely in T. This matters: sigma is known to equal the original s only on E, not on all of M. I corrected my draft to clear the finitely many R-coordinates of the chosen V in the integral R-basis, so tV is contained in A intersect E. The equality on E from step 1 therefore applies to every vector of tV. The only cited statement is incomplete-spectral-algebra-norm for scaling by t inverse. The remaining equality is written out and finite-dimensional linear algebra proves that the pulled-back vectors are a basis. There is no unsupported transport of spectral norms.

Small cases checked: V=0 and dimension one; E=R (clearing ordinary rational-function denominators); inseparable extensions (no splitting-field or primitive-element argument); a reduced product Tate model A=T times T (sigma is the maximum of factor values and the attaining evaluation may select either factor); n=0 in the supporting Tate lemma; and a nilpotent algebra, which is excluded there because strict positivity would otherwise be false. For the norming criterion U=0 is vacuous and every nonzero vector has a nonzero norm-attaining image; no injectivity of the evaluation is asserted. The completion lemma permits products and does not conflate a power-multiplicative spectral norm with a multiplicative field absolute value.

Citations.json copies the entire relevant node statement for every use, so the reviewer can check both the claimed clause and its hypotheses. No maintainer fields, chapter or unit file were edited; the direct-delivery brief assigns this self-review to O2 and no second agent was started.
