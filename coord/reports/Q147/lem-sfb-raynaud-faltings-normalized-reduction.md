# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-raynaud-faltings-normalized-reduction.json: statement, split into nine proof steps; original statement preserved verbatim.
- dag/nodes/sec-six-functors-basics/lem-sfb-epp-essentially-finite-type-traits.json: statement-only, unsplit; no Mathlib match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep.
- citations.json: one verbatim statement quotation for every step/node citation.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, Raynaud, Faltings and reduced-fibre names; the sole Raynaud hit is a flattening discussion in Compactification/EliminationOfIndeterminacy.lean. Searched both project roots for Epp and the new id: no declaration. The inherited Mathlib searches concern normalization constructions, not the extension-existence theorem. Read the ramification search hit at Mathlib/RingTheory/RamificationInertia/Ramification.lean:90–115: its ramification-index conclusion assumes unramifiedness and gives no Epp extension.

## Sources and requests

WANTED: Prasad–Yu, On quasi-reductive group schemes, arXiv math/0405381, Appendix A.2, A.6, A.7–A.10, for lem-sfb-raynaud-faltings-normalized-reduction (local archival copy). Read the primary PDF online at https://arxiv.org/pdf/math/0405381 . It confirms the original statement and explains that generic smoothness of the normalized special fibre suffices. The delivered proof instead uses the locally available Stacks argument at Tag 09IL, below the fixed unit route. No missing document is used as an unproved citation in a step; proof_origin is agent because this is an explicit algebraic assembly and specialization.

For the new input read more-algebra.tex: Tag 09II (proposition-epp-essentially-finite-type), Tag 0GLR (lemma-solution-goes-up), Tag 09EM (remark-construction), Tag 09E7 (lemma-extension-dvrs-formally-smooth), and algebra.tex Tag 030U (lemma-separable-extension-preserves-reducedness). Together these assert exactly the local theorem, including all further finite extensions and reduced residue tensors. Complete lower DVR implies its integral closure in each finite extension is one DVR. There is no perfect-residue-field or mixed-characteristic restriction in 09II. The reduced generic tensor in the new statement is essential when the extension is inseparable.

## Corrections and blueprint comparison

The imported item had no proof. Its statement is correct, including the zero algebra and the absence of separability restrictions; no STATEMENT-DISPUTED correction is needed. The mixed-characteristic/perfect-residue Epp nodes cannot supply its local input. New local Epp is strictly smaller than this global algebra theorem: it concerns an essentially finite type local extension of DVRs and says nothing about normalizing an entire finite type model or excluding embedded fibre nilpotents.

Read the chapter and unit records and the latest blueprint files under literature/blueprint/latest, including sk-thm-sf-ctf-stability-direct-images.proof.md. The current proof (3) is the proper/open compactification assembly. The long historical creation chain connects this auxiliary input to its alteration prerequisites; it does not mean that current blueprint (3) itself states Epp. tools/blueprint_refs.py ancestor reports None because that creation chain is broken upstream; preserved the null ancestor and copied the historical via chain, adding this item for the new node. Searched the whole blueprint for Epp, essentially of finite type, reduced fibres, discrete valuation and normalization; no imported node states the new local theorem. No chapter or unit route is changed.

## Unfinished work

No part of the item's proof remains unfinished. The single new local Epp theorem is deliberately statement-only and joins the stage-1 queue. No Lean was written and no compiler, Lake or local preflight was run.

## Review by Q147

I checked B–E against the actual node statements and sources, not only the JSON format. The new node introduces D, T, F, H, the finite extensions, both integral closures and both residue fields. It defines essentially finite type and reduced inline and cites the notions it uses. The source tags and labels above were verified in the local tag table. I checked all search results: neither the unramifiedness tests nor the ramification index formulas produce the extension required by Epp. The local statement has no proof or proof dependencies.

Step 1 uses the flat-module definition to tensor multiplication by pi, the DVR definition for a uniformizer, and the normal-ring definition for reducedness. The zero-algebra conclusion is direct. Step 2 uses finite-type Noetherianity, the stated total-fraction product theorem, complete-local Nagata, and Nagata universally Japanese for each domain quotient. The latter explicitly gives finite integral closure even for the identity fraction-field extension. Projection and product of monic equations justify the finite product construction; this is not an uncited normalization theorem.

Step 3 uses normal-ring integral closedness in the total fraction ring, the normal/finite-product equivalence, the integral-closure-in-normal-product theorem, finite-algebra Noetherianity and torsion-free-over-PID flatness. Each theorem's hypotheses hold: A and A_K are Noetherian, A_K is normal by assumption, the ambient product factors are normal domains, and A^nu embeds in A_K. The PID condition follows directly from the DVR definition. In Step 4 the finite-minimal-primes node supplies finiteness, the principal ideal height bound supplies height at most one, and nonzero pi supplies the reverse bound. The one-dimensional normal-local theorem then really gives DVRs. I corrected an initially guessed nonexistent principal-ideal node id to the existing Mathlib leaf lem-sfb-krull-principal-ideal-height-bound, and removed an unnecessary associated-prime assertion from that step. Each T_i is a prime localization of the finite type algebra N_j, so the new local Epp theorem applies with no hidden excellence or perfectness assumption.

Step 5 uses exactly the complete-DVR normalization theorem (finiteness, locality, completeness and uniqueness), the common finite trait extension theorem (valid with arbitrary residue field), and the new Epp theorem's quantifier over further finite extensions. The empty-family case is stated explicitly. Step 6 reuses Steps 2–3 with R and E_R, checks flatness by the explicit tensor identification, and invokes finite-algebra integrality and transitivity to prove equality of the two integral closures. The common-extension output makes R finite over D; monomials in finite module generators give the stated finite-over-N conclusion.

Step 7 uses the normal product decomposition, flat going down to identify the generic component contraction, and integral going down over a normal domain to bound the vertical prime's contracted height. I checked the domain and injectivity conditions before applying the latter theorem. Step 8 uses the actual integral-closure localization statement, not an isomorphism borrowed from its proof: S-localization changes N_j to T_i and its generic localization to H_i; transitivity makes the larger-base and smaller-base closures identical. The generic tensor is reduced by geometric normality, so it agrees with the reduced tensor used by the new Epp node. Localizing at q therefore gives precisely its DVR, maximal-ideal equality and reduced residue tensors.

Step 9 uses the associated-height theorem only on each normal domain factor C_b, with nonzero rho. Height-one primes containing rho are minimal over rho, so the finite-minimal-primes theorem makes the relevant product finite. The associated-prime theorem supplies the displayed injection. I added the existing every-module-over-a-field-is-flat leaf so that tensor-injectivity is applied under an explicit cited flatness hypothesis. Finite products commute with tensor by writing them as finite direct sums; a nilpotent then dies in every reduced factor. This proves geometric reducedness, not only ordinary reducedness. All citations have verbatim quotations in citations.json. Off-unit statements are declared as generic algebra tools in split_report.tool_uses.

Tested E=0, E=D, E=D[x], E=F=D[1/pi] (empty special fibre), and E=D[x,y]/(xy-pi^e). For E=D[x]/(x^e-pi), with e invertible in D, the generic fibre is geometrically normal and a splitting finite extension produces normalization R^e, so the reduction is reduced as required. For the new local input T=D the identity extension works. In equal characteristic p, T=D[pi^(1/p)] shows why an inseparable extension must be allowed; choosing that extension removes the ramification in the reduced tensor. These cases expose the missing hypotheses in the existing mixed-characteristic Epp alternatives but do not contradict the new theorem. None of the nine steps exceeds 2000 characters or hides a separately assumed comparison: the normalization and localization identifications are proved inline from cited ring lemmas. No SGA source is used.

## Not duplicates

lem-sfb-epp-essentially-finite-type-traits vs lem-pc-separable-tensor-algebraic-closure: existing concerns Tensor product of a finite separable field with an algebraic closure; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-per-complete-dvr-finite-normalization: existing normalizes only the lower complete DVR in a finite field extension; new eliminates ramification for a second, essentially finite type upper DVR.

lem-sfb-epp-essentially-finite-type-traits vs lem-per-epp-common-finite-trait-extension: existing constructs a common finite lower trait and contains no elimination of upper-trait ramification; new supplies each individual Epp solution.

lem-sfb-epp-essentially-finite-type-traits vs lem-per-galois-epp-reduced-fibre-cover: existing concerns Galois Epp preparation with reduced special fibre; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-abhyankar-local-maximal-ideal: existing concerns Abhyankar maximal-ideal equality for a local DVR compositum diagram under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-abhyankar-local-residue: existing concerns Abhyankar residue separability for a local DVR compositum diagram under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-abhyankar-normalized-factor-index-one: existing concerns Index one after a sufficiently ramified DVR base change under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-galois-components-root-cotangent: existing concerns First-order root calculation for finite Galois field components under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-galois-components-root-not-square: existing concerns Nonzero first-order tame root class for finite Galois components under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-galois-root-factor-uniformizer: existing concerns A tame root generates the maximal ideal in an integral-closure tensor factor under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-normalized-compositum-local-diagram: existing concerns Compatible local DVR diagram of a finite normalized compositum under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-normalized-tensor-factor-lift: existing concerns Lifting a normalized tensor factor along a finite DVR extension under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-root-normalization-maximal-ideal: existing concerns Tame torsor ramification is killed by the group-order root over a DVR under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-tame-tensor-factor-maximal-ideal: existing concerns Maximal ideal equality after tame DVR base change under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-tame-tensor-factor-ramification-bound: existing concerns Quantitative ramification bound for a tame normalized tensor factor under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-tame-tensor-factor-residue-separable: existing concerns Residue separability after tame DVR base change under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-tame-tensor-factor-unramified: existing concerns Abhyankar base change for a finite DVR extension with given tame bounds under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-uniformizer-root-compositum-formally-unramified-data: existing concerns Formal unramifiedness data for the normalized root compositum under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-uniformizer-root-compositum-maximal-ideal: existing concerns Weak unramifiedness in the uniformizer-root compositum under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-uniformizer-root-compositum-residue: existing concerns Residue separability over a uniformizer-root DVR base under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-dvr-unramified-compositum-base-change: existing concerns Arbitrary DVR base change of a local unramified field compositum under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-radicial-reduced-flat-generic-fibre: existing concerns Radicial reduced generic fibre under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-root-normalization-cotangent-root: existing concerns Root class spans the normalized stalk cotangent space under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-root-normalization-generic-stalk-maximal-ideal: existing concerns Maximal-ideal equality after the group-order root extension under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-root-normalization-generic-stalk-residue-separable: existing concerns Separable normalization residue fields after the group-order root extension under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sbc-root-normalization-root-not-square: existing concerns The tame root has nonzero first-order class under specified tame, root, torsor, or pre-existing unramifiedness hypotheses; new constructs a wild Epp extension for an arbitrary essentially finite type DVR extension, allowing inseparability.

lem-sfb-epp-essentially-finite-type-traits vs lem-sfb-separating-stein-generic-curve: existing concerns Separating function fields and the geometrically integral generic curve; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-finite-eta-modification-spreading: existing concerns Spreading finite generic modifications from a valuation subring; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-geometric-reducedness-finite-inseparable-test: existing concerns Finite purely inseparable extensions test geometric reducedness of any algebra; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-geometric-reducedness-separable-scalar-restriction: existing concerns Geometric reducedness under restriction along a separable algebraic field extension; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-geometrically-integral-curve-factorization: existing concerns Factorization with a geometrically integral generic curve; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-separable-closed-point-formal-presentation: existing concerns Formal presentation and differential comparison at a separable closed point; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-separable-evaluation-local-base-change: existing concerns Local field extension at a specified separable evaluation point; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-finite-separable-tensor-field-reduced: existing concerns A finite separable field extension tensored with a field extension is reduced; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-separable-field-geometrically-normal: existing concerns Separable fields are geometrically normal; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-separable-polynomial-quotient-reduced: existing concerns The quotient of a polynomial ring over a field by a separable polynomial is reduced; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-separably-generated-separable: existing concerns A separably generated field extension is separable; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-separably-generated-tensor-reduced: existing concerns Tensor product of a separably generated field extension with a reduced algebra is reduced; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-separating-transcendence-basis-finite-subextension: existing concerns Finitely many elements of a separably generated extension lie in a finite separable extension of a finitely generated purely transcendental subfield; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-weil-pbc-squarefree-polynomial-divides-power: existing concerns A squarefree polynomial divides a power only when it divides its base; it does not construct a finite lower-field extension eliminating ramification for an arbitrary essentially finite type DVR extension and all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-per-epp-single-trait-base-change: existing assumes mixed characteristic and a perfect lower residue field plus a perfect-core hypothesis; new assumes essential finite type of the upper DVR and permits every characteristic and imperfect residue fields. Neither is a one-line specialization of the other under its stated hypotheses.

lem-sfb-epp-essentially-finite-type-traits vs lem-per-epp-finite-family-traits: existing is a simultaneous mixed-characteristic perfect-residue theorem with perfect-core hypotheses; new is a one-trait essentially finite type theorem without those characteristic restrictions and includes all further finite extensions.

lem-sfb-epp-essentially-finite-type-traits vs lem-trf-valuation-reduced-fibre-normalization: existing assumes a separably closed generic field and constructs a whole finite flat algebra; new starts with a complete DVR fraction field and constructs a finite field extension for a local upper trait.
