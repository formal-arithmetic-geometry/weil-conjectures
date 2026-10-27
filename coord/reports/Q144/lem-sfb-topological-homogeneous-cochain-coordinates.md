# Repair of lem-sfb-topological-homogeneous-cochain-coordinates

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-topological-homogeneous-cochain-coordinates.json: statement unchanged; four-step assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-joint-continuous-coordinate-equivalence.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-joint-continuous-coordinate-differential.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-joint-continuous-coordinate-naturality.json: statement, unsplit; no exact Mathlib match.
- citations.json: one verbatim statement quotation per cited node per parent step.

## Attachments

None. Rep.exists_homogeneousCochains_inhomogeneous_coordinates (WeilConjectures/RepresentationTheory/HomogeneousInhomogeneousContinuousCohomology.lean:55) needs compact Hausdorff totally disconnected J and discrete integer coefficients with open stabilizers. It does not cover arbitrary topological E-vector coefficients. The parent's Sheaf existence and naturality declarations (lines 128, 157) still have sorry (lines 137, 184).

## WANTED

None. The source is available locally; the homogeneous conversion is explicitly agent-formulated, not attributed as a theorem to Stacks.

## What was wrong and what changed

The return asks to spread 5215 characters of proof into at least two comparable statement-only jobs. The initial sandbox contained only dispatcher .brief markers, so I copied the current returned node from the read clone. Its statement and all maintained metadata are retained. Three new nodes now own the distinct arguments below, with no proof steps or proof dependencies. The parent has fewer than 3000 characters of assembly. No statement dispute or change of route is needed.

The repository's prior Mathlib searches and their results are retained on the parent. For each new node I ran both semantic phrasings, Loogle and source grep through msearch.py, read their outputs, and recorded their actual log entries. One LeanSearch query for the equivalence was rate limited and is recorded unavailable. Nearby continuous-cohomology results are iterated-map constructions; groupCohomology results use unrestricted functions. Fin.partialProd_contractNth proves only the internal tuple identity, and shearMulRight only a coordinate homeomorphism. None is a one-line match for a whole new obligation.

## Unfinished work

The three new statements intentionally remain unsplit for other stage-1 workers. The initial repair-session dry run passed on the current server base at 804be665fac. The final edited package is checked again before pushing. No Lean was written, compiled, or built.

## Review by Q144

I read Stacks etale-cohomology.tex, section-continuous-group-cohomology (Tag 0DVG), lines 9007–9040, for the parent and all three new nodes. It explicitly permits arbitrary topological abelian coefficients and gives precisely the inhomogeneous differential and gv-v. The homogeneous formula and its checks are agent arguments; the node sources say so. I read the current blueprint ancestor's direct-image proof paragraph (3), the chapter and inherited unit: this is still the arithmetic transfer input beneath coefficient comparison, and no chapter or unit route is changed. The blueprint_refs ancestor command returns None through legacy creation metadata; The first dry run required the children to use the computed null ancestor, which is the explicitly supported value for a broken created.item chain in tools/blueprint_refs.py. The chain terminates at lem-sfb-admissible-direct-image, whose created.item is the Lean module Sheaf.SixFunctors.CtfStabilityDirectImages rather than a node id. I therefore set the children's from.node to null, matching the actual ancestor command, while retaining the precise known blueprint paragraph in from.place and the complete existing via chain with this item prepended. The parent's existing concrete from.node remains unchanged. This records the inherited metadata defect without changing other workers' nodes or a tool.

For step 1 I checked that the equivalence node states continuity, equivariance, the pointwise vector-space structures, E-linearity, both inverses and the n=0 formulas. Its hypotheses are precisely the parent's: joint continuity of the action, continuous group operations, and continuous vector operations. It asserts no differential or derived conclusion. For step 2 I opened both new statements: the differential node supplies well-defined linear delta and d, delta squared zero and the explicit Phi-delta identity with first, internal and final faces; the equivalence node supplies exactly the inverse identities used to deduce d squared zero and the inverse cochain identity. These latter deductions and the negative-degree zero extension are written in the parent, rather than assumed. For step 3 I checked that the naturality node gives both induced maps, both differential identities and both coordinate squares for simultaneous h,u, not just an invariants functor or one coordinate arrow. Setting h or u to the identity gives the two operations requested by the parent. The restricted action is jointly continuous by composition with h×id, now written before the application in parent step 3; the child also states this clause. For step 4 I read the statement of def-weil-abstract-derived-category: it defines Q on complexes as a localization functor. Applying a functor to the inverse and commutative-square equalities needs no theorem about topological derived categories. The citation quotes are verbatim, and every non-elementary parent step cites its actual input statements.

For new-node self-containment I introduced every space and every formula in each statement; none assumes the parent. Topological field, group, and vector-space continuity conditions are stated inline; def-weil-field is used only for the underlying field notion, not as a purported definition of topology. I checked n=0 (empty ratios, Phi=F(1), Psi(v)(x)=xv, no internal faces, dv=gv-v), n=1 (the internal omission merges g1,g2 with sign -1), trivial J (d and delta alternate zero and identity), V=0, trivial actions, characteristic two (paired signs still sum to zero), and a noncommutative group (ratios and products retain their order). Joint continuity of Psi uses the action on J times V, and does not assert that any iterated continuous-map space is a joint-map space. Coefficient naturality requires u(h(a)v)=a u(v), exactly the stated intertwining hypothesis. No completeness, local compactness, compactness, Hausdorffness or discreteness is used.

The B–E audit found no missing citations, cycle, borrowed proof-only construction, unsupported source attribution, or extra hypotheses. All new dependencies are the field definition only, so they cannot depend back on the parent. The explicit re-split instruction authorizes extracting these finite calculations as parallel obligations even though the earlier split called each small part elementary. No single child restates the full parent: none gives its natural derived cochain isomorphism. The three jobs separate inverse-coordinate, signed differential, and naturality arguments. No non-elementary parent step exceeds 2000 characters.

## Landing-refusal repair (2026-10-22)

The current return is the landing refusal for returned head 36cb35b2ed7, recorded in coord/returns/Q144.md at 06:54 UTC. I continued the retained delivered sandbox rather than regenerating its nodes or search history. The required initial dry run rebuilt it on the current origin/sheaf-dag and passed at 804be665fac. The released stage-1 repair note still requires at least two comparable new obligations and an assembly under 3000 characters; the existing reviewed record does not cancel that order.

I compared every field of the retained item with the current read-clone item: only proof, proof_deps and split_report differ. In particular statement, stmt_deps, source, blueprint, proof_origin, searches, Lean record and maintained reviews agree. The current main node still has the twelve-step proof preserved below; none of the three retained children exists on main. Thus the three obligations and their argument ownership remain needed. I re-read both external cited statements, def-weil-field and def-weil-abstract-derived-category, as well as each of the three child statements. The field node defines the underlying field; the derived-category node explicitly provides the localization functor on abstract complexes. Their present statements support exactly the uses recorded here; no different theorem or topological derived category is being substituted.

I adjusted assembly step 3 to construct joint continuity of the restricted action before applying naturality: (a,v) maps continuously to (h(a),v), followed by the given action. Its intertwining assumption with u=id is then literally the same expression on both sides. This removes the earlier wording that described restricted continuity as a hypothesis supplied by the lemma. I also expanded the first citation quotation from just vector-space closure to the full inverse linear-map assertion, including continuity and degree zero. All changes are confined to the sandbox; deliver.py carries current maintained metadata onto its fresh base. The existing search questions and three child statements are unchanged, so their logged search results are reused.

## Preservation of the returned proof

The following text preserves every original argument verbatim. Ownership is: old step 1's vector-space part goes to the equivalence node and its delta part to the differential node; step 2 and steps 7–8 go to the differential node; steps 3–6 go to the equivalence node; step 9's well-definedness goes to the differential node and its transport and zero extension remain in parent step 2; steps 10–11 go to the naturality node; step 12 remains in parent step 4. The simultaneous h,u statement also records the combined version of the two old naturality arguments. These are report notes for future workers, not proofs inside the statement-only node files.

### Old step 1

Pointwise addition and scalar multiplication preserve continuity and equivariance, since addition and scalar multiplication in the topological vector space are continuous and the action is E-linear. Thus each B^n is an E-vector subspace of all functions on J^{n+1}; the same argument gives the pointwise vector space C^n. Here E is a field in the sense of [def-weil-field]. Each coordinate omission is continuous and commutes with simultaneous left multiplication, so the finite alternating sum defining δ maps B^n into B^{n+1} and is E-linear.

### Old step 2

The homogeneous differential squares to zero by pairwise cancellation. For each pair of original positions 0≤i<j≤n+2, deleting i first and then position j−1 has coefficient (−1)^{i+j−1}; deleting j first and then i has coefficient (−1)^{j+i}. These two terms evaluate F on the identical tuple and sum to zero. Every term in δδF occurs in exactly one such pair. This proves δ²=0 without any assertion about resolutions.

### Old step 3

Write P_n(g)=(p_0,...,p_n), with p_0=1 and p_i=g_1⋯g_i. Each p_i is continuous: p_0 is constant and p_{i+1}=p_i g_{i+1}, so induction uses continuous multiplication and coordinate projections. Hence P_n is continuous for the finite product topology. Define Φ_n(F)=F∘P_n. It is continuous and E-linear in F. For n=0, the domain J^0 is a point and this is Φ_0(F)=F(1) in V.

### Old step 4

For a tuple x=(x_0,...,x_n) set r_i=x_{i−1}^{−1}x_i for 1≤i≤n. Each r_i is continuous by continuous inversion and multiplication. Thus x↦(x_0,f(r_1,...,r_n)) is continuous, and the assumed jointly continuous action makes Ψ_n(f)(x)=x_0 f(r_1,...,r_n) continuous. Moreover (ax_{i−1})^{−1}(ax_i)=r_i and (ax_0)w=a(x_0w), proving equivariance. E-linearity of the action proves E-linearity of Ψ_n. The empty-ratio case gives Ψ_0(v)(x_0)=x_0v.

### Old step 5

At x=P_n(g), one has x_0=1 and x_{i−1}^{−1}x_i=p_{i−1}^{−1}(p_{i−1}g_i)=g_i. Substitution into Ψ gives (Φ_nΨ_nf)(g)=1 f(g_1,...,g_n)=f(g). This includes n=0 and proves Φ_nΨ_n=id by equality of functions.

### Old step 6

Conversely, the cumulative products of r_i=x_{i−1}^{−1}x_i telescope: r_1⋯r_i=x_0^{−1}x_i. Therefore P_n(r)=(x_0^{−1}x_0,...,x_0^{−1}x_n). Equivariance of F gives (Ψ_nΦ_nF)(x)=x_0 F(x_0^{−1}x_0,...,x_0^{−1}x_n)=F(x). This also holds for the single-coordinate tuple when n=0. Thus Ψ_nΦ_n=id; Φ_n and Ψ_n are inverse E-linear maps.

### Old step 7

Fix n≥0, F∈B^n and g=(g_1,...,g_{n+1}), and evaluate δF at P_{n+1}(g)=(1,p_1,...,p_{n+1}). Its omission of position 0 is F(p_1,...,p_{n+1}). This tuple equals g_1 times (1,g_2,g_2g_3,...,g_2⋯g_{n+1}); hence equivariance identifies the term with g_1(Φ_nF)(g_2,...,g_{n+1}). Its sign is +1. For n=0 this reads F(g_1)=g_1F(1).

### Old step 8

For an internal position 1≤i≤n, omitting p_i from (1,p_1,...,p_{n+1}) is exactly the cumulative-product tuple of (g_1,...,g_ig_{i+1},...,g_{n+1}): the cumulative products up to i−1 are unchanged, the next is p_{i−1}(g_ig_{i+1})=p_{i+1}, and the later ones are unchanged. Its sign is (−1)^i. Omitting the final position leaves P_n(g_1,...,g_n), with sign (−1)^{n+1}. Adding these terms and the first omission of Step 7 gives Φ_{n+1}δF=dΦ_nF. For n=0 there are no internal positions and this gives (dv)(g)=gv−v.

### Old step 9

The displayed d is well-defined and E-linear: its first term uses the jointly continuous action composed with continuous coordinate projections and f; each other term is a continuous f composed with a continuous multiplication/projection map; the sum is finite. Steps 5–8 give d=Φ_{n+1}δΨ_n. It follows that d²=Φ_{n+2}δ(Ψ_{n+1}Φ_{n+1})δΨ_n=0 by Step 2. Thus C is indeed a cochain complex. Also Ψ_{n+1}d=Ψ_{n+1}Φ_{n+1}δΨ_n=δΨ_n. Extending both maps by the unique map on zero spaces in negative degrees gives inverse E-linear cochain maps Φ and Ψ, including the zero differential from degree −1.

### Old step 10

Let u:V→W be a continuous equivariant E-linear coefficient map. Postcomposition defines maps on both kinds of cochains. It commutes with δ by linearity, and with d because u(gv)=gu(v). Evaluation gives Φ_n(u∘F)=u∘Φ_n(F). For the inverse formula u(x_0 f(r))=x_0 u(f(r)), so Ψ_n(u∘f)=u∘Ψ_n(f). These are equalities of the specified continuous functions, proving coefficient naturality for both cochain isomorphisms.

### Old step 11

For a continuous homomorphism h:H→J, use the H-action a·v=h(a)·v. Homogeneous restriction is F↦F∘h^{n+1}; inhomogeneous restriction is f↦f∘h^n. They preserve continuity and commute with the differentials: omission commutes with h coordinatewise, and h(ab)=h(a)h(b) identifies every internal product and the action term. Since h(1)=1, h(g_1⋯g_i)=h(g_1)⋯h(g_i), and h(a^{−1}b)=h(a)^{−1}h(b), direct substitution gives Φ_H∘res_B=res_C∘Φ_J and Ψ_H∘res_C=res_B∘Ψ_J. The restricted action is jointly continuous by composition with h×id.

### Old step 12

Use the localization functor Q of [def-weil-abstract-derived-category] on the abstract E-vector-space complexes of Step 9. Functoriality gives Q(Ψ)Q(Φ)=Q(ΨΦ)=Q(id_B)=id_{Q(B)} and Q(Φ)Q(Ψ)=id_{Q(C)}. Thus Q(Φ) with inverse Q(Ψ) is the asserted isomorphism in D(E-Vect), represented by the actual cochain isomorphism already constructed. Applying Q to the equalities in Steps 10–11 proves the same naturality in the derived category. Only functoriality is used here, so no topological vector-space derived category or exponential law is involved.

## Not duplicates

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sfb-topological-homogeneous-cochain-coordinates: the child isolates the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module; the parent additionally assembles actual cochain inverses and a natural derived-category isomorphism, which the child does not assert.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sfb-procyclic-scalar-cochain-evaluation: the existing statement treats a two-term comparison for trivial scalar coefficients on Z_l with profinite parameters; the new statement treats the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-per-finite-quotient-cochain-colimit: the existing statement concerns Continuous cochains from finite quotients with varying coefficients with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-continuous-cochains-invariants-zero: the existing statement concerns Degree-zero cochains are invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-galois-units-homogeneous-comparison: the existing statement concerns Homogeneous and inhomogeneous unit cohomology for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-coinduced-homotopy-identity: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-etale-units-h2-reverse-embedding: the existing statement concerns Etale unit H2 embeds into Galois unit H2 for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-faithful: the existing statement concerns Scalar defects distinguish precisely Brauer classes for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-cochains-derived-invariants: the existing statement concerns Continuous cochains compute derived invariants for discrete profinite modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs def-sc-homogeneous-cochain-evaluation: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module without those assumptions.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-continuous-cochains-delta-functor: the existing statement concerns Continuous cochains form a delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-coinduced-continuous-acyclic: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-coinduced-homotopy-continuous: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing statement concerns Homogeneous cocycles and inhomogeneous two-cocycles for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-discrete-invariants-continuous-comparison: the existing statement concerns Derived invariants under an equivalence compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-continuous-cohomology-coefficient-equiv: the existing statement concerns Equivariant discrete coefficient equivalences preserve continuous cohomology across universes with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs def-sc-brauer-scalar-defect: the existing statement concerns Matrix scalar-defect realization of a continuous Galois class for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-coinduced-discrete-embedding: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-etale-units-two-cocycle-comparison: the existing statement concerns Etale unit cohomology and inhomogeneous cocycles for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-lifts: the existing statement concerns Locally constant conjugating matrix lifts for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing statement concerns Invariants of a transported resolution compute locally constant inhomogeneous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-exc-continuous-cochains-short-exact: the existing statement concerns Continuous cochains preserve short exact sequences of discrete modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module without those assumptions.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-cocycle-monomial-coefficients: the existing statement concerns Regular monomial coefficients for a continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-finite-galois-cocycle-data: the existing statement concerns Finite quotient data for a prescribed continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs def-sc-galois-units-two-cocycle-classes: the existing statement concerns Continuous inhomogeneous unit two-cocycle classes for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-surjective: the existing statement concerns Crossed products realize every continuous units class for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-amplification: the existing statement concerns Matrix amplification preserves scalar-defect realizations for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-invariants-zero: the existing statement concerns Degree-zero locally constant integer cochain homology is naturally invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-galois-units-scalar-coboundary: the existing statement concerns Equal homogeneous classes give a locally constant scalar coboundary for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-tensor-split: the existing statement concerns Equal scalar defects split the tensor product with an opposite algebra for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-galois-units-comparison: the existing statement concerns Central simple algebras and continuous Galois degree-two classes for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-discrete-resolution-continuous-cohomology: the existing statement concerns Invariants of a transported injective resolution compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-exists: the existing statement concerns Locally constant lifts of a matrix splitting for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-etale-galois-units-comparison: the existing statement concerns Etale multiplicative degree-two cohomology equals Galois cohomology for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-faithful-backward: the existing statement concerns Equal scalar-defect classes imply Brauer equivalence for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-exact: the existing statement concerns The locally constant integer cochain complex is additive and degreewise exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing statement concerns Every object embeds in one whose locally constant integer cochain complex is exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-effaceable: the existing statement concerns Effaceable locally constant integer cochain delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-structure: the existing statement concerns Construction of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing statement concerns Realization of continuous scalar cocycles for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-etale-stalk-continuous-cohomology: the existing statement concerns For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M. with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-homogeneous-cochain-evaluation-differential: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module without those assumptions.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-cocycle: the existing statement concerns Continuous homogeneous cocycle of matrix scalar defects for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module without those assumptions.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-unique: the existing statement concerns Uniqueness of the scalar-defect class for one algebra for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing statement concerns Descent of homogeneous cocycles through cohomology for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-locally-constant-cochains-degreewise-exact: the existing statement concerns Pointwise degreewise exactness of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-scalar-data: the existing statement concerns Scalar extraction and cocycle identity for matrix descent defects for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-etale-units-h2-forward-embedding: the existing statement concerns Galois unit H2 embeds into etale unit H2 for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing statement concerns Crossed-product realization data for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs lem-sc-brauer-scalar-defect-faithful-forward: the existing statement concerns Brauer equivalence preserves scalar-defect classes for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-equivalence vs def-sc-galois-units-cohomology: the existing statement concerns Second continuous Galois cohomology of separable-closure units for discrete Galois units or central simple algebras; it does not state the graded inverse linear coordinate formulas on jointly continuous functions for every topological group and topological field module.

lem-sfb-joint-continuous-coordinate-differential vs lem-sfb-topological-homogeneous-cochain-coordinates: the child isolates well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions; the parent additionally assembles actual cochain inverses and a natural derived-category isomorphism, which the child does not assert.

lem-sfb-joint-continuous-coordinate-differential vs lem-sfb-procyclic-scalar-cochain-evaluation: the existing statement treats a two-term comparison for trivial scalar coefficients on Z_l with profinite parameters; the new statement treats well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-per-finite-quotient-cochain-colimit: the existing statement concerns Continuous cochains from finite quotients with varying coefficients with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-continuous-cochains-invariants-zero: the existing statement concerns Degree-zero cochains are invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-galois-units-homogeneous-comparison: the existing statement concerns Homogeneous and inhomogeneous unit cohomology for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-coinduced-homotopy-identity: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-etale-units-h2-reverse-embedding: the existing statement concerns Etale unit H2 embeds into Galois unit H2 for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-faithful: the existing statement concerns Scalar defects distinguish precisely Brauer classes for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-cochains-derived-invariants: the existing statement concerns Continuous cochains compute derived invariants for discrete profinite modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs def-sc-homogeneous-cochain-evaluation: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions without those assumptions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-continuous-cochains-delta-functor: the existing statement concerns Continuous cochains form a delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-coinduced-continuous-acyclic: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-coinduced-homotopy-continuous: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing statement concerns Homogeneous cocycles and inhomogeneous two-cocycles for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-discrete-invariants-continuous-comparison: the existing statement concerns Derived invariants under an equivalence compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-continuous-cohomology-coefficient-equiv: the existing statement concerns Equivariant discrete coefficient equivalences preserve continuous cohomology across universes with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs def-sc-brauer-scalar-defect: the existing statement concerns Matrix scalar-defect realization of a continuous Galois class for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-coinduced-discrete-embedding: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-etale-units-two-cocycle-comparison: the existing statement concerns Etale unit cohomology and inhomogeneous cocycles for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-lifts: the existing statement concerns Locally constant conjugating matrix lifts for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing statement concerns Invariants of a transported resolution compute locally constant inhomogeneous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-exc-continuous-cochains-short-exact: the existing statement concerns Continuous cochains preserve short exact sequences of discrete modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions without those assumptions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-cocycle-monomial-coefficients: the existing statement concerns Regular monomial coefficients for a continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-finite-galois-cocycle-data: the existing statement concerns Finite quotient data for a prescribed continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs def-sc-galois-units-two-cocycle-classes: the existing statement concerns Continuous inhomogeneous unit two-cocycle classes for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-surjective: the existing statement concerns Crossed products realize every continuous units class for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-amplification: the existing statement concerns Matrix amplification preserves scalar-defect realizations for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-invariants-zero: the existing statement concerns Degree-zero locally constant integer cochain homology is naturally invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-galois-units-scalar-coboundary: the existing statement concerns Equal homogeneous classes give a locally constant scalar coboundary for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-tensor-split: the existing statement concerns Equal scalar defects split the tensor product with an opposite algebra for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-galois-units-comparison: the existing statement concerns Central simple algebras and continuous Galois degree-two classes for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-discrete-resolution-continuous-cohomology: the existing statement concerns Invariants of a transported injective resolution compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-exists: the existing statement concerns Locally constant lifts of a matrix splitting for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-etale-galois-units-comparison: the existing statement concerns Etale multiplicative degree-two cohomology equals Galois cohomology for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-faithful-backward: the existing statement concerns Equal scalar-defect classes imply Brauer equivalence for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-exact: the existing statement concerns The locally constant integer cochain complex is additive and degreewise exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing statement concerns Every object embeds in one whose locally constant integer cochain complex is exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-effaceable: the existing statement concerns Effaceable locally constant integer cochain delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-structure: the existing statement concerns Construction of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing statement concerns Realization of continuous scalar cocycles for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-etale-stalk-continuous-cohomology: the existing statement concerns For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M. with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-homogeneous-cochain-evaluation-differential: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions without those assumptions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-cocycle: the existing statement concerns Continuous homogeneous cocycle of matrix scalar defects for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions without those assumptions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-unique: the existing statement concerns Uniqueness of the scalar-defect class for one algebra for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing statement concerns Descent of homogeneous cocycles through cohomology for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-locally-constant-cochains-degreewise-exact: the existing statement concerns Pointwise degreewise exactness of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-scalar-data: the existing statement concerns Scalar extraction and cocycle identity for matrix descent defects for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-etale-units-h2-forward-embedding: the existing statement concerns Galois unit H2 embeds into etale unit H2 for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing statement concerns Crossed-product realization data for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs lem-sc-brauer-scalar-defect-faithful-forward: the existing statement concerns Brauer equivalence preserves scalar-defect classes for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-differential vs def-sc-galois-units-cohomology: the existing statement concerns Second continuous Galois cohomology of separable-closure units for discrete Galois units or central simple algebras; it does not state well-defined differentials, alternating-omission cancellation and the signed face comparison for arbitrary jointly continuous coefficient functions.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sfb-topological-homogeneous-cochain-coordinates: the child isolates simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas; the parent additionally assembles actual cochain inverses and a natural derived-category isomorphism, which the child does not assert.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sfb-procyclic-scalar-cochain-evaluation: the existing statement treats a two-term comparison for trivial scalar coefficients on Z_l with profinite parameters; the new statement treats simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-per-finite-quotient-cochain-colimit: the existing statement concerns Continuous cochains from finite quotients with varying coefficients with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-continuous-cochains-invariants-zero: the existing statement concerns Degree-zero cochains are invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-galois-units-homogeneous-comparison: the existing statement concerns Homogeneous and inhomogeneous unit cohomology for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-coinduced-homotopy-identity: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-etale-units-h2-reverse-embedding: the existing statement concerns Etale unit H2 embeds into Galois unit H2 for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-faithful: the existing statement concerns Scalar defects distinguish precisely Brauer classes for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-cochains-derived-invariants: the existing statement concerns Continuous cochains compute derived invariants for discrete profinite modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs def-sc-homogeneous-cochain-evaluation: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas without those assumptions.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-continuous-cochains-delta-functor: the existing statement concerns Continuous cochains form a delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-coinduced-continuous-acyclic: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-coinduced-homotopy-continuous: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-galois-units-homogeneous-cocycle-equivalence: the existing statement concerns Homogeneous cocycles and inhomogeneous two-cocycles for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-discrete-invariants-continuous-comparison: the existing statement concerns Derived invariants under an equivalence compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-continuous-cohomology-coefficient-equiv: the existing statement concerns Equivariant discrete coefficient equivalences preserve continuous cohomology across universes with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs def-sc-brauer-scalar-defect: the existing statement concerns Matrix scalar-defect realization of a continuous Galois class for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-coinduced-discrete-embedding: the existing statement concerns a discrete coinduced coefficient module for a profinite group and its embedding or contraction; the new statement proves simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas for arbitrary topological coefficients.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-etale-units-two-cocycle-comparison: the existing statement concerns Etale unit cohomology and inhomogeneous cocycles for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-lifts: the existing statement concerns Locally constant conjugating matrix lifts for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-discrete-resolution-inhomogeneous-cohomology: the existing statement concerns Invariants of a transported resolution compute locally constant inhomogeneous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-exc-continuous-cochains-short-exact: the existing statement concerns Continuous cochains preserve short exact sequences of discrete modules with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-homogeneous-inhomogeneous-continuous-cohomology: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas without those assumptions.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-cocycle-monomial-coefficients: the existing statement concerns Regular monomial coefficients for a continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-finite-galois-cocycle-data: the existing statement concerns Finite quotient data for a prescribed continuous Galois cocycle for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs def-sc-galois-units-two-cocycle-classes: the existing statement concerns Continuous inhomogeneous unit two-cocycle classes for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-surjective: the existing statement concerns Crossed products realize every continuous units class for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-amplification: the existing statement concerns Matrix amplification preserves scalar-defect realizations for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-invariants-zero: the existing statement concerns Degree-zero locally constant integer cochain homology is naturally invariants with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-galois-units-scalar-coboundary: the existing statement concerns Equal homogeneous classes give a locally constant scalar coboundary for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-tensor-split: the existing statement concerns Equal scalar defects split the tensor product with an opposite algebra for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-galois-units-comparison: the existing statement concerns Central simple algebras and continuous Galois degree-two classes for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-discrete-resolution-continuous-cohomology: the existing statement concerns Invariants of a transported injective resolution compute homogeneous continuous cohomology with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-exists: the existing statement concerns Locally constant lifts of a matrix splitting for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-etale-galois-units-comparison: the existing statement concerns Etale multiplicative degree-two cohomology equals Galois cohomology for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-faithful-backward: the existing statement concerns Equal scalar-defect classes imply Brauer equivalence for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-exact: the existing statement concerns The locally constant integer cochain complex is additive and degreewise exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-acyclic-embedding: the existing statement concerns Every object embeds in one whose locally constant integer cochain complex is exact with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-effaceable: the existing statement concerns Effaceable locally constant integer cochain delta-functor with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-structure: the existing statement concerns Construction of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-cocycle-realization: the existing statement concerns Realization of continuous scalar cocycles for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-etale-stalk-continuous-cohomology: the existing statement concerns For an abelian etale sheaf on Spec K whose geometric stalk identifies equivariantly with a discrete Galois representation M, its sheaf cohomology in every degree is equivalent to continuous cohomology of M. with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-homogeneous-cochain-evaluation-differential: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas without those assumptions.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-cocycle: the existing statement concerns Continuous homogeneous cocycle of matrix scalar defects for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-homogeneous-cochain-evaluation-bijective: the existing statement assumes compact Hausdorff groups and discrete integer coefficients and uses iterated continuous maps; the new statement covers simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas without those assumptions.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-unique: the existing statement concerns Uniqueness of the scalar-defect class for one algebra for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-galois-units-homogeneous-cocycle-descent: the existing statement concerns Descent of homogeneous cocycles through cohomology for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-locally-constant-cochains-degreewise-exact: the existing statement concerns Pointwise degreewise exactness of locally constant integer cochains with discrete or locally constant coefficients, invariants, exactness or cohomology; it does not give simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-scalar-data: the existing statement concerns Scalar extraction and cocycle identity for matrix descent defects for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-etale-units-h2-forward-embedding: the existing statement concerns Galois unit H2 embeds into etale unit H2 for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-surjective-crossed-product-realization: the existing statement concerns Crossed-product realization data for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs lem-sc-brauer-scalar-defect-faithful-forward: the existing statement concerns Brauer equivalence preserves scalar-defect classes for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

lem-sfb-joint-continuous-coordinate-naturality vs def-sc-galois-units-cohomology: the existing statement concerns Second continuous Galois cohomology of separable-closure units for discrete Galois units or central simple algebras; it does not state simultaneous coefficient/restriction compatibility of both explicit jointly continuous coordinate formulas.

Additional DAG candidates read: lem-sfb-bar-resolution-cochains is an algebraic free Z[G]-resolution, not a joint-continuity or naturality assertion; lem-sfb-internal-homogeneous-functions-injective is an injectivity theorem for condensed internal modules. Neither states any of the three new obligations. Whole-blueprint searches for homogeneous, cochain coordinates, cumulative and continuous cochains found no matching blueprint statement; the compact/discrete coordinate nodes are created nodes, not unrestricted replacements.
