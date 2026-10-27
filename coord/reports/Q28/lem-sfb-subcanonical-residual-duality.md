# Stage-1 delivery: lem-sfb-subcanonical-residual-duality

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-subcanonical-residual-duality.json: item, split into five explicit steps; original statement retained, two direct notion dependencies added.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-curve-torsionfree-biduality.json: statement-only prerequisite, unsplit; no Mathlib match after seven logged searches, including a second semantic phrasing and inspection of the reflexivity hits.
- citations.json: one verbatim statement quotation for each of the fifteen step citations.

One new node; zero Mathlib leaves. No Lean files written and no compiler invoked.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and residual-cluster/subcanonical notions. The subcanonical hits are Grothendieck-topology statements. Curve/RiemannRoch.lean proves invertible-module biduality, not biduality for the possibly noninvertible cluster ideal; it cannot attach this item.

## Literature wanted

WANTED: Franciosi–Tenni, On Clifford's theorem for singular curves, Proc. LMS 108 (2014), pp.225–252, Definition 2.10 and Remarks 2.11 and 2.13, for lem-sfb-subcanonical-residual-duality. The local PDF is missing. I read the author's primary PDF online at https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf, printed pp.231–232. The assembly is marked proof_origin.by = agent. No download or repository change was made.

## Problems corrected or clarified

The imported item was a statement with no proof. The potentially dangerous inference is treating I_S as invertible: it need not be, including at an ordinary node. I use canonical biduality for coherent modules without dimension-zero torsion instead, and compute the second evaluation map explicitly. The two-connectedness assumption is unnecessary for this lemma but is retained. The previous correction deleting splitting-index invariance is preserved; no r(S*) = r(S) assertion is reintroduced.

The existing blueprint ancestor is null: blueprint_refs.py ancestor reports None for this isolated new-target chain. The new node inherits exactly that ancestor and prepends the item to the existing via chain. Searches across the latest blueprint for residual, Serre duality, torsion-free, torsionfree, bidual, reflexive and 0B5A found no equivalent prerequisite. The whole DAG was searched for 0B5A, local-CM, torsion-free biduality and Gorenstein duality before creating it.

The statement and imported metadata are retained. The nodal-line-duality and closed-ideal nodes are now explicit statement dependencies, since the item actually uses their notions.

## Unfinished

Only the new prerequisite's proof is deferred, as required for a one-level split. Nothing in the item proof is deferred to a new node restating residual construction or any numerical clause.

## Not duplicates

No existing node has Tag 0B5A in its source and states canonical module biduality. The two existing nodes mentioning it in their metadata were read:

lem-sfb-reduced-curve-torsionfree-biduality vs lem-sfb-normalized-dualizing-depth-detection: the existing node detects depth by the nonvanishing degrees of RHom; it neither gives the canonical double-dual isomorphism nor sheaf coherence and generic-section detection.

lem-sfb-reduced-curve-torsionfree-biduality vs lem-sfb-normalized-cm-local-dualizing-concentration: the existing node concentrates the dualizing complex of the ring itself and describes its module; it does not dualize an arbitrary torsion-free coherent module.

lem-sfb-reduced-curve-torsionfree-biduality vs lem-sfb-reduced-curve-dualizing-module: the existing node constructs and characterizes the dualizing module, excludes its own finite-support submodules, and computes its Euler characteristic; it does not assert reflexivity of arbitrary torsion-free modules.

lem-sfb-reduced-curve-torsionfree-biduality vs lem-pc-tensor-dual-invertible: the existing node assumes invertibility, which cluster ideals at nodes do not satisfy.

## Review by Q28

I read Definition 2.10 and Remarks 2.11 and 2.13 in the author-hosted paper, and Stacks dualizing.tex Tag 0B5A (lemma-local-CM), including the final anti-equivalence assertion and the canonical bidual map in its proof, for the new node. I also read curves.tex Tags 0BS2–0BS4 and varieties.tex Tag 0AYT (lemma-chi-tensor-finite). I checked the three-level route rules, GOAL.md, the chapter and unit records, and delivery-errors B–E in both copies. This is a generic coherent-curve prerequisite of the same stable-curve/moduli route, with no coefficient-category substitution and no SGA source.

For Step 1 I opened all seven cited statements. Projective-implies-proper supplies properness; finite-type-over-Noetherian supplies Noetherianity over a field; the Euler well-definedness node gives finite dimensions; the cohomological dimension node gives the bound one; global-functions explicitly allows a reduced singular connected proper curve and gives H0(O)=k. Nodal-line Serre–Riemann–Roch supplies the invertible representing module and h0(omega)=h1(O). Reduced-curve dualizing-module supplies uniqueness and the Euler sign. These give p_a=g and chi(omega)=p_a-1 without invoking a smooth-only duality theorem.

For Step 2 I opened the closed-immersion ideal statement (affine ideals and quasi-coherence), coherent kernel/cokernel statement (quasi-coherent submodules of coherent modules are coherent), and reduced-curve dualizing-module statement (generic rank one and exclusion of punctual submodules). Local trivializations of omega preserve coherence and inclusions. Generic detection of a section of a line is also the elementary reduced-ring argument: its coefficient maps to zero in every minimal-prime field, so it belongs to the nilradical and is zero. The new biduality statement supplies coherence and generic detection for Hom(F,omega), plus its canonical evaluation isomorphism. Evaluation is injective because s is a basis at each component generic point; the image ideal construction is performed in local bases with unit transition factors, rather than cited as an unexplained residual theorem. A closed support on a Noetherian one-dimensional scheme missing all component generic points has dimension zero. Evaluating the original inclusion produces precisely s, proving subcanonicity.

For Step 3 I checked the exact formula in the new node, not just the existence of some abstract isomorphism. The transported double-dual sends f to the map alpha(phi) -> phi(f). Since alpha(inclusion)=s, evaluating it at s returns the original inclusion of f. Thus the double residual is the same ideal, including nonreduced structure. No new node is merely an involution clause of the item.

For Step 4 I opened zero-support Euler, Euler additivity, and nodal-line duality. The first applies to the coherent sheaf O_X/I_T, supported in dimension zero, and its tensor with a line; it gives the same Euler characteristic and the dimension of global sections. The quotient's global sections are Gamma(T,O_T) by the closed-subscheme definition. The ideal sequences are exact in local bases. Serre duality here explicitly quantifies over every coherent F, so both F and the coherent evaluation image G satisfy its hypotheses; the second Hom identification is supplied by Step 3 rather than by a local-freeness assumption. Vanishing above degree one was already established in Step 1. These facts give both Euler equalities and their sign reversal. Step 5 is only substitution and nonnegativity of dimensions; I checked the signs in the section difference and Clifford-index difference.

I tested the new statement on F=0, on a line, and on a sheaf supported generically on just one component; the hypothesis does not require positive rank on every component. At the completed node k[[u,v]]/(uv), the maximal ideal (u,v) is torsion-free but not free, so this is the essential non-Cartier test for canonical biduality. Its dual and double dual satisfy the stated conclusion by the one-dimensional Cohen–Macaulay duality in 0B5A; no normalization-as-line-bundle argument is used. For the item I checked S empty, the full zero divisor of s, and a length-one cluster at a node. Empty and full clusters give lengths 0 and 2g-2 and section dimensions g and 1. For a nodal genus-one curve s has no zero and only the empty subcanonical cluster occurs, agreeing with the formulas. At genus zero there is no generically nonzero canonical section, so the hypotheses with subcanonical S have no instance. Arbitrary characteristic is allowed by the Stacks duality route.

Every cited node's full statement is copied verbatim to citations.json, covering all clauses used. Every step is shorter than 2000 characters. New nodes have only statements and empty proofs. The Mathlib log records actual successful searches, not reconstructed queries: the candidate reflexivity declarations assume reflexivity or finite freeness, and PicardGroup applies to invertible modules. No candidate covers nonfree cluster ideals. Generic off-unit tools are declared in split_report.tool_uses for review. No statement dispute, dropped metadata, hidden residual-invariance claim, or cycle through the parent Clifford theorem was introduced.
