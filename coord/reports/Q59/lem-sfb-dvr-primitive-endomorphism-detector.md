# Worker report: lem-sfb-dvr-primitive-endomorphism-detector

## Files written

All node files are under `dag/nodes/sec-six-functors-basics/` in this sandbox.

- `lem-sfb-dvr-primitive-endomorphism-detector.json`: statement, split in five steps; the original statement is unchanged. No exact Mathlib match.
- `lem-sfb-dvr-rho-section-modules.json`: statement-only, unsplit; integral rho character and actual nonzero finite free section modules. No Mathlib match.
- `lem-sfb-dvr-rho-tensor-square-invariant-line.json`: statement-only, unsplit; integral rank-one invariant tensor square. No Mathlib match.
- `lem-sfb-dvr-rho-tensor-square-eventual-detection.json`: statement-only, unsplit; all sufficiently large weights detect a primitive fixed vector modulo the maximal ideal. No Mathlib match.
- `lem-sfb-dvr-rho-section-self-duality.json`: statement-only, unsplit; integral self-duality at all positive weights in residue characteristic zero, and the Steinberg weights in positive residue characteristic. No Mathlib match.
- `citations.json`: a literal statement excerpt for each of the four node citations in the item.
- `searches.jsonl` and `research-*.json`: searches actually executed by msearch.py and their returned hits. `research.py` and `write_split.py` are sandbox-only working scripts, not delivery files.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag, primitive fixed vectors, rho-section modules, Steinberg and geometric reductivity. The Steinberg hits are Lang--Steinberg for semilinear Frobenius, not the algebraic group-scheme representation assertion. There is no project declaration to attach.

## WANTED

WANTED: Alper, *Adequate moduli spaces and geometrically reductive group schemes*, published PDF (Algebraic Geometry 1 (2014), 489--531), Section 9.7, printed pp.526--528, local path `literature/alper-adequate-moduli-spaces.pdf`, for this item and all four new nodes. The local file is absent. Read the primary published PDF at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf and cross-checked the mathematical text at https://arxiv.org/html/1005.2398v3#S9.SS7. No download or repository literature edit was made. The item's proof_origin remains explicitly agent-written assembly, not a claim that the missing local document was read.

## What was wrong or incomplete

The item was unsplit and had no proof. Its primitive hypothesis already fixes the nonvanishing defect in the printed source; no statement correction is needed. Existing rho representation lemmas in the DAG are over an algebraically closed field. Their statements cannot be used to obtain an equivariant map over the DVR or an integral self-duality. In particular, a special-fibre map is not automatically liftable.

Alper's abstract isomorphism of the invariant module with the base ring does not by itself identify the identity matrix as a generator. Step 5 writes out the matrix-entry argument making that identification. Reduction nonvanishing is transported through actual inverse maps, not by asserting that taking invariants commutes with residue-field base change. The proof never assumes such a base-change theorem.

## Source error

Alper Lemma 9.7.2(2), as printed, allows an arbitrary invariant v. For v=0, or even v=pi*w for a uniformizer pi, every A-linear map sends v into the maximal ideal times the target, so its reduction is zero. The item already restricts to primitive v; the new detection node states this necessary restriction explicitly. This is a correction of the supporting source formulation, not a weakening of the assigned item. The PDF extraction also renders the second characteristic condition in Lemma 9.7.4 incorrectly; the arXiv HTML explicitly gives char(kappa)=p and m=p^nu-1. The new duality statement distinguishes characteristic zero from positive characteristic accordingly.

## Not duplicates

Searches ran over the full DAG by statement keywords and source lemma numbers, and over all imported blueprint nodes with blueprint_refs.py search: `Steinberg`, `rho`, `tensor-square`, `self-duality`, `semisimple simply connected`, `rho section`, `primitive fixed`, `9.7.2`, and `9.7.4`. The first rho search produced many unrelated occurrences in formulas; their titles and statements did not give an integral representation result. No new ID already occurs. The only same-source representation predecessors are the following field results.

lem-sfb-dvr-rho-section-modules vs lem-sfb-rho-section-modules: the latter assumes an algebraically closed field; the new result constructs the section modules over a nonfield DVR and proves finite freeness over that ring.

lem-sfb-dvr-rho-section-modules vs def-sfb-rho-section-module-data: this definition is explicitly over a field and defines the subspaces/action predicate; it does not prove integral rho existence or finite freeness over a DVR.

lem-sfb-dvr-rho-tensor-square-invariant-line vs lem-sfb-rho-tensor-square-invariant-line: the latter gives a dimension over a field; the new statement is freeness of the invariant A-module before reduction. No commutation of invariants with reduction is asserted.

lem-sfb-dvr-rho-tensor-square-eventual-detection vs lem-sfb-rho-tensor-square-eventual-detection: the latter gives maps of field representations nonzero at a vector; the new statement gives maps over A and requires a primitive vector and nonzero residual value. The field statement cannot lift those maps.

lem-sfb-dvr-rho-section-self-duality vs lem-sfb-rho-section-self-duality: the latter gives a field-linear isomorphism; the new statement requires an A-linear equivariant isomorphism, including mixed characteristic. A fibre isomorphism supplies no integral map.

lem-sfb-dvr-rho-tensor-square-eventual-detection vs lem-sfb-dvr-primitive-endomorphism-detector: detection only gives maps into a specified tensor square for large weights, with no self-duality or scalar endomorphism conclusion. The item must still select the right weights, form the endomorphism comparison, and prove the scalar-map assertion.

lem-sfb-dvr-rho-tensor-square-invariant-line vs lem-sfb-dvr-primitive-endomorphism-detector: the rank-one tensor invariant module does not identify scalar endomorphisms or give any detecting map; both are proved in the assembly.

lem-sfb-dvr-rho-section-self-duality vs lem-sfb-dvr-primitive-endomorphism-detector: self-duality concerns a specified family of section modules and says nothing about V, v or invariant endomorphisms.

lem-sfb-dvr-rho-section-modules vs lem-sfb-dvr-primitive-endomorphism-detector: this result only supplies actual finite free rational representations; it has no detecting map or scalar invariant conclusion.

The four new statements are independent prerequisites of the endomorphism construction, not renamed clauses of the item. The old field detector `lem-sfb-steinberg-endomorphism-detection` also cannot produce the integral objects. No same-Stacks-tag pair arises: the new sources are Alper's representation lemmas, not Stacks results.

## Review by Q59

I read the worker and stage-1 contracts, GOAL.md, the three levels of SETUP.md, the chapter and unit records, and delivery-errors B--E in both copies. I read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3); the existing ancestry records locate this as an invariant-theory prerequisite below that direct-image route. I did not change the chapter, unit route, statement, or source metadata of the item. The ancestor tool reports blueprint.from.node=None for this existing ancestry; new nodes retain this same value and extend the existing via list with the item, rather than inventing a blueprint ancestor.

For the item and each new node I read Alper's actual mathematical statements in Section 9.7. The section-module node spells out the character, extension, regular functions and left translation in the paragraph preceding Lemma 9.7.2; its nonzero finite free module conclusion is the integral section-module input used in the subsequent construction, exposed as its own unsplit theorem rather than hidden inside the assembly. The invariant-line node states exactly 9.7.2(1), with Remark 9.7.3 distinguishing integral invariants from a field dimension. The detection node states 9.7.2(2) with the indispensable primitivity condition. The duality node states the two cases of 9.7.4 as A-linear isomorphisms, not field-linear ones. All rational invariance and equivariance are coaction identities after every algebra extension. The sources are literature references rather than Stacks tags because these are Seshadri's representation-theoretic inputs, not results in Stacks. No SGA source is used.

In step 1 the cited new module statement actually supplies both the rho character/extension and nonzero finite free rational W_m; the citation excerpt includes both. H is already split semisimple simply connected, smooth affine finitely presented, and the given residue field is algebraically closed, exactly as required. In step 2 the detection statement gives all m above a threshold for the given finite free V and primitive fixed v. The self-duality statement gives the integral isomorphism at the SAME chosen weight. I checked the characteristic-p choice explicitly: p>=2 and p^r-1 is unbounded. No general positive-characteristic self-duality is assumed. The two cited conclusions are copied literally in citations.json.

Step 3 is elementary finite-basis algebra. I checked both inverse maps of theta, its equivariance on an arbitrary test algebra, and its matrix-entry reduction. It uses only the supplied finite free module and its dual; no theorem about invariant base change, derived tensor, or field rationality is implicit. Step 4 cites precisely the integral rank-one invariant statement, and restricts an equivariant isomorphism and its inverse to invariants. Step 5 has no uncited Schur lemma: a diagonal entry proves that the coefficient of a chosen rank-one generator is a unit. Positive rank, supplied in step 1, is exactly the hypothesis that guarantees this diagonal entry and faithfulness of the scalar map. These elementary steps are written in full, and each non-elementary step has the cited statement that it uses. All proof steps are below 2000 characters.

For small cases I checked H=1 (rho=0, W_m=A, detection is a coordinate functional taking a primitive vector to a unit), V=A with v a unit, rank-one W, residue characteristic two (m=2^r-1 remains positive and unbounded), and mixed characteristic. V=0 supplies no primitive vector, so detection is correctly vacuous. v=pi*w fails the source's unqualified formulation, as explained above. There is no statement about arbitrary m in characteristic p for duality. The module constructions are concrete submodules of A[H], not data chosen from an undetermined existence theorem.

I inspected all five recorded search batches, including the second semantic phrasings. Loogle's invariants and dual hits concern representations of abstract groups; LieModule weight results concern Lie algebras; Mathlib's free_of_finite_type_torsion_free still requires the finite-type module input and supplies none of the group-scheme/section-module assertions. The invariant-character hits require a finite group and an invertible group order. None is an exact match or a one-line specialization of a new node. New nodes have no proof, proof dependencies or proof origin. Their self-contained statements introduce A, kappa, H, T, B, the actual W_m, coactions, the relevant vectors, weights and duals. Mathlib records are copied from actual msearch.py runs, not reconstructed searches.

## What remains unfinished

The four new prerequisites remain unsplit stage-1 items, as required for a one-level split. There are no Lean edits, compiles, or builds. The complete natural-language proof of the assigned item is in its five steps; the dry run and push results are recorded below when the delivery tool completes.
