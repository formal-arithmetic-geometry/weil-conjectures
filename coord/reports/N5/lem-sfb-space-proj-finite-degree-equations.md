# Stage-1 delivery: lem-sfb-space-proj-finite-degree-equations

Group N5, 2026-10-24. The item statement is unchanged. This is a new split, not a returned delivery. Only stage 1 was performed: no Lean file was written and no compiler, Lake command, or local DAG/preflight checker was run. All writes are in this item's sandbox.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proj-finite-degree-equations.json`: item, now split; five explicit proof steps following Stacks 085M.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proj-homogeneous-ideal-recovery.json`: new statement-only node, Stacks 085L; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-proj-ideal-single-degree.json`: new statement-only node, the affine argument of Stacks 0802 with a prescribed input ideal; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-qcoh-finite-type-union.json`: new statement-only node, Stacks 0829; no Mathlib match.
- `citations.json`: exact statement quotations for all 13 proof-step citations.
- `searches.jsonl`: actual search-command log, retained verbatim. `write_split.py` is the sandbox-only construction script; it is not part of the DAG delivery.

Three new nodes, zero Mathlib leaves. The new nodes carry statements only, empty proof/dependency lists for their proofs, `status: unsplit`, full sources and blueprint provenance. All notions in them are either defined inline or named through statement dependencies. The inherited item fields were retained, including its earlier searches.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and for relative Proj, finite-degree equations, closed Proj, and homogeneous equations. The relative-Proj functoriality declaration is about quotient maps; the finite-degree blowup declaration concerns a finite-type Rees algebra on a scheme. Neither states this item over algebraic spaces and arbitrary graded algebras. The same comparison was made before creating the new nodes. No sorry declaration was treated as an established proof.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Corrections and provenance

The source for the item is `spaces-divisors.tex`, Tag 085M, label `lemma-closed-subscheme-proj-finite`, read in full with its neighboring 085L and 085N. Its phrase “closed subscheme” means the closed subspace of relative Proj in this algebraic-space setting; the item already explains that and was not changed.

The last paragraph of the 085M proof cites `lemma-surjective-generated-degree-1-map-relative-proj` for the quotient closed immersion, although generation in degree one is not assumed. That cited lemma has an extra degree-one-generation hypothesis. The general surjection lemma 085H, `lemma-surjective-graded-rings-map-relative-proj`, supplies exactly the needed closed immersion, with no such hypothesis. The split cites the existing node for 085H. This is a correction of a source reference, not a change of the theorem or its route.

I read the current blueprint through `literature/blueprint/latest/`, especially `sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), and the unit/chapter records. The item is a supporting finite-equations input to the inherited Chow-modification/compactification prerequisite. The command `blueprint_refs.py ancestor lem-sfb-space-proj-finite-degree-equations` returns `None`, matching the original item's `blueprint.from.node: null`. I retained its detailed original `from.place` and `via`; new nodes prepend the item to that same chain and specify the exact sentence of 085M they support. I did not invent an ancestor or edit a predecessor outside this delivery. No unit realization record is due: this item is not its unit's key statement.

The generic atlas-refinement and base-change-of-etale-cover results are declared in `split_report.tool_uses`; they do not replace any unit argument. All other cited statement nodes are in the item's own unit.

## Searches read

For the item and separately for each new node I ran LeanFinder, Loogle, grep and LeanSearch through the prescribed msearch command, and a second natural-language phrasing. All services returned successfully. Each recorded query is copied exactly from `searches.jsonl`, with the returned hits, digest, directory and verdict. No unavailable result was treated as absence.

I opened Mathlib's `ProjectiveSpectrum/Topology.lean` at the vanishing-ideal definition (87–108) and the closed-set criterion (305–309), and `ProjectiveSpectrum/Functor.lean` at `Proj.map` (148–164). These give point-set radical ideals and ordinary Proj maps, not scheme-theoretic recovery of a possibly nonreduced closed subspace or a finite set of same-degree equations. I also read `RingTheory/GradedAlgebra/Homogeneous/Ideal.lean` at `homogeneous_span` (157) and `Ideal.IsHomogeneous.iff_exists` (212): arbitrary homogeneous generation is weaker than the required finite same-degree presentation. For the union node I read the local presentation and finite-presentation material in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` and the affine tilde construction in `AlgebraicGeometry/Modules/Tilde.lean`. Existence of filtered colimits of sheaves is not exhaustion by finite-type quasi-coherent subobjects on a qcqs space.

Whole-DAG keyword/tag searches and whole-blueprint searches were made before node creation, including 085L, 0802, 0829, 085M, “homogeneous ideal”, “finite type submodule”, “finite type quasi-coherent”, “single degree” and closed relative Proj. The closest statements are compared below. No blueprint node states any of the new lemmas in the necessary generality.

## Not duplicates

lem-sfb-space-proj-homogeneous-ideal-recovery vs lem-sfb-projective-closed-subscheme-homogeneous-ideal: the existing statement treats only a polynomial ring in finitely many degree-one variables and its projective space over a ring; the new one treats arbitrary quasi-coherent graded algebras over algebraic spaces, without degree-one generation or a finite generating set.

lem-sfb-space-proj-homogeneous-ideal-recovery vs lem-sfb-space-relative-proj-quotient-closed-immersion: the existing node starts with a graded surjection and constructs its closed immersion; it does not assert that an arbitrary closed subspace comes from any homogeneous ideal.

lem-sfb-space-proj-homogeneous-ideal-recovery vs lem-sfb-space-proj-finite-degree-equations: recovery asserts an unrestricted quasi-coherent homogeneous ideal without finite equations, without qcqs on the base and without finite presentation of the closed immersion. It is a genuinely weaker prerequisite, not this item's finite-generation conclusion.

lem-sfb-affine-proj-ideal-single-degree vs lemma-nagata-proj-closed-center-finite-degree-exists: the existing statement is specific to the Rees algebra of a finite-type ideal on a scheme, including a support conclusion. The new algebraic lemma allows any graded R-algebra and any prescribed homogeneous ideal I; it requires finite presentation of its Proj quotient and produces numerators inside that I. No Rees presentation is available for the graded algebra in this item.

lem-sfb-affine-proj-ideal-single-degree vs lem-sfb-space-proj-finite-degree-equations: the new node only handles an affine base and an already supplied ideal, with finite R-module generators in its chosen component. The item additionally constructs the ideal for an arbitrary closed subspace and performs the global enlargement/descent on a qcqs algebraic space. The item's Steps 1, 3, 4 and 5 retain those arguments; its proof does not become “apply the new node”.

lem-sfb-space-qcoh-finite-type-union vs lem-sfb-space-coherent-filtered-union: the existing node assumes X Noetherian and gives coherent submodules; the new node works on an arbitrary qcqs space with finite-type quasi-coherent submodules. The Noetherian hypothesis is unavailable here.

lem-sfb-space-qcoh-finite-type-union vs lemma-nagata-ideal-directed-union-finite-type: the existing blueprint statement concerns ideal sheaves inside the structure sheaf of a scheme, with an extra open-support clause. The new node concerns arbitrary quasi-coherent modules on algebraic spaces; the component I_d is not an ideal of O_X.

lem-sfb-space-qcoh-finite-type-union vs lem-sfb-space-qcoh-affine-chart-calculus: the existing node computes a given small filtered colimit on affine charts; it does not assert that a sheaf is the colimit of its finite-type submodules.

## Review by N5

I checked B–E of delivery-errors against the actual statements and sources. The item is exactly 085M, with no added Noetherian, degree-one-generation, or finite-type-component assumption. The three new statements are self-contained, and the arguments below explain why each is true rather than shifting the whole theorem into a renamed clause.

For homogeneous-ideal recovery I read 085L's entire statement and proof and its scheme analogue in `divisors.tex`, label `lemma-closed-subscheme-proj`. The source constructs the graded kernel, proves its components quasi-coherent using quasi-compact separated Proj pushforward, and identifies its quotient Proj on scheme charts. The new node takes only the existential consequence needed here, with no unsupported canonical-map or arbitrary-base-change assertion. It does not choose data from a nonunique unproved existence statement inside a definition. The quotient, algebra and quasi-coherence notions all cite their existing definitions/constructions.

For the affine single-degree lemma I read 0802's entire proof in `divisors.tex`. It works with the prescribed ideal I: finitely many standard opens D_+(f_a) cover the quasi-compact Proj. Finite presentation of the quotient immersion gives a finite-type ideal on each chart. The degree-zero localized ideal is generated by the fractions h/f_a^e with h in I of degree e deg(f_a); choose finitely many such fractions generating each chart ideal. Multiplying numerator and denominator by f_a makes e positive if necessary. Choose one positive D divisible by all deg(f_a) and at least every e deg(f_a). Replacing each chosen numerator h by h f_a^(D/deg(f_a)-e) puts it in I_D without changing its localized fraction. The R-span of these finitely many numerators is finite, lies in I_D, and generates the same ideal on every chart; conversely containment in I prevents adding equations not satisfied by the original quotient. This works even if R differs from A_0. This is not an elementary new node: it packages the finite-chart, localized-ideal and common-degree argument, whereas the global finite-type enlargement is still carried out in the item.

For the union node I read `spaces-limits.tex`, 0829, both the statement and proof. Finite-type submodules form a directed system by taking images of finite sums, and images of the finitely presented modules in a filtered presentation exhaust M. The indexing is a set of subobjects in a specified universe, not the category of all quasi-coherent modules. The new node states exactly this result and does not assume finite type of M. I compared the existing Noetherian coherent-union statement and the scheme-ideal union statement in full; neither applies to I_d in this problem.

Step 1 uses the new recovery statement for precisely the existence of I and its quotient identification. I opened the atlas-refinement statement: its quasi-compactness is explicitly the atlas convention in the item, and its last sentence gives a single affine surjective etale chart. Thus there is no silent change from atlas quasi-compactness to an unproved topology convention.

Step 2 uses the chart-calculus statement for kernels, quotients and affine module descriptions, the scheme-tests statement for the actual relative-Proj comparison, the quasi-compact-affine-tests statement for quasi-compactness on U, and the flat/proper/fp-locality statement only for preservation of finite presentation under base change. Each was read in full. Their hypotheses are satisfied by the original pi and i, and the new affine node receives the already supplied ideal I(U), not an ideal obtained by set-theoretic vanishing. The algebra A is an R-algebra; no identification R=A_0 is needed.

Step 3 uses exactly the directed-colimit conclusion of 0829 and the affine-chart computation of small filtered colimits. Each of finitely many generators has a representative in some stage, and directedness gives one stage containing all of them. This is the elementary finite-list argument written out in the step, not an invented descent theorem for F'. No descent datum for F' is assumed: F is allowed to be larger after restriction. F is contained in I_d globally, ensuring that enlargement cannot impose spurious equations on Z.

Step 4 uses the chart-calculus generated-ideal clause and the quotient-closed-immersion node, including its composition compatibility, both read in full. The two ideal containments give opposite closed-subscheme containments on U, not just containments of point sets. The middle quotient is quasi-coherent and every quotient homomorphism is degreewise surjective. The use of 085H avoids the erroneous degree-one citation discussed above. No equality of arbitrary twist tensor products is asserted.

Step 5 uses the fibre-product/etale-cover statement for the covering P_U -> P and the ideal/closed-subspace correspondence for restriction of ideals along an etale map and its injectivity. Equality of subsheaves is local by the sheaf axiom. Thus scheme structures and nilpotents are preserved in descending equality. Every non-elementary fact in these steps is a cited statement, and citations.json contains verbatim excerpts of those statements. proof_deps is exactly the union of uses. No step is longer than 2000 characters (the longest is 749), and none hides an additional comparison lemma.

I tested empty X, empty P and the zero ring: the empty cover/list is allowed and any d>0 with F=0 works when P is empty. For Z=P one can take I=0 and F=0. For Z empty in a nonempty Proj, the affine node extracts equations from the irrelevant ideal on a finite standard cover; it does not claim the ring ideal is the unit ideal. Weighted gradings such as R[x,y] with degrees 2 and 3 use a common multiple, never an arbitrary sufficiently large degree. For nilpotents, the double point V(y^2) in P^1 is retained scheme-theoretically: the quotient ideal and localization are never radicalized. Infinite-dimensional graded components and non-Noetherian base rings are permitted: finiteness is used only for the chart cover and the ideal of the finitely presented immersion. A finite-type submodule need not be coherent, which is why the Noetherian union node was not used.

## Unfinished work

None for this one-level stage-1 split. The three new nodes are deliberately left unsplit for their own items. The required remote dry run and direct push follow this report.
