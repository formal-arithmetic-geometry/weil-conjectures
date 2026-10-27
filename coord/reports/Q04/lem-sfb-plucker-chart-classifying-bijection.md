## Worker report

Item: lem-sfb-plucker-chart-classifying-bijection. Group Q04, 2026-10-23. Direct delivery, stage 1 only.

### 1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-plucker-chart-classifying-bijection.json`: statement, split; no Mathlib match. Nine proof steps, all using existing nodes, replace the empty proof. The statement is unchanged. The determinant-chart and quotient-gluing theorems move from statement dependencies to proof dependencies, since the statement already introduces its objects and assumes its framed quotient explicitly.
- `report.md`: this worker report and signed review.
- `citations.json`: 30 step/node entries with verbatim excerpts from the statements actually used.
- `searches.jsonl`: five actual Q04 Mathlib-search results, produced by the required search command. The five inherited search entries in the item are retained, and the Q04 results are appended.

New nodes: 0. New Mathlib leaves: 0. No Lean files, compiler calls, repository writes, launcher edits or additional agents.

### 2. Attachments

None. Searches of `lean/WeilConjectures/` by the exact blueprint tag and by Grassmann/Plucker terminology found no declaration of the item. Existing exterior-power declarations supply component results only.

### 3. WANTED

None for this split. The proof needs no source beyond the available Stacks files and existing component nodes. The parent's archival Pluecker-embedding reference is not used as an unsupported black box.

### 4. What needed correction or completion

The live item was statement-only, without a proof or a released repair note. I preserved its statement and all maintainer-owned fields. The main gap was the actual scheme-theoretic construction and its inverse/naturality checks: pointwise vanishing of the equations would not suffice on nonreduced test schemes. Step 4 constructs morphisms into the explicit polynomial chart rings and checks their overlap coordinate maps; step 5 compares actual scheme morphisms and proves uniqueness by the same chart generators. Thus no reducedness assumption or unsupported factor-through-closed-subscheme inference is used.

The final determinant-line claim follows from the projective-space functor with its labeled sections, after proving that the determinant morphism for the universal quotient is precisely j. It does not use only an abstract isomorphism of invertible modules.

The inherited `blueprint.from.node` is null, as confirmed by `tools/blueprint_refs.py ancestor`; its precise inherited place and via chain are preserved. Searches of the entire imported blueprint for Grassmann, Plucker, quotient line, projective space and exterior power found the familiar definition/projective-space/exterior nodes, but none stating this normalized Grassmannian classification. I do not manufacture a blueprint ancestor or alter the unit/chapter record.

### 5. Unfinished work

None in this item's one-level split. The existing determinant-chart and quotient-gluing nodes remain independent prerequisites, not proof claims silently assumed to have finished Lean proofs. This delivery supplies the complete natural-language assembly from their statements.

## Mathlib searches

The exact queries, service results and verdicts are recorded in the item and `searches.jsonl`. Both LeanFinder phrasings returned module Grassmannians, point projectivization or topological vector-bundle statements; Loogle returned `Module.Grassmannian.functor`, `functor_obj` and `functor_map`; LeanSearch returned constructors and accessors for module Grassmannians. The logged AlgebraicGeometry grep found no Grassmann/Plucker/exterior-quotient chart declaration. I read `Mathlib/RingTheory/Grassmannian.lean`: lines 46-53 explicitly list charts, scheme Grassmannians and representability as TODO, while the existing functor is on commutative algebras and module quotients. None of these gives the stated scheme classification or its labeled determinant-line identification in one specialization. Every Q04 entry came from the required msearch command; no unavailable service is represented as a negative result.

## Not duplicates

No new nodes were created. Existing nodes were reused for the determinant polynomial charts, normalized quotient transitions and pivot opens, exterior basis and sheafification comparison, matrix determinant identities, projective quotient-line classification, its chart formulas, and morphism/sheaf gluing. The stronger parent Grassmannian representability theorem depends on this item and is not cited, avoiding a cycle.

## Review by Q04

I read `GOAL.md`, the stage-1 brief, the worker/stage contract, the three blueprint levels in SETUP, the item's chapter and unit records, and delivery-errors B through E (including their duplicated new-target copy). The inherited alteration-to-Hilbert-to-Grassmannian prerequisite route is retained. I read Stacks `constructions.tex`, Tag 089T (`lemma-gkn-representable`), including all four parts of its normalized-quotient-chart proof, and Tag 01NE (`lemma-projective-space`). I also read the fraction map and overlap formulas in Tag 01N8 (`lemma-converse-construction`), the increasing-wedge basis in `algebra.tex` Tag 00DM (`section-tensor-algebra`), and the map-gluing statement and proof in `sheaves.tex` Tag 04TN (`lemma-glue-maps`). The tag/label pairs were checked in the local tags table. The determinant-coordinate completion is explicitly agent-written; Stacks 089T is not misrepresented as stating the specific homogeneous equations or the Pluecker embedding.

I opened the statement of every cited node and checked the following uses individually:

1. The quotient-gluing node actually supplies an open pivot cover and its normalized frames. The local exterior comparison actually supplies a bijective sheafification unit on every subopen of a trivializing open. The exterior-basis leaf identifies the unique increasing top wedge as a basis, and the exterior-sheaf definition identifies the wedge's restriction maps. Together these prove that s_I, rather than some unspecified local section, trivializes L. No claim of local freeness is taken just from the definition of a determinant line.

2. The exterior-algebra definition gives multilinearity and alternation; I wrote the surviving permutation terms and compared them to the determinant definition's column convention. The adjugate leaf supplies both products with the matrix, and the matrix-identity leaf supplies determinant multiplicativity. These yield the inverse when the determinant is a unit and the converse when a matrix inverse is given. In particular, the nonvanishing locus of s_I is exactly the pivot locus, and the minor ratios are computed only where det(M_I) is a unit. There is no cancellation of a possible zero divisor. The ordered single-replacement formula has the sign required by the statement.

3. The projective-space functor-of-points node gives both uniqueness of a morphism and the isomorphism carrying every coordinate section to its prescribed generator. Its statement alone does not give chart inverse images, so I additionally cite the sections-to-Proj theorem whose clauses (ii) and (iii) do. Its ring base is specialized to Z and its degree is one. The generated invertible module and the nonvanishing cover have already been established; no triviality of L on all of T is assumed.

4. The determinant-chart node gives exactly the polynomial-ring chart isomorphism and the equality det(M^(I)_J)=p_J/p_I. The affine-target theorem applies to arbitrary source schemes, including the nonaffine T_I and their intersections, and its basic-open clause recognizes the overlap using the unit s_K/s_I. The quotient-gluing statement gives both the transition identity on X and the normalized frame change for q. Evaluating the former yields ((N_I)_K)^(-1)N_I=N_K, so equality on every off-pivot generator follows. I then use the actual morphism-gluing theorem. No affine-intersection assumption occurs.

5. The projective twisting-sheaf chart theorem really states that the ratios p_J/p_I generate the projective standard affine coordinate ring. This and affine-target injectivity compare j b_q with a_q as morphisms. For uniqueness of the factorization, c^(-1)(U_I)=T_I follows from j c=a_q and the already proved inverse-image formula. The x-generators are single-replacement ratios, so they determine c on each chart. Neither topological image containment nor a pointwise argument is substituted for scheme-theoretic factorization.

6. The pullback clause of the quotient-gluing statement supplies the pulled-back pivot frame and its pulled-back normalized entries, not just a definition of pullback. The given frames on q_X then produce explicit local quotient-preserving isomorphisms. Their transition matrices coincide, so the morphism-gluing clause of the sheaf-gluing node applies to these maps and their inverses. Its uniqueness clause proves the inverse equations. This is a genuine global quotient isomorphism, not a comparison of ranks or determinant lines.

7. For an arbitrary b, the opens b^(-1)(U_I) cover T and the pulled-back normalized matrix on them is b^*M^(I). They lie inside the appropriate pivot loci; equality with the entire pivot locus is unnecessary. The polynomial chart theorem and affine-target injectivity give b_(b^*q_X)=b locally, and morphism gluing makes it global. The opposite inverse is step 6. No representability theorem of the parent is used circularly.

8. A quotient-preserving isomorphism carries each standard-generator image and each ordered pivot frame to its counterpart, so normalized entries coincide. For arbitrary f the quotient-gluing statement explicitly gives both inverse-image pivot opens and pulled-back normalized entries. Comparing chart coordinate maps and then gluing proves the stated naturality identity. The module-pullback definition explicitly includes its identity and composition isomorphisms, so pullback on quotient classes really forms a functor.

9. The inverse identity for b=id_X identifies b_(q_X) with id_X. The factorization identity identifies its projective determinant morphism with j. The projective-space theorem then gives the required line isomorphism with every labeled coordinate section; no additional determinant-pullback theorem is being quoted without a node.

I checked the hypotheses across these applications: arbitrary test schemes, constant locally free rank r, 0<r<N, finite coordinate index set, genuine epimorphic quotients, open pivot covers, and inversion only of pivot determinants that are units. No noetherian, finite-type, separated, reduced or characteristic assumption is introduced. Definitions are not cited as if they asserted the auxiliary theorems. Generic results filed in other units are declared in `split_report.tool_uses`; the same-unit determinant construction remains the route.

For small cases, r=1,N=2 gives H=0 and the ordinary projective-line quotient functor. For r=2,N=3 and normalized matrix [[1,0,u],[0,1,v]], the coordinates are p_12=1, p_13=v, p_23=-u, so the single-replacement coordinate in the first row is p_32/p_12=u; this checks the ordering sign. On the K={1,3} overlap v is a unit and the normalized matrix is [[1,-u/v,0],[0,1/v,1]], agreeing with the stated inverse-column transition. Setting u=epsilon, v=1 over Z[epsilon]/(epsilon^2) checks that the construction keeps nilpotents and the equalities of scheme maps. The same alternating formulas work in characteristic two without division by two. Empty pivot loci and the empty test scheme cause no exception: the exterior comparison explicitly includes zero section rings and the gluing statements apply to the empty cover.

All nine steps are below 2000 characters. They contain explicit coordinate calculations and assembly, with no long hidden sublemma or new node that merely renames a clause. All 30 step/node pairs have an exact statement excerpt in citations.json, checked as substrings after the final edit. My substantive corrections during review were to cite the projective chart-ratio theorem separately from its functor-of-points theorem, to obtain pulled-back pivot frames from the quotient-gluing theorem rather than merely invoke the definition of pullback, and to use only containment of the pulled-back chart in the pivot locus for the inverse identity. No statement dispute was found.
