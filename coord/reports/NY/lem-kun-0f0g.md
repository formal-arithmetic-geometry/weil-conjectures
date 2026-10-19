# Worker report: lem-kun-0f0g

## Files written

- dag/nodes/sec-smooth-purity/lem-kun-0f0g.json: statement unchanged; five-step split following Stacks 0F0G.
- dag/nodes/sec-smooth-purity/lem-kun-proper-base-change-torsion-ring.json: statement-only input; no Mathlib match. General torsion-ring coefficients, not restricted to Z/n.
- citations.json: verbatim statement quotations for all step citations.

## Attachments

No finished attachment for the item. Searched the blueprint tag and projection formula wording in WeilConjectures/. LowerStarProjection.lean constructs the canonical map but does not prove invertibility. ProjectionFormula.lean:263-266 states isIso_rightDerivedLowerStarProjectionMap_of_finite with sorry and assumes Finite Λ. Finiteness/Kunneth.lean:92-104 states an abstract Nonempty isomorphism with sorry and imposes finite-type base-field hypotheses; neither states the canonical general torsion-ring result as a finished proof.

The new node records AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring, WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/Proper.lean:154-157, which has sorry. This declaration occurs as an unattached open entry in thm-sf-comp-composition. It belongs to lem-kun-proper-base-change-torsion-ring, whose statement specifies the components of precisely that natural transformation. It is not a finished attachment.

## Wanted

None. Sources used are present in literature/stacks-project/.

## Corrections and source comparison

The imported statement agrees with Stacks 0F0G and is retained. Its imported proof is not valid: a torsion ring need not be Z/n (for example F_2[t]); constant free sheaves need not generate arbitrary etale sheaves by the claimed finite sums and shifts; flat is not the same as globally free; and arbitrary proper morphisms need not be morphisms between finite-type schemes over one field. These are node-level proof errors, not errors in the unit's theorem or Stacks source. The unit has no prescribed numbered proof steps, and already names this projection formula as its proper-morphism clause. The replacement follows the exact geometric-fiber route of 0F0G. No chapter or unit statement is changed.

The existing lem-kun-0f0c statement is only over Z/n; citing it directly for arbitrary Λ would be C4. Instead the new input exposes the coefficient-general base-change fact, explicitly implicit in the reduction in 0F0G and explicitly stated (but sorried) in the reference Lean. The proof of Stacks 0F0C, read at lemma-proper-base-change-mod-n, extends to torsion Λ: every Λ-module is killed by n annihilating 1, the locally bounded proper fiber dimensions bound cohomological dimension, and the termwise acyclic K-injective argument is unchanged. This explanation is in the report, not a proof hidden in the new statement. Future splitting must expose that argument and its inputs.

## Searches and reuse

Read all returned signatures from the msearch commands, which are preserved exactly in searches.jsonl and mathlib_searches. LeanFinder's projection query returned affine-transition-limit and derived projective-resolution facts; the base-change phrasings returned pushforward composition and pullback-free comparison maps, not proper etale cohomology. Loogle's projection search returned Lean projection metadata; its baseChange/IsIso search returned Guitart-exact Kan extension comparisons, without the required proper etale hypotheses. Source grep for projectionFormula|projection_formula in AlgebraicGeometry had no hit; the second grep in CategoryTheory returned an unrelated ColimCoyoneda comment. The base-change grep returned ordinary morphism stability under base change, not derived etale base change. LeanSearch returned Internal Server Error for both actual queries and is recorded unavailable. There is no Mathlib leaf.

Before creating the node, searched the whole DAG and whole blueprint for proper base change, base change with, torsion coefficients, the Stacks 0F0C tag, pull-out-constant-mod-n, and the full Lean declaration name. Read lem-kun-0f0c, lem-kun-0f12, lem-kun-0f10, and lem-kun-proj-formula-natural. No existing node states unbounded proper base change for every torsion ring. The four nt-target declarations concern other sites or smooth base change and do not provide this statement.

## Not duplicates

lem-kun-proper-base-change-torsion-ring vs lem-kun-0f0c: the existing node restricts the coefficient ring to Z/n; the new node allows arbitrary commutative torsion rings, including F_2[t], and records the existing sorried general-coefficient declaration.
lem-kun-proper-base-change-torsion-ring vs thm-weil-pbc-bounded-below: the latter covers bounded-below abelian complexes; the new statement covers unbounded module complexes over a torsion ring.
lem-kun-proper-base-change-torsion-ring vs lem-kun-0f0g: base change is an exchange map for one complex on an arbitrary Cartesian square, whereas the item is the tensor projection map for two complexes. Neither is a clause of the other. The fiber reduction and constant-complex calculation remain in the item's steps.

## Unfinished

Nothing required for this one-level split. The new input is deliberately unsplit, with empty proof and proof_deps.

## Review by NY

I read Stacks etale-cohomology.tex at lemma-projection-formula-proper-mod-n (0F0G), the immediately preceding lemma-pull-out-constant-mod-n (0F12), and lemma-proper-base-change-mod-n (0F0C), including its finite-dimension/K-injective proof. I compared the generalization with Proper.lean:143-157, where the ring is commutative and additively torsion and the exchange is unbounded. Torsion for a unital ring supplies a single n annihilating 1 and hence every module; no finiteness or flatness of the ring is imposed. The source distinction between Z/n and general Λ is explicit in the new node and the nonduplicate explanation.

For step 1 I opened lem-weil-pbc-proper-base-change, whose statement gives stability of properness for arbitrary base change, and the scheme conventions, which define proper as separated and finite type. I opened lem-kun-0f10 and used only clause (2), now with the genuine finite-type scheme X_s over the algebraically closed field Ω. This fixes the original global misuse. Quasi-compactness follows from finite type and quasi-separatedness from separatedness.

For step 2 I opened lem-kun-stalk-as-pullback: it covers sheaves and derived objects. I read the statement of lem-exc-abelian-sheaves-gmodules and its source 04JQ, lemma-equivalence-abelian-sheaves-point. With K=Ω its group is trivial. The scalar-action extension is formal: for every λ the fully faithful equivalence carries multiplication by λ to an endomorphism, and faithfulness preserves and reflects all ring-action equalities. The same inverse carries differentials and their commutation with scalars, giving the asserted identification of complexes. This step does not use the much narrower finite-field/constructible point-fiber node.

For step 3 I checked that the new base-change input permits any unbounded E, including the tensor complex in the right side. I opened lem-kun-inverse-image-monoidal, whose statement is for arbitrary commutative coefficients and unbounded K,L. I opened lem-kun-proj-formula-natural and used its displayed commuting square exactly: its left vertical is exchange on E tensor the identity and its right vertical is exchange on E tensor f inverse K. This establishes that it is the canonical projection morphism that is tested.

For step 4 I opened lem-kun-0f12: it needs qcqs, finite cd, torsion Λ, and allows arbitrary unbounded E and a complex of modules M. All four conditions were established before invoking it. I checked def-kun-projection-formula-map's adjoint/counit construction to identify that canonical map with the one after the naturality square; no abstract Nonempty isomorphism is substituted.

For step 5 I opened prop-weil-pbc-geometric-stalks-exact and lemma-weil-pbc-geometric-stalk-conservative. They state exactness and conservativity for abelian sheaves, not unbounded derived categories. The step supplies the remaining argument explicitly: exactness commutes with each cohomology, the conservative statement is applied to each cohomology sheaf after forgetting coefficients, and an acyclic cone is zero in the derived category. Thus the bounded-below derived conservativity node is not misused for unbounded objects. The off-unit citations are declared as generic tool uses, not alternative proof routes.

I checked B1–B10: the one new node introduces every object, gives the exchange definition dependency, has no proof sketch or proof dependencies, gives exact source labels and blueprint ancestry, and records only searches actually run. C1–C8: every non-elementary input is cited, every cited statement was opened, the new input is distinct from projection formula, and the generic tools are declared. D1–D5: no clause is moved to a new node; the five steps carry the geometric-fiber argument. E1–E7: there is no invertibility-of-n or base-field assumption globally, no boundedness assumption on complexes, and no substitution of a narrower coefficient category.

Small cases: f=id reduces all exchange and projection maps to unit constraints; an empty fiber gives zero on both sides; Λ=0 is vacuous; Λ=F_2[t] shows why the original Lambda=Z/n substitution fails while both the new input and 0F12 remain applicable; unbounded complexes are covered without invoking bounded-below conservativity. No statement dispute is needed because the source theorem is correct. The errors corrected were in the imported argument only.

## Second reading by NY

- Item statement: checked every hypothesis and both sides against etale-cohomology.tex, Tag 0F0G / lemma-projection-formula-proper-mod-n; agrees, including arbitrary torsion ring and unbounded E,K.
- Step 1: opened lem-weil-pbc-proper-base-change, scheme conventions and clause (2) of lem-kun-0f10; proper fiber is finite type over the algebraically closed field, so the finite-cd input applies. Expanded qcqs justification from the diagonal definition; passes.
- Step 2: opened lem-kun-stalk-as-pullback and lem-exc-abelian-sheaves-gmodules, and read 04JQ / lemma-equivalence-abelian-sheaves-point; trivial Galois group gives groups, scalar endomorphisms give modules. Expanded exactness and passage through quasi-isomorphisms; passes.
- Step 3: opened the new exchange statement, lem-kun-inverse-image-monoidal and the displayed square in lem-kun-proj-formula-natural; both exchange applications admit these unbounded complexes and the square identifies the canonical map, not only its objects; passes.
- Step 4: opened lem-kun-0f12 and def-kun-projection-formula-map, and read 0F12 / lemma-pull-out-constant-mod-n; all qcqs, finite-cd and coefficient hypotheses hold on the fiber and the adjoint map is precisely the constant-complex map; passes.
- Step 5: opened prop-weil-pbc-geometric-stalks-exact and lemma-weil-pbc-geometric-stalk-conservative; their abelian statements suffice after cohomology and forgetting scalars. The cone argument is elementary and applies in every degree without boundedness; passes.
- New node lem-kun-proper-base-change-torsion-ring: read 0F0C / lemma-proper-base-change-mod-n and 0F0G proof, and Proper.lean:154-157 in read-only slopmaster2. General torsion coefficients are implicit in 0F0G, not literally the 0F0C statement; the Lean declaration states this version but is sorry, not a proof. It is an independent exchange theorem, not a projection-formula clause or elementary fact; retain unsplit. Added the explicit derived-category meaning and its definition dependency; statement-only B1-B7 passes.

Independent reuse checks: searched all blueprint chapters with blueprint_refs.py for proper base change and torsion ring, checked ancestor lem-kun-0f0g, and searched DAG statements/source tags and the reference Lean. The Z/n node lem-kun-0f0c and bounded-below thm-weil-pbc-bounded-below do not cover this statement. Own Mathlib queries use higher direct images / integer-annihilated modules, IsProper plus derived, and derivedBaseChangeMap names: LeanFinder gives sheaf-pushforward composition or open-restriction results; Loogle and grep give zero hits. No leaf. Actual outputs remain in searches.jsonl and both node search records.

Edge cases checked: zero ring (n=1), zero complexes, empty fiber, identity over an algebraically closed field, and F_2[t] coefficients. These satisfy the repaired statements; no invertibility, finite coefficient ring, global finite-type field base, or boundedness assumption is introduced. B1-B7 and C1-C4 checked directly against the opened statements; no fact is taken from a cited proof.

Changes: expanded qcqs and derived-equivalence arguments in steps 1 and 2 to make the elementary inferences explicit; supplied the new node's derived-category definition citation to satisfy B3; refreshed its verbatim citation and recorded independent searches. The first worker's correct fiber route and Review by NY section are retained. No statement dispute.
