# Stage-1 report: lem-sfb-sheaf-modobj-grothendieck-any-ring

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-modobj-grothendieck-any-ring.json: split, five steps; all original conclusion clauses and hypotheses retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-sheaves-grothendieck-with-sheafification.json: new statement, Mathlib leaf, general Grothendieck coefficient category with a left exact reflector, plus its abelian-group specialization.
- dag/nodes/sec-six-functors-basics/lem-sfb-free-internal-module-adjunction.json: new statement-only helper; no Mathlib match, project adjunction candidate recorded.
- citations.json: verbatim statement excerpts for every citation of every proof step.

## Attachments

CategoryTheory.Mod.freeModObj, CategoryTheory.Mod.free, CategoryTheory.Mod.freeForgetAdjunction belong to lem-sfb-free-internal-module-adjunction, lean/WeilConjectures/CategoryTheory/Monoidal/Mod/Abelian.lean:44-111. These are supporting declarations for the new helper; independent transitive axiom checking remains the maintainer's job. I do not propose an ATTACH disposition for the item.

## Wanted

None. All sources used are present locally.

## Corrections and source comparison

The item's former source path refers to the October 15 blueprint layout. I read the current blueprint through literature/blueprint/latest, now main-20261025, especially sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/lem-sfb-modobj-grothendieck.md and its .proof.md. The current statement explicitly allows an arbitrary monoid object, whereas the live DAG's lem-sfb-modobj-grothendieck.statement still assumes commutativity. Its blueprint_update contains the newer general statement. C4 forbids taking this broader fact from the old statement, so the split proves the module Grothendieck assertion through its component results instead of citing that node. The item's statement itself is unchanged. No STATEMENT-DISPUTED is needed.

I also read the current sk-lem-formal-closed-support proof, especially its adjunction paragraph: Grothendieckness is a categorical input for K-injective resolutions, not a change of the support argument. No SGA source is used. The three existing internal-module tools are declared as generic tool uses; their off-unit use supplies this categorical input.

## Searches and nonduplicates

I searched the project declaration tree by the exact blueprint tag and by the module-category declarations. I read Mod/Abelian.lean, including all binders of the Grothendieck and free adjunction sections, and Mod/Limits.lean. The earlier combined attachment refusal is respected: an ordinary Mathlib sheaf instance is not represented as a project declaration.

Before writing either helper I searched the full DAG's statements, sources and Mathlib matches for Grothendieck sheaves, HasExactColimitsOfShape.domain_of_functor, freeForgetAdjunction, free internal modules, and free module adjunctions. The whole-blueprint searches included Grothendieck, modobj, free module, free internal, sheafification and sheaves.*Grothendieck. The lone blueprint hit for free internal was thm-weil-six-operations, a seven-clause global functor package, not an internal free-module adjunction.

Every Mathlib query in the new records was run through batch2/msearch.py. searches.jsonl retains the actual hit counts and names. I read the returned statements. Monad.adj requires a monad algebra category; it does not by itself identify internal modules with those algebras. ModuleCat.adj and PresheafOfModules.freeAdjunction concern different free functors. Two semantic phrasings and separate Mod and Mod_ source searches found no Mathlib internal adjunction. The general sheaf theorem is a direct match; the local source, rather than remote search-service binder snippets, determines its hypotheses.

## Not duplicates

lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact: the latter (same 03CO source) states colimit existence and filtered exactness for Ab, not a generator or Grothendieckness for general coefficients.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-abelian-etale-sheaves-grothendieck: the latter is restricted to small etale sites of schemes and abelian groups; the new leaf is conditional for arbitrary small sites and Grothendieck coefficients.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-cbc-sieve-module-sheaves-grothendieck: the latter has constant ordinary ModuleCat coefficients. It does not state the general coefficient theorem; its Z case does not identify arbitrary abelian-category coefficients.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-sfb-proetale-sheaves-grothendieck: the latter is restricted to scheme pro-etale sites and asserts sheafification-free general-coefficient existence; the new general-site leaf explicitly requires a left exact reflector.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-sfb-grothendieck-sheafification: the latter constructs the reflector and proves abelianness; it does not assert the generator and exact filtered colimits of the sheaf category.
lem-sfb-free-internal-module-adjunction vs lem-sfb-modobj-grothendieck: same blueprint proof source, different assertions. The helper only constructs F_R and states its adjunction in any monoidal category. It does not assert abelianness, colimits, a generator or Grothendieckness, and does not require commutativity.
lem-sfb-free-internal-module-adjunction vs lem-weil-pbc-module-object-free-generators: the latter concerns the composite free-on-an-underlying-set construction and finite locally constant charts on scheme pro-etale sites. It does not state the free internal-module adjunction on an arbitrary object of an arbitrary monoidal category.
lem-sfb-free-internal-module-adjunction vs def-sfb-condensed-free-module-adjunction: the latter starts with condensed sets and commutative condensed rings; the helper starts with arbitrary objects in arbitrary monoidal categories and arbitrary monoids.

lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-ringed-site-module-sheafification-exact: the latter proves exactness of module sheafification, not Grothendieckness or a generator for sheaves with general Grothendieck coefficients.
lem-sfb-sheaves-grothendieck-with-sheafification vs aux-site-filtered-colimit-sections-inverse: the latter computes sectionwise filtered colimits under finite-cover hypotheses; it asserts neither a generator nor a general sheaf Grothendieck theorem.
lem-sfb-sheaves-grothendieck-with-sheafification vs def-weil-pbc-colimit-site-abelian-stage-image: the latter defines a subgroup-generated stage-image subpresheaf in a diagram of sites; it makes no Grothendieck assertion.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-pbc-u2-module-sheaf-underlying-colimit: the latter concerns a forgetful functor on constant module sheaves of an etale scheme site preserving one colimit cocone; it does not supply Grothendieckness of general sheaf categories.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-pbc-u2-module-sheaf-underlying-preserves-colimit: the latter preserves colimits under forgetting constant etale module coefficients; it is not a theorem about generators or Grothendieckness for arbitrary coefficient categories.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-of-sites-sections: the latter is a sections continuity comparison on a filtered colimit of sites with finite covers; it does not assert Grothendieckness on an arbitrary fixed site.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-site-abelian-cover-section-lift: the latter lifts a family of sections on a cover to some stage and asserts no compatibility or amalgamation; it is not a Grothendieck theorem.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-site-abelian-finite-family-stabilization: the latter makes an already image-compatible family compatible after stage refinement; it does not concern generators or exact colimits of a general coefficient sheaf category.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-site-abelian-finite-indexed-matching: the latter stabilizes indexed matching families in a filtered diagram of sites; it is not the fixed-site Grothendieck assertion.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-site-abelian-finite-object-section-lift: the latter simultaneously lifts finitely many stage-image sections; it proves no abelianness, generators or filtered exactness for general coefficient sheaves.
lem-sfb-sheaves-grothendieck-with-sheafification vs lem-weil-pbc-colimit-site-abelian-inverse-image: the latter constructs a sectionwise inverse-image colimit comparison in a diagram of finite-cover sites; it is not a Grothendieck category theorem.

## Review by NG

For the item I read all three paragraphs of the current blueprint's module Grothendieck proof and the parent support adjunction paragraph. I retained its route: abelianness, created colimits, filtered exactness, free generator. I did not use the commutative internal-to-section-module equivalence for noncommutative rings.

Step 1 cites the size convention, the new general sheaf leaf, and the existing sheaf-tensor statement. The size convention permits working on a small representative; the leaf explicitly provides the Ab specialization without extra topology assumptions. The tensor node explicitly states closedness and colimit preservation, not just a formula for a tensor. I supplied the elementary biproduct argument for additivity, so no flatness or tensor exactness is silently assumed. For the new leaf I read Mathlib CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.lean:72-84, Sites/Abelian.lean:40-42, the HasSheafify constructor in Sites/Sheafification.lean, the concrete instance Sites/LeftExact.lean:308-311, and Algebra/Category/Grp/AB.lean:109. The conditional general statement exactly fits the small-site instance; its Ab clause uses existing concrete sheafification. Stacks 03CO (sites-modules.tex, lemma-limits-colimits-abelian-sheaves) supplies the abelian-valued colimit and exactness source, not the more general coefficient theorem; that theorem's precise source is the Mathlib declaration named in the node.

Step 2 uses lem-sfb-modobj-abelian. I opened its statement and checked that it requires a monoid, not a commutative monoid, and requires only additivity and finite-colimit preservation of R tensor. Both were established in step 1. Step 3 uses lem-sfb-modobj-forget-faithful and both clauses of lem-sfb-modobj-forget-creates. I opened both nodes: the second really gives a limit action and a colimit action with the associated universal properties, and assumes only a small index and preservation by the fixed tensor for the colimit clause. The base Grothendieck category has the underlying colimits and finite limits. This supplies the precise finite and filtered preservation assertions, not merely existence of objectwise operations.

For step 4 I opened lem-weil-pbc-jointly-reflect-short-exact and verified all its hypotheses: both categories are abelian; U preserves finite limits, finite colimits and zero maps; the family is a singleton; inverse linearity is written out so U reflects isomorphisms. Its statement gives exactly the short-exactness criterion used. The base filtered-colimit exactness is a clause of the cited Grothendieck definition. This removes the unproved implication 'faithful exact, therefore reflects exactness' from the blueprint's prose and replaces it by an explicit applicable theorem. No assertion of sectionwise filtered colimits on an arbitrary site is used.

For step 5 and the new free helper I read the last blueprint paragraph and the general freeModObj/free/freeForgetAdjunction constructions in Mod/Abelian.lean:44-111. The module action uses alpha inverse in the stated orientation, and the two displayed Hom maps have the correct domains. The unit and associativity laws, not symmetry, prove the inverse formulas. Its statement is strictly below the item: it has no abelian or Grothendieck hypotheses or conclusions. The item itself carries the generator argument using faithfulness and naturality; the helper does not restate the Grothendieck clause. The final Grothendieck definition is cited for all three remaining axioms.

I tested the small cases of every new statement and the specialization: the empty site, a site with the maximal topology, the zero coefficient category, the zero ring object, the tensor unit ring, and on a one-object point site a noncommutative matrix ring. The free adjunction gives zero on the zero ring, all modules there are zero by the unit law, and a generator of the zero category is allowed. No nonzero-object assumption or commutative multiplication was introduced. The new sheaf theorem allows any Grothendieck topology and does not require pullbacks in the underlying category. The free adjunction requires no (co)limits and works for non-braided monoidal categories as well. No new node merely duplicates a clause of this item; the sheaf result is a general Mathlib leaf and the free adjunction is the substantive construction used in the generator proof.

I checked delivery-errors B through E against the actual JSON and sources: both helpers are statement-only, all objects and hypotheses are introduced, TeX uses single backslashes, and every cited non-elementary input has a node with a verbatim quote. No proof step exceeds 2000 characters. No repository or launcher file was changed, and no compiler or Lake was run.

## Unfinished

No mathematical part of this stage-1 split is left unfinished. The new adjunction helper is intentionally statement-only, with the project declaration recorded for independent review; that is the required one-level split.
