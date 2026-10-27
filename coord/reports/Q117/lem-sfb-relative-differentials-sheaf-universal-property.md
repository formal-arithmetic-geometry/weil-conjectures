# Stage-1 report: Q117

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-differentials-sheaf-universal-property.json: item, statement, split. Statement and all its hypotheses retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-derivation-global-ext.json: new statement-only node, not in Mathlib; project attachment candidate recorded.
- citations.json: one exact statement quotation for every step/node pair.
- searches.jsonl: actual msearch log; the node search records use its exact tool/query strings.

## Attachments

AlgebraicGeometry.Scheme.Modules.derivation_ext_of_isAffine belongs to lem-sfb-affine-derivation-global-ext; lean/WeilConjectures/AlgebraicGeometry/Modules/Differentials.lean:422. Read the complete proof (through line 451): it has no sorry and is more general than the new node. The maintainer must verify the transitive closure. The new node records lean_candidates rather than claiming a checked lean_audit.

This does not attach the item. AlgebraicGeometry.Scheme.Hom.relativeDifferentialsHomEquiv at that file:119 is a proved equivalence of types, using a sheafified presheaf definition and inverse-image derivations. It does not state the complete item: no additive equivalence, target naturality or restriction-commuting assertion is in its signature. relativeDifferentialsRestrictIso at line 405 identifies restricted differential objects; it likewise does not state the item’s full restriction square.

## WANTED

None. All sources used are present locally. coord/dag-sync.md mentioned in the historical isolated-project appendix is absent in this live read clone; current explicit shared-clone instructions govern the delivery.

## Corrections and scope

No mathematical statement correction was needed. The item initially had an empty proof and one grep search. I retained that search as history, added only actually logged searches, and supplied the proof from the affine-local definition. Stacks 01UR is a definitional restatement because Stacks defines the differential sheaf by universality. Our defining DAG node instead describes affine sheaves of ring differentials: citing 01UR alone would hide the comparison. The split now constructs the factorization from the affine adjunction and checks it on all opens, then glues it.

The new lemma is just the uniqueness ingredient in Stacks 01UO, not a repackaging of the item. Its source’s uniqueness proof works for an arbitrary base scheme: relative base annihilation is unused. The argument intended for later work is the source’s equation D(a)=a/g^n D(g^n)+g^n D(a/g^n) on D(g), with the restrictions understood. Invertibility of g^n forces D(a/g^n), hence agreement on global sections forces agreement on standard opens and by the sheaf axiom everywhere. The complete proved project candidate already writes this argument. The new node itself has no proof or proof dependencies.

## Not duplicates

lem-sfb-affine-derivation-global-ext vs lem-sfb-relative-differentials-sheaf-universal-property: both cite 01UO; the new node only detects equality of two existing derivations on an affine source from equality on its global ring. The item constructs a universal module-sheaf factorization on arbitrary schemes, including additivity, naturality and restriction.

lem-sfb-affine-derivation-global-ext vs lem-sfb-smooth-derivation-zero-divisor: both cite 01UO; the existing node concerns vector fields on a smooth proper connected curve over an algebraically closed field, their divisor and degree. It does not give arbitrary affine sheaf-derivation extensionality, and it depends on the item, so cannot be used here.

I searched the whole DAG by 01UO, affine-case-derivation, derivation_ext_of_isAffine, and global-section uniqueness wording. I also read the statement search results for derivation and affine/global wording, and ran blueprint_refs search for derivation and the affine/global combination. There is no matching blueprint node; same_as remains empty. blueprint_refs ancestor prints None for this item, as inherited from its current null blueprint ancestor; the new node uses exactly that ancestor and prepends the item to the inherited via list. The latest blueprint’s unit and direct-images proof were read: this is the generic rigidity prerequisite below its proper-direct-image route, not a replacement of a unit-level argument.

## Review by Q117

I read the source of the item in literature/stacks-project/morphisms.tex: Tags 01UR (lemma-universal-derivation-universal), 01UO (lemma-affine-case-derivation, including the fraction formula and its omitted existence details), 01UT (lemma-differentials-affine) and 01US (lemma-differentials-restrict-open). For the new node I used only the uniqueness paragraph of 01UO, not its omitted existence calculation. I read the full proved declaration Scheme.Modules.derivation_ext_of_isAffine: affine basic opens cover any open, global agreement gives agreement on numerators and denominators, invertibility cancels the denominator, and the sheaf axiom concludes. This is exactly the new node’s statement, with the inverse-image ring presheaf specialized to f. No field, smoothness, separatedness, finite type or quasi-coherence assumption is used.

For step 1 I opened def-sc-relative-differential-sheaf, def-weil-pbc-kahler-differentials and def-weil-sheaf-of-modules-category. Their statements give respectively affine local differential data compatible with restriction, additive derivations annihilating the base, and sectionwise linearity of module morphisms. Covering by affine neighbourhoods inside a chosen base open proves the sheaf derivation laws and base annihilation even for sections on a nonaffine base open. This is a short equality check from the definitions and the sheaf axiom.

For step 2 the same differential and ring statements give the ring universal factorization into F(U). I opened lem-weil-pbc-affine-tilde-gamma-adjunction: clause (1) explicitly states the Hom bijection for EVERY O-module F, not only a quasi-coherent target. I also read its source, Schemes 01I7, lemma-compare-constructions, and the pinned Mathlib tilde.adjunction around lines 338--374. The new extensionality statement explicitly applies to any affine source and arbitrary module sheaf, so both alpha_U d and D|_U satisfy its hypotheses. Their equality on A therefore gives equality as sheaf derivations, not merely on global sections. For uniqueness of alpha_U the affine Hom bijection is injective and ring universality identifies its global component. No source sheaf-Hom proof internals are being used.

For step 3 I opened lem-pur-sheaf-hom-cover-gluing and its source Sites Modules 03EM, lemma-internal-hom, which points to Sites 04TQ, lemma-glue-maps. Its actual statement gives existence AND uniqueness of gluing O-linear morphisms from compatible local module maps. The Zariski site has the required intersection pullbacks. On a possibly nonaffine overlap I use a cover by smaller affine T mapping into a smaller affine V in the intersection of base charts. Step 2 on each (T,V) gives agreement. This checks the affine hypothesis every time; no separatedness or affine-intersection hypothesis is invented. The gluing node is declared as a generic off-unit tool in split_report.tool_uses.

For step 4 the category-of-module-sheaves definition explicitly supplies additive sheaves and linear components. The addition, zero and composition equalities are sectionwise identities, so a bijective additive map is the claimed abelian-group isomorphism and composition associativity proves target naturality. Inverse naturality follows from the already proved uniqueness, with no additional representability or Yoneda lemma invoked.

For step 5 I use the precise affine description WITH compatible universal derivations from def-sc-relative-differential-sheaf, not a definition of mere unidentified objects. On W both affine-local differential pairs are identical; step 2 proves uniqueness of their d-preserving local identifications on the overlaps. The gluing statement therefore glues the maps and their inverses. The displayed equality (alpha|_W c^{-1}) d_{W/S}=(alpha d)|_W proves the actual restriction square. Stacks 01US gives the same identification, but is not used as an uncited black box. The needed proof ingredients are already cited nodes and the preceding affine calculation.

I checked B1--B10, C1--C8, D1--D5 and E1--E7 against the written files. New node: self-contained, one-backslash TeX after JSON decoding, explicit base-annihilation condition, statement-only, no hidden existence assertion, no repetition of the item. Sources have verified tags and labels. All 16 citations quote verbatim portions of the cited statement (in fact the full statements), and no proof is used in place of a statement. The five proof steps are each below 2000 characters. Small cases: X empty (all equalities unique), zero target, identity X→X (all relative derivations vanish), and Spec k[t]→Spec k with arbitrary target sheaf. Nonreduced A and characteristic p cause no problem because the only cancellation is by units on D(g), never by n or a nilpotent. The proof never assumes F(U)_g equals F(D(g)). I also checked that none of the cited nodes depends on the item: the new node has only definition dependencies, the ring/tilde nodes are Mathlib leaves, and the gluing tool has independent sheaf-theoretic prerequisites.

## Unfinished work

None in this one-level split. The new statement is deliberately unsplit and supplies a proved project candidate for independent attachment verification. No Lean was written or compiled and no repository or launcher file was changed.
