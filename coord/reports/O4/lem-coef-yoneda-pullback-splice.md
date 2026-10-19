## Files written

- `dag/nodes/sec-six-functors/lem-coef-yoneda-pullback-splice.json`: statement item, now split into seven steps; no Mathlib match for the whole item.
- `citations.json`: verbatim statement quotations for every dependency of every step.
- No new nodes and no new Mathlib leaves. The initial candidate pullback-epi leaf was unnecessary: the existing, more general refinement criterion proves it in three lines.

## Attachments

None. Searched all `WeilConjectures/` of the supplied slopmaster2 checkout for the item tag, Yoneda extensions, and splicing, and inspected the relevant homological source directories. No declaration proves this exact comparison. Derived Ext operations alone do not state this exact-sequence construction.

## WANTED

None. Read the local Stacks sources. No SGA source is used.

## Corrections and scope

The statement is unchanged. Added the existing exact-sequence definition to statement dependencies. The item had no proof and no Lean audit entry. Its five inherited Mathlib-search records are retained verbatim, and new searches actually run in this session are appended. LeanSearch returned HTTP rate limiting and is recorded unavailable. Read the hits: Ext composition/associativity and exact Ext sequences are statements about derived Ext; ComposableArrows truncation exactness gives neither this pullback construction nor the required comparison. Read `Ext/Basic.lean:128-174` and `Ext/ExtClass.lean:126-138` to check that distinction.

The current chapter/unit records were read, including the three-level route policy. This is an inherited foundational lemma below the historical second paragraph of `prop-coef-integral-exceptional-adjoint` through `lem-coef-module-flat-cotorsion-foundation`, step 8. The main-20261015 ancestor now states the constructible adjoint without that historical foundational paragraph. I retain the existing chapter, unit, ancestry and via list; I do not alter the unit route or its realized fields. The elementary categorical tools used are existing Mathlib leaves, so there is no off-route theorem substitution.

## Not duplicates

No new nodes. Searched the whole DAG by Yoneda, splicing, pullback, epimorphism, tags 06XT/06XP/08N3/05PK and declaration `epi_pullback_of_epi_f`. Ran whole-blueprint searches `Yoneda pullback splice`, `Yoneda`, `pullback`, `epimorphism universal`, `epimorphisms pullback`, `cartesian-kernel`, `05PK`, and `epimorphism`. No imported node states the item. `lem-coef-yoneda-zero-splice` concerns equivalence under a fixed splice and annihilation of a zero prefix; it does not prove prefix replacement. `lem-coef-yoneda-derived-ext-comparison` concerns passage to derived Ext, which this argument does not need. Reused `lem-sp-abelian-refinements` instead of creating the proposed pullback-epi node; its general lifting criterion gives the required projection epimorphism directly.

## Review by N4

I read Stacks `derived.tex`, Tag 06XT (`definition-yoneda-extension`), and `homology.tex`, Tag 010I (`section-extensions`), including its pullback construction. I also opened Tag 08N3 (`lemma-cartesian-kernel`), Tag 08N4 (`lemma-cartesian-cocartesian`), Tag 05PK (`lemma-epimorphism-universal-abelian-category`), and checked their labels in `tags/tags`. The prefix replacement below is an explicit agent argument following these constructions; I mark proof_origin as agent, rather than claiming Stacks states this full lemma verbatim. I opened every cited DAG file and copied its actual statement into citations.json. There are no new nodes to audit.

Step 1 uses `def-sp-abelian` for kernels and monomorphism cancellation, `def-weil-pbc-exact-sequence` for the meaning of exactness, and `lem-weil-pbc-abelian-exact-iff-epi-kernel-lift` exactly for the induced epic map to a kernel. The original exactness at E_0 supplies the hypotheses for d:E_1→L. For the new tail, the map to the kernel is its identity. The monicity of the kernel inclusion, and the assumed epicity of ep, finish the tail. No epicity of p is inferred.

Step 2 constructs the pullback as a kernel in a finite biproduct, using exactly the data of `def-sp-abelian`. The displayed correspondence with compatible pairs proves the universal property explicitly. The incoming object is T for n=2 and E_2 otherwise, so there is never an undefined E_2 in degree two. The zero second component and vanishing consecutive composites ensure the new incoming map exists and remains a differential.

Step 3 uses precisely clause (a) of `lem-sp-abelian-refinements`, first with d and then with s. For every arbitrary-domain arrow to K it supplies a lift after an epimorphic refinement. The pullback universal property gives the intermediate lift. This is a three-line consequence of the cited statement, so I did not create an elementary node for it.

Step 4 uses exactly clause (b) of that same node, first at E_1 in the original sequence and then at Q in the replacement sequence. Both projections of the lifted maps are checked. Domains are arbitrary objects; this is valid in an arbitrary abelian category, without assuming it is concrete, has elements, or has enough projectives.

Step 5 uses `def-weil-pbc-exact-sequence`. For n=2, the projection of the new first map is the old mono, hence the new map is mono. For n>2, the two-projection test identifies ker j with ker b at E_2. All further-left arrows stay identical. This establishes every term of the pulled-back prefix, not merely its last surjection.

Step 6 uses the exact-sequence definition and the kernel-lift epicity criterion at P. At Q monicity of K→P identifies the outgoing kernel with ker s. At P the map to ker(ep) is s, epic by Step 3. These are the two exactness checks needed for splicing; neither is hidden behind a generic assertion that splicing preserves exactness.

Step 7 has no external dependency: it checks the incoming square rj=b, the joining square p i s=ell a s=ell d r, the F square, and every unchanged square. In degree two rj=b is also the left-endpoint square. This single endpoint-fixing morphism gives equivalence by the definition in the item's statement. In the common-refinement convention actually printed in Tag 06XT, take the replacement extension itself as middle row and use its identity map and this comparison.

I checked delivery-errors B–E: no statement-only child carries a hidden proof; no notions are supplied by unrelated definitions; no new source/tag or Mathlib leaf needs validation; the cited statements supply the precise clauses used; no definition node stands in for the projection-epic theorem. There are no dependencies back to the item, no child restating a clause, and no change to hypotheses or coefficient categories. Every step is below 2000 characters. Exactness, the kernel comparison, and commutation are explicit rather than asserted as transport.

Small cases: for n=2 the result is the familiar short-exact pullback followed by its short exact tail; for n=3 the only additional check is ker j=ker b at E_2. For p=identity the kernels identify and the comparison reduces to the original sequence. For F=0 even p=0 is allowed, K=P, L=E_0 and the pullback of d along zero gives the appropriate zero K-component incoming map. For T=0 the same kernel and lift tests apply. A split tail is also allowed. None requires an injective or projective object or any smallness of Ext groups.

There was no returned delivery to repair. The important changes from the initial draft plan were replacing an unnecessary new pullback-epi leaf by the existing refinement criterion, explicitly treating degree two, and verifying the joining comparison equation.

## Unfinished work

None within this one-level stage-1 split. No Lean was written or compiled. The server dry run and direct push are the remaining delivery checks.
