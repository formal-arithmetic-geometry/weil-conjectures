# Stage-1 report: lem-sfb-affine-space-invertible-trivial

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-space-invertible-trivial.json: statement, split into three steps; no statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-ufd-invertible-module-trivial.json: statement-only Mathlib leaf. CommRing.Pic.mk_eq_one_iff with instSubsingletonPicOfIsDomainOfIsGCDMonoid, PicardGroup.lean:493 and :886; the UFD-to-GCD instance is at UniqueFactorizationDomain/GCDMonoid.lean:50-51.
- citations.json: every step/node pair has a verbatim statement quote.
- searches.jsonl: actual msearch outputs, retained without alteration.

## Attachments

None for the item. The existing project theorem AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_of_uniqueFactorizationMonoid (Modules/PicardAffine.lean:142) supplies a free generator under a UFD global-functions hypothesis; it is not a declaration of the complete affine-space statement with its sheaf isomorphism. Scheme.Pic.subsingleton_of_isAffine (AffineSpace/PuncturedLine.lean:155) is similarly an affine-UFD Picard statement, not an exact affine-space declaration. The affine-sections theorem already belongs to lem-sc-affine-invertible-sections; no duplicate was created for it.

## WANTED

None.

## Errors and corrections

The original item was unsplit, with no proof or existing sandbox attempt. The statement agrees with Stacks 0BDA, including n=0; no STATEMENT-DISPUTED correction is needed. The imported blueprint ancestry is broken upstream (blueprint_refs.py ancestor reports None). The item already has from.node=null with a precise inherited place and via chain. These maintainer-owned fields were retained, and the new node follows the same ancestry and adds the item to via. No chapter or unit record is changed.

I initially considered adding a finite-projective-local-rank-one algebra lemma. A further whole-DAG search found lem-sc-affine-invertible-sections, whose statement already supplies the exact bijective evaluation hypothesis; the final new node therefore uses that hypothesis and is a Mathlib leaf. No new unsplit bridge was created.

## What remains

No unfinished work within this one-level split. The delivery checks and push are performed after this report.

## Not duplicates

lem-sfb-ufd-invertible-module-trivial vs lem-pur-pid-invertible-module-trivial: both cite 0BCH and use bijective evaluation, but the existing node assumes every ideal is principal. The new node applies to arbitrary UFDs such as k[x,y], which are not PIDs. The extra generality is necessary for n greater than one.

lem-sfb-ufd-invertible-module-trivial vs lem-pur-affine-punctured-line-algebra: both cite 0BCH, but the existing node computes units and Picard groups only for the affine line and its punctured line over a field. It is not a theorem about arbitrary UFD modules or higher-dimensional polynomial rings.

The whole DAG was searched by 0BCH, 0BDA, UFD, unique factorization, polynomial factoriality, invertible sections and projective rank one; blueprint_refs.py searches included affine space, invertible module, UFD, projective rank, 0BCH and 0BDA. Existing lem-per-polynomial-ufd-prime-quotient is reused for polynomial factoriality. Existing lem-sc-affine-invertible-sections is reused instead of adding an affine comparison. Existing lem-trf-line-module-duality is unnecessary since evaluation bijectivity is already the affine-sections conclusion. New-node name searched against the whole DAG before writing; no same id exists.


lem-sfb-ufd-invertible-module-trivial vs lem-trf-k0-class-trivial-invertible: the existing 0B8I citation concerns a rank-one finite projective module with an additional equality [L]=n[S] in K_0(S). No such equality is available here; the new theorem instead assumes the ring is a UFD and needs no K_0 hypothesis.

lem-sfb-ufd-invertible-module-trivial vs lem-trf-k0-determinant-map: the existing node constructs the determinant homomorphism from K_0(S) to Pic(S); it neither assumes a UFD nor concludes that a module is trivial. The new theorem concludes N is isomorphic to R from evaluation bijectivity and unique factorization.

lem-sfb-ufd-invertible-module-trivial vs lem-trf-line-module-duality: the existing node proves evaluation and scalar-endomorphism isomorphisms for a line module over an arbitrary ring. It does not conclude L is isomorphic to R, which fails over rings with nontrivial Picard group. The new theorem assumes a UFD and evaluation bijectivity and concludes triviality.

lem-sfb-ufd-invertible-module-trivial vs lem-trf-regular-local-pic-zero: the existing node only applies to A_f for A a regular local ring. A polynomial ring in multiple variables over a field is not furnished as such a localization. The new theorem applies to every UFD with no local or regular hypothesis, and uses the evaluation form of invertibility.

## Review by Q02

I read the item against divisors.tex, Tag 0BDA, lemma-open-subscheme-UFD, both the statement and its proof. For the whole affine scheme, its route is polynomial unique factorization followed by triviality of the algebraic Picard group; the subsequent proof about arbitrary open subschemes is unnecessary here. I read algebra.tex, Tag 0BC1, lemma-polynomial-ring-UFD, and more-algebra.tex, Tag 0BCH, lemma-UFD-Pic-trivial, with Tag 0B8I, lemma-invertible, for the precise meaning of invertibility. I also read the existing tilde-sections and affine-equivalence statements, sourced to schemes.tex Tags 01HV, 01IA and 01IB. The new node states a pure module theorem, with UFD and evaluation bijectivity written out, rather than hiding a sheaf comparison in a Mathlib match.

For step 1 I opened lem-per-polynomial-ufd-prime-quotient and read its first clause: polynomial unique factorization holds over any PID, not merely over a field. The step proves that the field is a PID by the explicit nonzero-ideal argument before applying that clause. No prime-quotient clause is used. The zero-variable case is included and gives A=k. There is no assumption that k is algebraically closed, perfect or infinite.

For step 2 I opened lem-sc-affine-invertible-sections. Its statement asserts exactly the bijectivity of Hom(N,A) tensor N to A for an invertible sheaf on an affine open. We take U=X, which is affine by its stated construction. I opened the new UFD module leaf: it has exactly those hypotheses and concludes N is isomorphic to A. I verified the Mathlib definition Module.Invertible at PicardGroup.lean:77-78, CommRing.Pic.mk_eq_one_iff at :493-494 and the GCD-domain subsingleton instance at :886-887. The UFD instance supplies IsGCDMonoid at GCDMonoid.lean:50-51, so the algebraic conclusion is the one-line specialization recorded in mathlib_match. I read the search hits rather than treating a semantic result about a dual tensor product as N being isomorphic to R. Searches were run through msearch and their exact query text and output metadata are retained. A second phrasing was tried. This lemma is strictly below the item: its objects are modules, and it neither assumes nor concludes anything about sheaves or affine spaces.

For step 3 I opened def-sc-invertible-module and used its explicit quasi-coherence clause, then opened lem-weil-pbc-affine-tilde-gamma-adjunction. Clause (3) supplies the counit isomorphism for this quasi-coherent M, and clause (1) supplies the functor on both e and its inverse. I opened lem-weil-pbc-spec-module-tilde-sections: it identifies tilde(A) on D(f) with A_f, compatibly with restrictions and module structures. For N=A these are the structure-sheaf basic-open descriptions; the identities therefore glue. This is an elementary use of the already cited constructions, not a hidden tensor comparison. The composite with the inverse counit has the required direction M to O_X. All six cited step/node pairs have verbatim statement quotes in citations.json.

I checked delivery-errors B through E against the final files. The new leaf is self-contained and statement-only; its tensor notation cites its definition, and UFD is defined inline. The source gives the actual Stacks tags and TeX labels. No new node repeats a clause of the item: the proof carries polynomial factoriality, passage to sections and the final sheaf isomorphism. The only cross-unit theorem not already a Mathlib leaf is the existing affine-sections theorem, recorded as a generic tool use; it does not change the inherited stable-curve/projective-frame route. Proof dependencies are exactly the union of uses. No step exceeds 2000 characters, no recursive dependency points back to the item, no SGA source is used, and no Lean or compiler command was run.

Edge cases checked: n=0; n=1; n=2 where a PID-only argument would fail; the trivial line sheaf; arbitrary characteristic and finite fields. The new module lemma requires a nonzero domain, so it does not silently apply a field argument to the zero ring. It asserts rank-one invertible-module triviality, not that every finite projective module over every UFD is free. The existing PID and punctured-line nodes cannot cover the necessary higher-dimensional UFD case.

The first dry run flagged the four additional 0B8I tag overlaps above. I opened each entire statement and added these comparisons; none gives the UFD module theorem under its actual hypotheses.
