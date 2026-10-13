## What changed

Reduced `AlgebraicGeometry.exists_canonicalDerivedTensorHom` to two strictly separate
parts: construction of normalized natural functions, and bijectivity of any such
functions. The parent obtains the functions, applies the bijectivity theorem, builds
`Equiv.ofBijective` componentwise, and transfers the two normalization clauses by
definitional equality. This is a decomposition, not a sorry-free proof of the
mathematical adjunction.

Added `CanonicalDerivedTensorHomMapExistence` and `CanonicalDerivedTensorHomMapBijective`,
each with one named public theorem. Added the shared model module
`CanonicalDerivedTensorHomModel` to let these modules import the representative
constructions without an import cycle. All five existing definitions moved there
have identical names, signatures, bodies and public visibility; the parent publicly
imports them. The new `IsCanonicalDerivedTensorHomMap` repeats the exact naturality
and representative equations for functions, without asserting bijectivity. No
arbitrary natural family is chosen in a definition. The original uniqueness proof
and the uniquely characterized final `schemeDerivedTensorHomEquiv` are unchanged.

The existing node now records the actual reduction and preserved uniqueness proof.
Interface extraction is recorded in
`coord/changes/canonical-derived-tensor-hom-model.md`.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_canonicalDerivedTensorHom` of
`def-pc-canonical-derived-tensor-hom-bijection`, by a complete Lean combination proof.
There are no sorries left in the item module. Added two holes, counted as a
one-to-two decomposition (net minus one), not as completion of the adjunction:

- `AlgebraicGeometry.exists_canonicalDerivedTensorHomMap`, node
  `lem-pc-canonical-derived-tensor-hom-map-existence`: only existence and coherence of
  functions; no inverse or bijectivity requirement.
- `AlgebraicGeometry.canonicalDerivedTensorHomMap_bijective`, node
  `lem-pc-canonical-derived-tensor-hom-map-bijective`: injectivity and surjectivity
  under the full, explicitly normalized function predicate; no existence assertion.

Every new hole is the whole proof of a named public theorem in its own new module,
with a detailed source-based proof in words. The model module has no sorry and all
its data are real constructions. All four modules compile together through lcompile.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.HomTensorTotal`; the declaration
`CategoryTheory.homComplex_tensorTotal_iso` and node `lem-sc-derived-hom-tensor-total`
are not used by this reduction or by either new proof plan. That existential
isomorphism does not specify the pinned component normalization. The two new plans
reuse the existing normalized HomTensorDegreewise, HomTensorDifferential,
HomTensorNaturality and HomComplexGlobalCochains lemmas for that calculation.
HomTensorTotal remains reachable transitively through KInjectiveHomComplex;
no whole module is claimed pruned from the import closure.
This is pruning of this item's route, not a claim that other targets do not use it.

The three former public imports (DerivedInternalHom, CanonicalPullbackTensorComparison,
and upstream MonoidalClosed) are relocated unchanged to the public model module;
they are not pruned. KFlatResolution, KInjectiveHomComplex and Mathlib KInjective
remain proof imports of the parent and are used by its existing uniqueness proof.
No other existing dependency is claimed unnecessary.

## Where the brief, the DAG or earlier work was wrong

The prior proposal incorrectly inferred the fixed representative normalization from
naturality. A sign-twisted natural equivalence has the wrong evaluation, so that
proposal is not reused. Here the first new theorem constructs already normalized
functions, and the second assumes that same full normalization; neither asserts
that arbitrary natural functions have it. Negating a map over Spec(Q) violates this
hypothesis, and the zero-object cases cause no invertibility issue (singleton Hom
sets). The final inverse functions are chosen only from bijectivity, which fixes
them uniquely.

The original plan's HomTensorTotal statement is insufficient for the requested
normalization: it asserts an existential isomorphism, without its component
coordinates. The replacement names the normalization at the function level and
separates the two inverse laws. No existing statement is weakened, and the
sk-thm-picard-duality unit's empty realized record is unchanged. The extracted
model definitions are byte-for-byte identical in declaration text. No existing
consumer requires adaptation.

Searches were actually run via msearch: Lean Finder found generic Tor and the
K-injective localization bijection; grep located Equiv.ofBijective and its
reducible forward map. LeanSearch returned HTTP Internal Server Error and Loogle
was unavailable; those are recorded as unavailable, not as no-match findings.
The local literature payload is absent on this machine; the official Stacks pages
for 08DJ and 0A90 were read directly. Blueprint search returned no matching node.

## New nodes

`def-pc-canonical-derived-tensor-hom-model` records the unchanged extracted
representative definitions and the new function-valued normalization predicate in
`Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel`. It has no proof hole.

`lem-pc-canonical-derived-tensor-hom-map-existence` records the normalized function
construction in `Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapExistence`.
Its proof plan uses K-flat resolutions, Hom into K-injectives, the K-injective
localization Hom bijection, and sheaf tensor-Hom currying with the exact coordinates.

`lem-pc-canonical-derived-tensor-hom-map-bijective` records bijectivity in
`Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomMapBijective`. It uses inverse
componentwise currying on homotopy classes and transports the two inverse laws
along representative isomorphisms. It neither depends on the new existence theorem
nor on the parent node, so the two proof items can be worked independently.

## Second reading by M4

1. Compared repository and delivery with diff and checked all eight original
   declarations with the project's declaration parser. Every existing statement is
   identical. The five extracted definitions, including bodies and docstrings,
   form a byte-for-byte identical block in the model module. The uniqueness proof and
   final choice definition are unchanged. The public model import re-exports the
   three former public imports. Verdict: no target or existing meaning changed.
2. Compiled all four delivered modules with lcompile in import order. Inspected all
   data definitions: none contains a sorry or chooses an arbitrary new natural map.
   The final family is determined by the unchanged uniqueness theorem; the inverses
   in Equiv.ofBijective are fixed by bijectivity. Only the two reported named theorems
   retain sorry. No forbidden declaration or attribute occurs. Explicit axiom checks
   and deliver3's per-declaration probes check the allowed axioms, including sorryAx
   from the two open lemmas and imported open results.
3. Matched each new statement to its node and full normalization predicate. The map
   existence theorem omits inverse laws; bijectivity assumes an already normalized
   family and asserts no existence. These are separate proper parts of the argument,
   not renamed copies of the original equivalence existence statement. Checked the
   zero-object/empty-scheme case (singleton morphism sets) and degree-zero complexes
   over a field (ordinary tensor-Hom adjunction). For homogeneous degrees p,q the
   Hom differential gives d(phi(x))(y) - (-1)^p phi(x)(d y), precisely the total tensor
   differential d x tensor y + (-1)^p x tensor d y. A negated nonzero evaluation map
   fails the normalization, so naturality alone has not been mistaken for canonicity.
   Read Stacks Tags 08DJ and 0A90 and searched independently with Lean Finder, Loogle
   and grep using homotopy-class/currying queries. Found existing degreewise normalized
   currying and global-cochain comparison lemmas and repaired both proof plans to
   reuse them. Neither open theorem duplicates an existing normalized derived family.
4. Checked the reduction from the top: Equiv.ofBijective keeps its forward function
   definitionally, so the two normalization clauses transfer without weakening.
   Retained all three imports used by the existing uniqueness proof. Removed only
   the old direct HomTensorTotal proof import; corrected the report to distinguish
   that removal from pruning the module, which is still imported transitively.
   The unit sk-thm-picard-duality has realized.statement=[] and realized.steps=[[]];
   it is unchanged and no realized unit step is bypassed. Verdict: valid decomposition,
   one old hole closed and two added, net minus one; no full adjunction proof claimed.
5. Compared old/new parent proof_deps: only lem-sc-derived-hom-tensor-total was
   removed; the K-flat, K-injective Hom and localization-Hom dependencies remain.
   The parent records the new combination and unchanged uniqueness argument. Each new
   node has source, self-contained statement, proof, dependency union, proof_origin,
   searches, creation, blueprint, unit/chapter and Lean fields. Added the existing
   degreewise, differential, naturality and global-cochain nodes to both new plans,
   with plain proof imports in their modules. Checked all 379 downstream modules:
   unchanged names, bodies and public re-exports require no adaptations. Expanded the
   change record's Users table accordingly and restored its Old block verbatim.

Second reading changed the two proof plans and their proof imports/dependencies,
the inaccurate Tag 0A90 parenthetical, the change record's verbatim Old and complete
Users sections, and the report's pruning qualification. No mathematical signature
or existing proof was changed by this reader. The two remaining proofs require
localization/coherence work and cannot be closed by a short application of the
existing component lemmas.
