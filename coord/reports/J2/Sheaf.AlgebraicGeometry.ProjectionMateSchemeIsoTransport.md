## What changed

Proved the existing `AlgebraicGeometry.projectionMate_schemeIso_transport` from
one new geometric comparison theorem and the existing scheme-isomorphism derived
equivalence and quasi-coherence lemmas. The theorem's signature, universes and
visibility are unchanged. Added only proof imports to the item's module.

The categorical argument is fully implemented in private helpers: a transported
Hom equivalence and adjunction, the lifted tensor-pullback comparison, its explicit
image under the equivalence, the transported counit equation, the mate-square
calculation, and naturality in the two coefficients. The conclusion composes two
explicit arrow isomorphisms. These helpers have complete proofs and constructions;
none uses a new hole to construct data in a definition.

Added `Sheaf.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons` for the geometric
part of step 1: tensor, pullback and direct-image natural isomorphisms for supplied
isomorphism-induced equivalences with localization factorizations. Updated the
parent DAG proof to follow the Lean argument. No definition, existing statement,
target, public import or other module was changed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.projectionMate_schemeIso_transport`
(`lem-pc-projection-mate-scheme-iso-transport`). No `sorry` remains in the item.

Added one hole:
`AlgebraicGeometry.schemeIso_derived_functor_comparisons`
(`lem-pc-scheme-iso-derived-functor-comparisons`). Its proof is exactly `by sorry`
in its own new module, with a source and complete proof in words in the docstring
and a matching DAG node. It asserts only the four functor comparisons, with no
adjunction, tensor-pullback comparison, coefficients, quasi-coherence or mate
conclusion. The entire categorical conjugation and quasi-coherent coefficient
assembly are proved in the item. This is a decomposition: one hole closed, one
hole added, net zero before downstream pruning; it is not a claim of a complete
sorry-free proof of the geometric assertion.

Local compilation of both delivery modules succeeds. The delivery dry run is the
final gate. The interface checker reports no changes to the existing module
interface; the original theorem statement and all original public imports remain
identical. Edge cases were checked mathematically: empty schemes and zero
complexes still have the same exact equivalences and comparisons; identity scheme
isomorphisms reduce to localization comparisons and identity tensor maps. The
categorical proof uses arbitrary natural alpha and beta, arbitrary supplied p and
t, and arbitrary coefficients, and assumes neither projection mate is invertible.
Independent morphism universes w and w' are preserved throughout.

## No longer needed

No original import, proof-dependency node or module is pruned: all original
geometric dependencies remain needed, directly or through the new comparison
node. Removed a redundant experimental import of
`Mathlib.CategoryTheory.Functor.FullyFaithful` before final compilation; its API
is already available through the original imports. No candidate theorem found in
the searches was imported. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first dry run conservatively classified global helper variables and an extra
`open` as an interface change. The helpers were refactored to explicit binders and
scoped elaboration options, preserving the original module commands; the interface
checker now reports no changes. No tool was modified or bypassed.

The original plan's step 1 requires tensor and derived-functor comparison
isomorphisms which the two recorded scheme-isomorphism theorem signatures do not
supply. Those signatures give localization equivalences and preservation of
quasi-coherent cohomology. The new comparison node makes the missing geometric
interface explicit rather than using facts found only in their proof text.

The calculation does not need a separately supplied theorem identifying beta as
the conjugate of alpha. Constructing q by the transported Hom equivalence gives
the required counit identity for any natural alpha and beta of the specified
types. This identity and the formula for s are proved before the mate calculation.
No unit-level route is bypassed: `sk-thm-picard-duality.realized` has no statement
or step assigned to the item, and the original scheme-isomorphism argument is kept.

The blueprint ancestor helper prints `None` because the parent's `created.item`
is a module name. The new node inherits the parent's recorded blueprint ancestor
`lem-sc-finite-duality`, exact source place, and via chain. Blueprint searches for
projection mates, scheme isomorphisms, derived tensors and isomorphism transport
found no matching imported blueprint statement. LeanFinder found only underived
pushforward ingredients; Loogle found categorical conjugation ingredients; grep
found no exact Mathlib result. LeanSearch was unavailable with an internal server
error and is recorded as unavailable.

## New nodes

`lem-pc-scheme-iso-derived-functor-comparisons`, in
`dag/nodes/sec-picard-framework/lem-pc-scheme-iso-derived-functor-comparisons.json`,
is the four geometric comparison isomorphisms needed before constructing q and s.
It lives in `Sheaf.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons`. Its source
is the scheme-isomorphism expansion of Stacks Tag 08EU's affine reduction, using
the K-flat construction of Tag 06YI and the K-injective construction of Tag 079V.
The proof and docstring spell out preservation of K-flatness and K-injectivity,
comparison on representatives, descent and independence of localization universes.
No change record is needed because no existing interface changed.

## Second reading by J2

1. **Interface and statement:** I compared the delivered item against the repository version byte for byte. The target theorem signature, universes, hypotheses, conclusion, and existing public imports are unchanged. The added comparison theorem is a strictly smaller geometric interface: four natural isomorphisms, with no adjunction, coefficients, quasi-coherence, or mate conclusion.

2. **Proof and axioms:** I compiled both delivered modules with the launcher compiler. The item has no remaining sorry; the only sorry is the named split theorem `schemeIso_derived_functor_comparisons`, whose docstring gives its source and proof plan. The item proof uses private constructions for the transported Hom equivalence, adjunction, tensor comparison, mate square, and coefficient naturality. No forbidden declarations or hollow definitions were found; the split theorem is the sole declaration carrying `sorry`.

3. **Split statement:** I checked the new node and theorem against the four comparison clauses in the parent proof. It is true in the stated generality as the intended scheme-isomorphism geometric reduction, and is strictly weaker than the parent target. Its docstring, source, blueprint fields, search record, Lean statement, and DAG node agree. Small cases (identity isomorphisms, empty schemes, and zero complexes) introduce no missing hypotheses.

4. **Pruning and route:** The proof follows the recorded route through scheme-isomorphism derived equivalences, geometric comparisons, transported adjunction/tensor data, and quasi-coherent inverse preservation. I checked the imports and removed the redundant experimental `Mathlib.CategoryTheory.Functor.FullyFaithful` import; all remaining imports are used. No original proof dependency or module is pruned, and the unit route is not bypassed.

5. **DAG consistency:** The parent node's proof and `proof_deps` include the new comparison node and match the Lean construction. The new node has the required statement, source, searches, blueprint ancestry, Lean record, and split status. No existing declaration statement or definition was changed.

**Changes made while second reading:** appended this review section only. No Lean, node, or import changes were needed after compilation and interface comparison.
