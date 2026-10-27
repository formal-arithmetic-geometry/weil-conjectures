## What changed

Prove `CategoryTheory.RingedHomRestriction.ordinary_comparisons` with its existing
statement. All additional helpers are private and proved in the assigned module.
The proof uses the canonical Hom-complex projection API through a private import
of `WeilConjectures.Algebra.Homology.HomComplexComponents`, together with Mathlib
sheaf limits and preservation of products. The original public imports stay.

Construct the factor map for direct continuous restriction by precomposing local
linear maps with `Over.post`. Use the explicit identity restriction-of-scalars
isomorphism to transport this map to Mathlib's standard pushforward functor. For an equivalence on each slice, prove this is invertible:
precomposition is fully faithful on abelian presheaves, and the preimage is linear
by transport along essential-surjectivity isomorphisms. Restriction preserves
products because its underlying abelian presheaf is precomposition. Package the fixed Hom-complex functor and factor bifunctor in the private
`ComplexHomShape` structure, with the projections, limit property, differential
formula and functoriality formula in `ComplexHomData` indexed by that shape.
The differential data keeps the source API's unit-valued sign. Convert it to an
integer scalar only in the abstract category calculation, avoiding expensive
normalization of concrete sheaf morphisms.
`ordinaryShape` and `ordinaryData` explicitly supply this data from the existing
proved projection API. Prove the complex comparison generically for these
structures in preadditive categories, then specialize to sheaf modules. This
keeps repeated unfolding of the concrete chosen Hom complex out of the generic
proof and out of the specialization interfaces. Product universal properties produce the graded isomorphisms. Projection formulas
and factor naturality prove the signed differential identity and naturality in
both complexes. Specialize to `Over.forget` and `Over.map`; the iterated-slice
equivalence supplies the required equivalences. Finally project the compatibility
equation and evaluate local maps; the factor coherence is reflexivity, with
`overFunctorMap` providing identity transport.

All helper constructions have explicit data; isomorphism inverses use proved
bijectivity and product universal properties only. The direct restriction helper
avoids costly unfolding of identity change of scalars. Separate private factor
interfaces convert to the standard restriction functors before the complex
construction; named comparison definitions and their projection lemmas keep
this conversion out of the final compatibility calculation. The final
comparisons use exactly the standard functors specified in the theorem. Private
construction definitions become locally irreducible after their proved API;
no global attribute is changed. Each comparison and its projection equation are
kept together in a private `ComparisonData` structure, so the final proof uses
the stored equation directly.

The construction applies to arbitrary unbounded complexes, zero complexes,
identity arrows, arbitrary nonmonomorphisms, and the empty site. No step assumes
boundedness, a nonempty object type, or monicity of a site arrow. The target
statements, all definitions used by targets, and the adopted source tree are
unchanged. Update the item's proof route and dependencies to match the proof.

## Proved and sorry left

Closed: `CategoryTheory.RingedHomRestriction.ordinary_comparisons`
(`lem-ringed-hom-restriction-ordinary`), the module's only original hole.
Added: none. Remaining in the delivered module: none. This is a proof, not a
decomposition; all helper proofs are complete.

## No longer needed

The stated proof dependency `lem-sc-internal-hom-over-naturality`
(`WeilConjectures.Algebra.Homology.InternalHomOverNaturality`) is unnecessary for
this proof: naturality of the generic `Over.post` factor map is proved directly
by evaluating local maps. No original imports were removed. No module is
withdrawn: the original sheaf naturality lemma has other users. Neither
`Sheaf.CategoryTheory.NativeRingedRestrictionHom` nor
`Sheaf.CategoryTheory.ElementRestrictionHom` is imported: their objectwise
existence conclusions do not specify the projections needed for coherence.
The added dependency `lem-sc-hom-complex-projections` is the existing proved
projection API, not a new obligation. No unit statement or unit proof step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The original dependency declarations specify the Hom complex and the sheaf
restriction comparison but do not directly state naturality and coherence for
Hom complexes. The existing projection API gives a direct proof without further
splitting. The existing objectwise restriction theorems do not themselves imply
the coherence assertion, so choosing their arbitrary witnesses would not have
sufficed. No mathematical statement correction was needed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
