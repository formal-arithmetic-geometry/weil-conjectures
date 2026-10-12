# HomologicalComplex₂.firstQuadrantExtension comparison aliases

## Reason

The complete proof uses explicit aliases for the double-extension functor and bicomplex,
and a canonical isomorphism between a surviving extended summand and its original summand.
These are real constructions using existing extension functors and extendXIso. The public
aliases keep the type of the bicomplex explicit during elaboration; all total comparison maps
and lemmas remain private. These additions change no existing signature or definition.

## Old

The three auxiliary declarations did not exist. The existing theorem signature is unchanged.

## New

The new declarations, in namespace `HomologicalComplex₂.firstQuadrantExtension`, are:

```lean
noncomputable abbrev firstQuadrantExtensionFunctor :=
  (embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
    embeddingUpNat.extendFunctor (CochainComplex C ℤ)

variable (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The extended double complex, with its firstQuadrantExtendedBicomplex type made explicit. -/
noncomputable abbrev firstQuadrantExtendedBicomplex : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (firstQuadrantExtensionFunctor (C := C)).obj K

variable [HasTotal (firstQuadrantExtendedBicomplex K) (up ℤ)]

/-- The identification of an extended summand in nonnegative bidegree. -/
noncomputable def firstQuadrantExtendedTermIso (a b : ℕ) :
    ((firstQuadrantExtendedBicomplex K).X (a : ℤ)).X (b : ℤ) ≅ (K.X a).X b :=
  (HomologicalComplex.eval C (up ℤ) (b : ℤ)).mapIso
    ((((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K).extendXIso
      embeddingUpNat (i := a) rfl) ≪≫
    (K.X a).extendXIso embeddingUpNat (i := b) rfl


```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FirstQuadrantTotalExtension | G1 | Its proof uses the new helpers. |

No pre-existing downstream module can mention these new names. No adaptations are required.
The meaning and elaborated type of every pre-existing statement, including every target,
stays identical.

## Status

landed 20261012T204508-L-869070 2026-10-12 (merge of deliver/G1/Sheaf.Algebra.Homology.FirstQuadrantTotalExtension)
