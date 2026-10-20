# CategoryTheory.affineProjectiveComplexDerivedHom

## Reason

The stage-3 preflight requires a change record for the new file-level commands.
The proof introduces section variables for private helpers and locally marks
`homComplexFunctor` and `derivedInternalHom` irreducible to avoid expanding their
large constructions during elaboration. Those attributes are local to this module.
The public theorem signature and the three public imports are unchanged; there is
no semantic interface change, no target-definition change, and no consumer adaptation.
All newly introduced helpers are private and proved.

## Old

The original theorem signature, verbatim:

```lean
theorem affineProjectiveComplexDerivedHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R)))]
    (P L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R))) ℤ)
    (d e : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE e]
    [∀ n : ℤ, Projective (P.X n)] :
    Nonempty (DerivedCategory.Q.obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P L) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf R)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L)) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op P)).map
            (η.app L)))) ∧
    ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R) P L).homology n)
```

The original private proof import was:

```lean
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
```

## New

The theorem signature is identical, verbatim:

```lean
theorem affineProjectiveComplexDerivedHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R)))]
    (P L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R))) ℤ)
    (d e : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE e]
    [∀ n : ℤ, Projective (P.X n)] :
    Nonempty (DerivedCategory.Q.obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P L) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf R)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L)) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op P)).map
            (η.app L)))) ∧
    ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R) P L).homology n)
```

The private proof imports are now:

```lean
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.HomComplexComponents
```

The local attribute command is:

```lean
attribute [local irreducible] homComplexFunctor derivedInternalHom
```

The added section variables supply explicit `HasSheafCompose` instances to private
helpers. They do not add a binder to the public theorem. No local helper or local
attribute is exported as a public declaration or an instance for consumers.

## Users

`tools/downstream.py Sheaf.Paper.AffineProjectiveComplexDerivedHom --uses
CategoryTheory.affineProjectiveComplexDerivedHom` lists the two downstream modules
below. Its textual declaration-use search finds only the item itself: the consumers
currently import the dependency for their planned proofs. The direct consumer's
source and its statements were read; they use the same original public imports and
no newly private name. The second consumer is reached through that direct consumer. An ordered `lcompile.py --all`
check compiled the changed item first (54.0 seconds), then the unchanged direct consumer
(5.2 seconds), then the unchanged transitive consumer (7.1 seconds), all with exit code 0
and no diagnostics. The unchanged consumer copies were removed from the delivery packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineProjectiveComplexDerivedHom | F5 | Original proposition proved; unchanged public signature and imports. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed in shared snapshot | Direct importer; unchanged source and statements; no adaptation. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed in shared snapshot | Transitive importer; unchanged source and statements; no adaptation. |

## Status

landed 20261020T211708-L-3489696 2026-10-20 (merge of deliver/F5/Sheaf.Paper.AffineProjectiveComplexDerivedHom)
