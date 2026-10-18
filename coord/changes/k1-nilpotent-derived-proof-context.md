# DerivedCategory.isZero_homology_of_nilpotent_derived_reduction

## Reason

The delivery preflight requests a change record because it conservatively classifies the
added `MonoidalCategory` open command and proof elaboration options as changes to what
importers see. They support the private tensor-comparison helpers and the proof. Every
helper instance is explicitly `private local instance`; no new global instance registration,
public definition, or existing signature is introduced or changed. All new imports are
proof-only imports. The four original public imports are retained verbatim.

## Old

The original open command was:

```lean
open CategoryTheory CategoryTheory.Limits
```

The original public theorem signature was:

```lean
theorem isZero_homology_of_nilpotent_derived_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules (A ⧸ I))]
    (E : RingSiteModules A ⥤ RingSiteModules (A ⧸ I))
    (hobjects : ∀ M : RingSiteModules A,
      E.obj M = SheafOfModules.changeOfRings (ringSiteMap (Ideal.Quotient.mk I)) M)
    (hmaps : ∀ {M M' : RingSiteModules A} (f : M ⟶ M'),
      E.map f = eqToHom (hobjects M) ≫
        SheafOfModules.changeOfRingsHom (ringSiteMap (Ideal.Quotient.mk I)) M f ≫
          eqToHom (hobjects M').symm)
    [E.Additive]
    (LF : DerivedCategory (RingSiteModules A) ⥤ DerivedCategory (RingSiteModules (A ⧸ I)))
    (ε : Qh ⋙ LF ⟶ E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (RingSiteModules A) (ComplexShape.up ℤ)))
    (C : DerivedCategory (RingSiteModules A)) (b : ℤ)
    (hred : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (RingSiteModules (A ⧸ I)) i).obj (LF.obj C))) :
    ∀ i : ℤ, b < i → IsZero ((homologyFunctor (RingSiteModules A) i).obj C)
```

## New

The proof uses tensor notation through:

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

Elaboration options explicitly disable auto-implicit variables and permit unfolding for
the constant-ring comparison calculations. These options and the open command are local
to elaborating this module. The private equivalence and additive instances are registered
locally, so they add no typeclass instances for importing modules.

The complete public theorem signature is:

```lean
theorem isZero_homology_of_nilpotent_derived_reduction
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ)
    (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules (A ⧸ I))]
    (E : RingSiteModules A ⥤ RingSiteModules (A ⧸ I))
    (hobjects : ∀ M : RingSiteModules A,
      E.obj M = SheafOfModules.changeOfRings (ringSiteMap (Ideal.Quotient.mk I)) M)
    (hmaps : ∀ {M M' : RingSiteModules A} (f : M ⟶ M'),
      E.map f = eqToHom (hobjects M) ≫
        SheafOfModules.changeOfRingsHom (ringSiteMap (Ideal.Quotient.mk I)) M f ≫
          eqToHom (hobjects M').symm)
    [E.Additive]
    (LF : DerivedCategory (RingSiteModules A) ⥤ DerivedCategory (RingSiteModules (A ⧸ I)))
    (ε : Qh ⋙ LF ⟶ E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Qh)
    (hLF : LF.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (RingSiteModules A) (ComplexShape.up ℤ)))
    (C : DerivedCategory (RingSiteModules A)) (b : ℤ)
    (hred : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (RingSiteModules (A ⧸ I)) i).obj (LF.obj C))) :
    ∀ i : ℤ, b < i → IsZero ((homologyFunctor (RingSiteModules A) i).obj C)
```

Its proof is now complete. A normalized textual comparison of the Old and New signatures
passes.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.NilpotentDerivedUpperBound --uses
DerivedCategory.isZero_homology_of_nilpotent_derived_reduction` finds only this module as a
literal symbol user (the declaration itself). It also lists the following five transitive
importers. None is adapted: the existing signature and public imports are unchanged, and
the proof context and helper instances are local. Their claim holders were not queried
because no edit to another group's module is proposed or needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.NilpotentDerivedUpperBound | K1 | Complete proof and private local helpers. |
| Sheaf.RingTheory.NilpotentProjectiveComplexLift | not queried; unchanged | No signature or import change. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | not queried; unchanged | No signature or import change. |
| Sheaf.RingTheory.PseudoCoherentNilpotentInvariance | not queried; unchanged | No signature or import change. |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | not queried; unchanged | No signature or import change. |
| Sheaf.RingTheory.RlimPerfectComplete | not queried; unchanged | No signature or import change. |

## Status

landed 20261018T062818-L-658770 2026-10-18 (merge of deliver/K1/Sheaf.Algebra.Homology.NilpotentDerivedUpperBound)
