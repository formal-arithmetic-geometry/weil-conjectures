/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Derived Hom computed by a bounded-above projective resolution

Source: Stacks Project, More on Algebra, Tag 0A5W, Lemma 15.75.2;
Derived Categories Tag 06XR (blueprint: lem-sc-derived-hom-projective-resolution).

The ring `A` is the structure ring of the one-point ringed site
(`CochainComplex.onePointRingSheaf A`), so `A`-modules are the sheaves of modules
on that site and `R Hom_A` is the landed `derivedInternalHom` there.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory

/-- A bounded-above complex of projective modules resolving `F` computes
`R Hom_A(F[0], G[0])` by the ordinary Hom complex `Hom^•(E, G[0])`, and hence the
cohomology of that complex in every integer degree.
Source: Stacks Project, More on Algebra, Tag 0A5W, Lemma 15.75.2;
Derived Categories Tag 06XR (blueprint: lem-sc-derived-hom-projective-resolution).

Proof:
1. By `lem-sc-bounded-above-projective-kprojective` (`CochainComplex.isKProjective_of_projective`)
   `E` is K-projective, so `Hom^•(E, -)` sends the quasi-isomorphism `η_{G[0]} : G[0] → I(G[0])`
   of any functorial K-injective replacement to a quasi-isomorphism.
2. Since `I(G[0])` is K-injective and `e` is a quasi-isomorphism, precomposition with `e`,
   `Hom^•(F[0], I(G[0])) → Hom^•(E, I(G[0]))`, is a quasi-isomorphism.
3. By `def-pur-derived-internal-hom` (`derivedInternalHom_comparison`),
   `Q Hom^•(F[0], I(G[0]))` is `R Hom(F[0], G[0])`; composing the localized maps of
   steps 1 and 2 gives the representing isomorphism `c`.
4. Applying `DerivedCategory.homologyFunctor i` to `c` and
   `DerivedCategory.homologyFunctorFactors` gives the identification of cohomology in
   every degree `i : ℤ`. -/
theorem derivedHom_projectiveResolution
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))]
    (F G : SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
    (E : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A))) ℤ)
    (d : ℤ) [E.IsStrictlyLE d] [∀ n : ℤ, Projective (E.X n)]
    (e : E ⟶ (HomologicalComplex.single (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))
      (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso e] :
    Nonempty (DerivedCategory.Q.obj (homComplex (R := CochainComplex.onePointRingSheaf A) E
        ((HomologicalComplex.single (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
        (op (DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj F)),
          DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G))) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).obj (op E)).map
            (η.app ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)))) ∧
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf A)).map e.op).app
            (I.obj ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G))))) ∧
    ∀ i : ℤ, Nonempty
      ((HomologicalComplex.homologyFunctor (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) i).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) E
          ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)) ≅
      (DerivedCategory.homologyFunctor (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf A))) i).obj
        ((derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
          (op (DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj F)),
            DerivedCategory.Q.obj ((HomologicalComplex.single (SheafOfModules.{u}
              ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
                (CochainComplex.onePointRingSheaf A))) (ComplexShape.up ℤ) 0).obj G)))) := by
  sorry

end CategoryTheory
