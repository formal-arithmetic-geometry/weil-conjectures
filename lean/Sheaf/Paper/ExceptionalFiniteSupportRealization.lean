/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalFiniteRealization
/-! # Compact-support realization of the actual finite adjunction
Source: blueprint def-weil-exceptional-inverse-image.
(blueprint: def-pur-adic-support-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
section CompactSupport
variable (c : Compactification g)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)

/-- Open-extension realization is the mate of the unit-normalized inverse-image
comparison. Its Hom-transpose equation determines the map itself.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: extension by zero is left adjoint to the exact open inverse image in both
presentations. Transport these adjunctions along the realization equivalences and
take the mate of integralExceptionalEtaleInverse. The displayed equation is its
adjunction characterization; bijectivity of the Hom transposes gives uniqueness. -/
theorem integralExceptionalEtaleOpen_existsUnique (n : ℕ) :
    ∃! e : S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i,
      ∀ (M : strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : strictEtaleLevel c.Z (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (h : (S.val.levelOpen n).obj M ⟶ N),
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalEtaleRealization l E c.Z n).map h) =
        (integralExceptionalEtaleRealization l E X n).map
          ((S.val.levelOpenAdjunction n).homEquiv _ _ h) ≫
          (integralExceptionalEtaleInverse l E c.i S.openImage n).hom.app N := by
  sorry

/-- The ordinary open-extension mate, fixed by its transpose equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleOpen (n : ℕ) :
    S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i :=
  (integralExceptionalEtaleOpen_existsUnique l E g c S n).choose

/-- The full exact-localization square on every cochain representative.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleDerivedOpen (n : ℕ)
    (e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory) :
      Prop :=
  ∀ J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategory.map
                ((integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors.hom.app
                   J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory.map
          ((S.val.levelOpenFactors n).hom.app J) ≫
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategoryFactors.hom.app
          (((S.val.levelOpen n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalEtaleOpen l E g c S n).hom (.up ℤ)).app J)

/-- The exact derived open comparison is fixed on every cochain representative by
the recorded exact factorization and the ordinary adjunction mate.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: apply the exact localization functor to the ordinary comparison. The defining
localization factorization is precisely the displayed square. Every derived object
has a complex representative and every derived arrow is a roof; hence that square
also determines the natural isomorphism uniquely. -/
theorem integralExceptionalEtaleDerivedOpen_existsUnique (n : ℕ) :
    ∃! e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory,
      IsIntegralExceptionalEtaleDerivedOpen l E g c S n e := by
  sorry

/-- The exact derived open comparison, specified by its representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleDerivedOpen (n : ℕ) :
    S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory :=
  (integralExceptionalEtaleDerivedOpen_existsUnique l E g c S n).choose

/-- The compact-support realization, literally the open comparison followed by the
proper comparison. Each factor retains its universal normalization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleSupportComparison (n : ℕ) :
    S.levelFunctor n ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (integralExceptionalEtaleDerivedRight l E c.g S.properImage n
      (S.properDerived.level n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integralExceptionalEtaleDerivedOpen l E g c S n) _ ≪≫
    Functor.associator _ _ _
/-- The full compact-support adjunction-transpose normalization.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H)
    (e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H) : Prop :=
  ∀ (M : DerivedCategory (strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (N : DerivedCategory (strictEtaleLevel Y (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (h : (S.levelFunctor n).obj M ⟶ N),
        adj.homEquiv _ _
          ((integralExceptionalEtaleSupportComparison l E g c S n).inv.app M ≫
            (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.map h) =
        (integralExceptionalEtaleRealization l E X n).mapDerivedCategory.map
          ((G.levelAdjunction n).homEquiv _ _ h) ≫ e.hom.app N

/-- The finite exceptional realization is the mate of the already specified compact-
support realization. The Hom-transpose equation fixes its map, including the counit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: compose the generic finite adjunction with the realization equivalences. The
compact-support comparison identifies its left adjoint with the fixed finite compact-
support functor. The induced right-adjoint comparison is uniquely determined by the
Hom-transpose equation. Applying the inverse realization gives its inverse. -/
theorem integralExceptionalEtaleRightAdjoint_existsUnique (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    ∃! e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H,
      IsIntegralExceptionalEtaleRightAdjoint l E g c S n G H adj e := by
  sorry

/-- The finite right-adjoint comparison, fixed by the compact-support counit equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
@[no_expose] def integralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H :=
  (integralExceptionalEtaleRightAdjoint_existsUnique l E g c S n G H adj).choose

end CompactSupport

end WeilConjectures
