/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryKunnethMap

/-!
# The absolute and relative canonical Künneth arrows

Source: Stacks Project, Tag 0F1E, the adjoint definition of the Künneth map.
(blueprint: lem-pur-absolute-kunneth-comparison).
-/

@[expose] public section

universe u uA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

section
variable {C A : Type*} [Category C] [Category A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  {T : C} (hT : IsTerminal T)
attribute [local instance] Sheaf.monoidalCategory

end

section Pullback
variable {C D A : Type*} [Category C] [Category D] [Category A]
  [MonoidalCategory A] [BraidedCategory A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [F.IsContinuous J K]
attribute [local instance] Sheaf.monoidalCategory

omit [MonoidalCategory A] [BraidedCategory A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
end Pullback

section SectionMaps
variable {C B : Type*} [Category C] [Category B] [MonoidalCategory B]
    (J : GrothendieckTopology C) [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
attribute [local instance] Sheaf.monoidalCategory

end SectionMaps

omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
attribute [-instance] evaluationMonoidal sectionsMonoidal
  constantPresheafAdj_monoidal constantSheafAdj_monoidal precomposeEvaluation_monoidal
  sheafSectionsNatIsoEvaluation_monoidal pushforwardSections_monoidal

/-- The canonical right-adjoint comparison associated to pullback of constant complexes.
It is defined by conjugacy, so its counit equation is an adjunction identity.
Source: Stacks Tag 0F1E (blueprint: lem-pur-absolute-kunneth-comparison). -/
noncomputable def ordinaryKunnethSectionsIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (lowerStar A f).rightDerivedFunctor ⋙ rightDerivedGlobalSections A S ≅
      rightDerivedGlobalSections A X :=
  conjugateIsoEquiv
    ((derivedConstantGlobalSectionsAdjunction A S).comp
      (derivedUpperStarLowerStarAdjunction A f))
    (derivedConstantGlobalSectionsAdjunction A X) (derivedConstantPullbackIso A f)

omit [HasSmallSiteSheafify A] [UpperStarPreservesFlat A] in
/-- Relative Künneth, transported through the constant-complex adjunctions.
The point tensor comparison is the mate of the tensor of its two counits.
All comparison data are explicit canonical adjunction maps.
Source: Stacks Tag 0F1E (blueprint: lem-pur-absolute-kunneth-comparison). -/
noncomputable def ordinaryRelativeGlobalKunnethMap
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (rightDerivedGlobalSections A X).obj K ⊗
        (rightDerivedGlobalSections A Y).obj M ⟶
      (rightDerivedGlobalSections A Z).obj
        (((derivedTensor A Z).obj ((upperStar A p).leftDerivedFunctor.obj K)).obj
          ((upperStar A q).leftDerivedFunctor.obj M)) :=
  tensorHom ((ordinaryKunnethSectionsIso A f).inv.app K)
      ((ordinaryKunnethSectionsIso A g).inv.app M) ≫
    ordinaryKunnethTensorMate (curriedTensor (DerivedCategory A))
      (derivedTensor A S) (constantSheaf S.smallEtaleTopology A).leftDerivedFunctor
      (rightDerivedGlobalSections A S) (derivedConstantGlobalSectionsAdjunction A S)
      (constantSheaf S.smallEtaleTopology A).leftDerivedTensorComparison
      ((derivedConstantGlobalSectionsAdjunction A S).counit.app _)
      ((derivedConstantGlobalSectionsAdjunction A S).counit.app _) ≫
    (rightDerivedGlobalSections A S).map (kunnethMap A p q f g (p ≫ f) rfl w K M) ≫
    (ordinaryKunnethSectionsIso A (p ≫ f)).hom.app _

/-- The tensor-of-pulled-counits adjunct is relative Künneth transported by the
canonical right-adjoint comparisons for constants.

Source: Stacks Project, Tag 0F1E, terminal-topos specialization of the adjoint
construction in blueprint order 1740.
(blueprint: lem-pur-absolute-kunneth-comparison).

Proof: The comparisons identifying a constant complex on a source with the pullback
of a constant complex compose. This follows on sheaves from the constant-pullback
composition law, and after deriving from the counit normalization of the exact-functor
composition comparisons. They respect tensor: the constant-presheaf tensor constraints
have identity components, sheafification is monoidal, and the derived tensor comparison
respects monoidal natural isomorphisms and compositions of exact functors.
Transpose the claimed equality by the constants/sections adjunction on Z. The conjugate
counit equations for ordinaryKunnethSectionsIso replace each sections comparison by the
constant-pullback comparison followed by the composite adjunction counit. Naturality
moves the tensor of the two sections comparisons past the constant tensor constraint.
Expand the two Künneth adjuncts. Use the constant-pullback composition law for p,f and
q,g, and tensor compatibility to identify the front comparison. The unit and counit
at S cancel by the two triangle identities. Both sides now equal the constant tensor
comparison on Z followed by the tensor of the pulled-back counits on X and Y.
Injectivity of the adjunction bijection proves equality. This argument needs neither
coefficient finiteness, finite type, cartesianness, nor an equivalence at S; the empty
scheme and zero complexes obey the same adjunction identities. -/
theorem ordinaryGlobalKunnethMap_eq_relative
    {S X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (w : q ≫ g = p ≫ f)
    [(constantSheaf S.smallEtaleTopology A).PreservesFlat]
    [(constantSheaf Z.smallEtaleTopology A).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ordinaryGlobalKunnethMap A p q K M =
      ordinaryRelativeGlobalKunnethMap A p q f g w K M := by sorry

end AlgebraicGeometry.Etale
