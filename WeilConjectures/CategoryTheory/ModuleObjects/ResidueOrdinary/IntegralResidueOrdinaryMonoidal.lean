/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal

/-! # Strong monoidal ordinary pullback for condensed coefficient module objects

Balanced tensor coequalizers give the tensorator, with coherence checked on their
presentation epimorphisms. Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-ordinary-monoidal)
-/

@[expose] public section
universe v u v' u'
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Bimod.monoidalCategory
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided]
  (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

end CategoryTheory.Mod.ResidueOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Use the same ambient braiding as the tensor-presentation and tensor-model interfaces.
attribute [local instance 20000] sheafBraidedCategory

/-- The ordinary integral pullback is strong monoidal, constructed from the ambient
inverse image and the coefficient-pullback isomorphism. -/
@[instance_reducible] noncomputable def residueExchangeOrdinaryPullMonoidal
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦integralCoeff ℓ E⟧.Monoidal :=
  residueOrdinaryUpperStarMonoidal (integralCoeff ℓ E) f

end AlgebraicGeometry.ProEtale.CondensedRing

section OrdinaryBraiding
open MonObj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
end CategoryTheory.Mod.ResidueOrdinary
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] sheafBraidedCategory
set_option maxHeartbeats 600000 in
-- Allow elaboration of the explicitly constructed module tensor comparisons.
@[instance_reducible] private noncomputable def ordinary_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.LaxBraided := by
  let G := (f)^*[Ab.{u + 1}]
  let : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  let : (Mod.mapModComap ρ).LaxBraided :=
    { toLaxMonoidal := inferInstance
      braided := Mod.ResidueOrdinary.mapModComap_braided ρ }
  let i := Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  let : (G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)).Monoidal :=
    Functor.Monoidal.transport i.symm
  let : NatTrans.IsMonoidal i.symm.hom :=
    { unit := by simp [Functor.Monoidal.transport_ε]
      tensor M N := by
        simp [Functor.Monoidal.transport_μ] }
  let h := Functor.LaxBraided.ofNatIso
    (G := G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)) i.symm
  exact
    { toLaxMonoidal := (residueOrdinaryUpperStarMonoidal Λ f).toLaxMonoidal
      braided := h.braided }

end AlgebraicGeometry.ProEtale.CondensedRing

end OrdinaryBraiding
