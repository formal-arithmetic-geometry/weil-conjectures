/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Component.ComponentPullbackFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ResidueOrdinary.IntegralResidueOrdinaryMonoidal

/-! # Derived symmetry of component module pullback

Source: Hemo--Richarz--Scholbach, Construction (4.1) and Proposition 4.3(3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory

private theorem mapModComap_braiding
    {C D : Type*} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [IsGrothendieckAbelian.{v₁} C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian D] [IsGrothendieckAbelian.{v₂} D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
    {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
    {G : C ⥤ D} [G.Braided] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
    [PreservesColimitsOfShape WalkingParallelPair (Mod.mapModComap ρ)]
    (M N : Mod C R) :
    let := Mod.ResidueOrdinary.mapModComapMonoidal ρ
    Functor.LaxMonoidal.μ (Mod.mapModComap ρ) M N ≫
        (Mod.mapModComap ρ).map (β_ M N).hom =
      (β_ ((Mod.mapModComap ρ).obj M) ((Mod.mapModComap ρ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (Mod.mapModComap ρ) N M := by
  let := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ
    ((Mod.mapModComap ρ).obj M) ((Mod.mapModComap ρ).obj N))]
  change Mod.tensorObjπ _ _ ≫
      (Mod.ResidueOrdinary.tensorComparison ρ M N).inv.hom ≫
      G.map (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫
      (β_ ((Mod.mapModComap ρ).obj M) ((Mod.mapModComap ρ).obj N)).hom.hom ≫
      (Mod.ResidueOrdinary.tensorComparison ρ N M).inv.hom
  erw [reassoc_of% Mod.ResidueOrdinary.tensorComparison_inv_π, ← G.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, G.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Mod.ResidueOrdinary.tensorComparison_inv_π]
  rfl

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]

/-- Exact component pullback preserves the ordinary Koszul derived symmetry.
Source: Hemo--Richarz--Scholbach, Construction (4.1), Proposition 4.3(3);
Stacks Project, Tags 06YY and 0FPT
(blueprint: lem-zl-component-derived-symmetry).

Proof: the abelian inverse image is exact and strong symmetric monoidal. Its module
pullback, followed by restriction along the coefficient isomorphism, is therefore exact
and strong symmetric monoidal for ordinary balanced tensors. On flat-term K-flat
complexes apply this tensor comparison to each bidegree summand of the total tensor.
The balancing relations make the comparison invertible, and the comparison commutes
with the signed total differential. Pullback preserves K-flat complexes and flat terms,
so localization gives a strong tensor structure on the fixed termwise derived functor.
Associativity and unit equations descend from their ordinary counterparts. On the
summand of bidegree (p,q), both braiding composites interchange the two factors with
sign (-1)^(pq); hence they agree. K-flat descent extends this equation to all objects.
The zero coefficient ring and empty scheme satisfy the same formulas. -/
theorem component_derived_symmetry
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T)) :
    componentSymmetric Λ.X T α := by
  classical
  let G := componentInverse T
  let R := profiniteCoefficient Λ.X (affineComponentSpace T)
  let ρ := α.inv.hom
  let F := componentModules Λ.X T α
  let adj : G ⊣ (componentTests T).sheafPushforwardContinuous Ab.{u + 1}
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T) :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentTests T) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)
  let := adj.rightAdjointLaxMonoidal
  let : (G.mapMod R).IsLeftAdjoint := (adj.mapModAdjunction R).isLeftAdjoint
  let : F.IsLeftAdjoint := inferInstanceAs
    (G.mapMod R ⋙ Mod.comap ρ).IsLeftAdjoint
  let m : F.Monoidal :=
    Mod.ResidueOrdinary.mapModComapMonoidal (G := G) (R := R) ρ
  let : F.LaxMonoidal := m.toLaxMonoidal
  let : F.OplaxMonoidal := m.toOplaxMonoidal
  let : F.PreservesFlat := component_pullback_preservesFlat Λ T α
  have hb (M N : Mod
      (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      R) :
      Functor.LaxMonoidal.μ F M N ≫ F.map (β_ M N).hom =
        (β_ (F.obj M) (F.obj N)).hom ≫ Functor.LaxMonoidal.μ F N M := by
    exact mapModComap_braiding (G := G) (R := R) ρ M N
  have hδ (M N : Mod
      (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T)) Ab.{u + 1})
      R) :
      F.map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ F N M =
        Functor.OplaxMonoidal.δ F M N ≫ (β_ (F.obj M) (F.obj N)).hom := by
    rw [← cancel_epi (Functor.LaxMonoidal.μ F M N)]
    rw [← Category.assoc, hb, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id, Functor.Monoidal.μ_δ_assoc]
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      Ab.{u + 1}) R)
  let := DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
  change Nonempty F.mapDerivedCategory.Braided
  let b := F.leftDerivedFunctorBraided hδ
  let := b
  let : F.leftDerivedFunctor.Monoidal := b.toMonoidal
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  let := Functor.Monoidal.transport e
  let : NatTrans.IsMonoidal e.hom :=
    Functor.Monoidal.natTransIsMonoidal_of_transport e
  exact ⟨{ braided := (Functor.LaxBraided.ofNatIso e).braided }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
