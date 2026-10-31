/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData
import all WeilConjectures.Algebra.Homology.ScalarHomTensorComparison

/-! # Chain-level balancing for normalized reduction

Source: Stacks 03EL and 07A4; blueprint integral direct-image proof (3)
(blueprint: lem-sp-reduction-strict-tensor-balancing-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory SheafOfModules
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The chain comparison extending a supplied ordinary balancing family.
Source: Stacks 03EL and 07A4.
(blueprint: lem-sp-reduction-strict-tensor-balancing-chain).

Proof plan: define the map on each signed total summand by the inverse ordinary
balancing isomorphism.  The coproduct universal property assembles these maps
into a chain isomorphism.  The two components of the differential carry the
same Koszul sign on both sides, so the summand maps commute with the total
differential.  The displayed summand equation follows by precomposing with the
canonical tensor-summand coproduct injection.  This construction only needs the
ordinary family, its naturality, and the supplied right adjoint (which ensures
coproduct preservation). It is independent of the sheafified pure-generator proof. -/
theorem sp_reduction_strict_tensor_chain_exists
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    (ordinary : ∀ M N : spIntegralSectionModules l E T,
      (spMonoidalOrdinary l E T D r).obj
          (ordinaryTensor.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (spIntegralSectionRing l E T) M N) ≅
        ordinaryTensor.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (spMonoidalSystemRing l E T)
          ((spMonoidalOrdinary l E T D r).obj M)
          ((spMonoidalOrdinary l E T D r).obj N))
    (hnatural : ∀ {M M' N N' : spIntegralSectionModules l E T}
      (f : M ⟶ M') (g : N ⟶ N'),
      (spMonoidalOrdinary l E T D r).map
          (ordinaryTensorHom.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
            (spIntegralSectionRing l E T) f g) ≫ (ordinary M' N').hom =
        (ordinary M N).hom ≫
          (ordinaryTensorHom.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (spMonoidalSystemRing l E T)
            ((spMonoidalOrdinary l E T D r).map f)
            ((spMonoidalOrdinary l E T D r).map g)))
    (V : spMonoidalSystems l E T ⥤ spIntegralSectionModules l E T)
    (adj : spMonoidalOrdinary l E T D r ⊣ V) :
    ∃ (chain :
      (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).prod
        ((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ))) ⋙
          spMonoidalSystemTotal l E T ≅
      spMonoidalIntegralTotal l E T ⋙
        (spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)),
      ∀ (P Q : CochainComplex (spIntegralSectionModules l E T) ℤ)
        (p q k : ℤ) (h : p + q = k),
        tensorSummand.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T))
            (spMonoidalSystemRing l E T)
            (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj P)
            (((spMonoidalOrdinary l E T D r).mapHomologicalComplex (.up ℤ)).obj Q)
            p q k h ≫ (chain.hom.app (P,Q)).f k =
          (ordinary (P.X p) (Q.X q)).inv ≫ (spMonoidalOrdinary l E T D r).map
            (tensorSummand.{u + 1, u, u + 1}
              (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) P Q p q k h) := by
  classical
  let J := Scheme.ProEt.topology T
  let K := coefficientSequenceTopology J
  let R := spIntegralSectionRing l E T
  let S := spMonoidalSystemRing l E T
  let A := spIntegralSectionModules l E T
  let B := spMonoidalSystems l E T
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    SemilinearSections.abelianSheafify.{u + 1, u, u + 1} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    SemilinearSections.locallyBijective.{u + 1, u, u + 1} J
  let : HasSheafify K AddCommGrpCat.{u + 1} :=
    SemilinearSections.abelianSheafify.{u + 1, u, u + 1} K
  let : K.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    SemilinearSections.locallyBijective.{u + 1, u, u + 1} K
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  have (X : A) : (tensorLeft X).Additive := tensorLeft_additive_independent R X
  have (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  have (X : B) : (tensorLeft X).Additive := tensorLeft_additive_independent S X
  have (X : B) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let : MonoidalPreadditive B :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let L := spMonoidalOrdinary l E T D r
  let F := L.mapHomologicalComplex (.up ℤ)
  have he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (ordinary X' Y').hom =
        (ordinary X Y).hom ≫ (L.map f ⊗ₘ L.map g) := by
    exact hnatural
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal L ordinary he P Q) :=
    tensorPullbackTotal_isIso L ordinary he V adj P Q
  let chain : (F.prod F) ⋙ spMonoidalSystemTotal l E T ≅
      spMonoidalIntegralTotal l E T ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal L ordinary he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, Functor.comp_map, Functor.prod_map]
        simp only [spMonoidalSystemTotal, spMonoidalIntegralTotal, totalTensor,
          coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom,
          CategoryTheory.ScalarHomTensor.tensorMap_factor]
        exact CategoryTheory.ScalarHomTensor.tensorPullbackTotal_naturality
          L ordinary he f.1 f.2)
  refine ⟨chain, ?_⟩
  intro P Q p q k h
  change _ ≫ tensorPullbackTotalComponent L ordinary P Q k = _
  exact HomologicalComplex.ι_mapBifunctorDesc _ p q h

end AlgebraicGeometry.ProEtale
