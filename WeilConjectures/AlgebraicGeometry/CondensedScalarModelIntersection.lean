/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
import WeilConjectures.AlgebraicGeometry.PointScalarRealizationAdjunction
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Comparing scalar models on intersecting images

Source: Hemo--Richarz--Scholbach, Theorem 4.13, geometric-value comparison
(blueprint: lem-pod-condensed-scalar-model-intersection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem scalar_model_restrict
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y T : Scheme.{u}} (f : Y ⟶ X) (g : T ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (e : (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X Y).obj P) :
    Nonempty ((CondensedRing.upperStar Λ.X (g ≫ f)).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X T).obj P) := by
  obtain ⟨a⟩ := condensed_scalarRealization_pullback Λ g
  exact ⟨(ComponentDerivedSquare.schemeComposition Λ f g).app K ≪≫
    (CondensedRing.upperStar Λ.X g).mapDerivedCategory.mapIso e ≪≫ a.app P⟩

/-- Scalar models on two scheme maps with intersecting images have isomorphic values.
No affine or covering hypothesis is needed for this comparison.

Source: HRS Lemma 4.1(1) and Theorem 4.13, finite-component reduction
(blueprint: lem-pod-condensed-scalar-model-intersection).

Proof: choose points of the two sources above a common image point. The fibre
product has a point above this pair. Take the algebraic closure of its residue
field and the induced geometric point of the fibre product. Pull both model
isomorphisms back to this point. Inverse-image composition, the fibre-product
square, and scalar-realization pullback identify the two scalar realizations.
The point scalar adjunction has invertible unit, hence is fully faithful; take
the preimage isomorphism in the chosen scalar derived category.
The intersection hypothesis excludes
empty source intersections; the zero coefficient ring causes no exception. -/
theorem scalar_models_agree_of_intersection
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X T S : Scheme.{u}} (f : T ⟶ X) (g : S ⟶ X)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (P Q : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (e : (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X T).obj P)
    (e' : (CondensedRing.upperStar Λ.X g).mapDerivedCategory.obj K ≅
      (condensedScalarRealization Λ.X S).obj Q)
    (h : (Set.range f ∩ Set.range g).Nonempty) : Nonempty (P ≅ Q) := by
  classical
  obtain ⟨x, ⟨t, ht⟩, ⟨s, hs⟩⟩ := h
  obtain ⟨v, _, _⟩ := Scheme.Pullback.exists_preimage_pullback t s (ht.trans hs.symm)
  let Ω := AlgebraicClosure ((pullback f g).residueField v)
  let η : Spec (.of Ω) ⟶ pullback f g :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f g).residueField v) Ω)) ≫
      (pullback f g).fromSpecResidueField v
  obtain ⟨a⟩ := scalar_model_restrict Λ f (η ≫ pullback.fst f g) K P e
  obtain ⟨b⟩ := scalar_model_restrict Λ g (η ≫ pullback.snd f g) K Q e'
  have hab : (η ≫ pullback.fst f g) ≫ f = (η ≫ pullback.snd f g) ≫ g := by
    simp only [Category.assoc, pullback.condition]
  let c : (condensedScalarRealization Λ.X (Spec (.of Ω))).obj P ≅
      (condensedScalarRealization Λ.X (Spec (.of Ω))).obj Q :=
    a.symm ≪≫ eqToIso (congrArg
      (fun k ↦ (CondensedRing.upperStar Λ.X k).mapDerivedCategory.obj K) hab) ≪≫ b
  obtain ⟨_, adj, hunit⟩ := point_scalar_realization_adjunction Λ Ω
  let := hunit
  exact ⟨adj.fullyFaithfulLOfIsIsoUnit.preimageIso c⟩


end AlgebraicGeometry.ProEtale
