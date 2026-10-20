/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalRightCechModels
public import Sheaf.Paper.CechCupProduct
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential

/-! # External Alexander--Whitney components
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-component).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- The tuple formula for a single natural-index external cochain map.
Source: Stacks Project, Tags 0BED and 07MB.
(blueprint: lem-sc-picard-external-cech-cup-component). -/
def IsPicardExternalCechCupComponent
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)) : Prop :=
  ∀ (p q : ℕ) (a : ((picardCechFunctor f U).obj F).X p)
        (b : ((picardCechFunctor g V).obj G).X q) (y : Fin (p + q + 1) → ι × κ),
        TopCat.Presheaf.cechComplexFunctorXAddEquiv
          (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
            pullback.snd f g ⁻¹ᵁ V ij.2)
          (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
          (p + q) (c.f (p + q)
            (HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
              ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
                (ComplexShape.up ℕ) p q (p + q) rfl (a ⊗ₜ[k] b))) y =
          tmulSection
            (((fun (Q : X.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.fst f g ⁻¹ᵁ Q) (s : Γ(F, Q)) ↦
              ((tensorPullback (pullback.fst f g)).obj F).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.fst f g))).unit.app F).val.app (op Q) s))
              (⨅ l, U (y (cupFront p q l)).1) _
              (by
                intro x hx
                change (pullback.fst f g).base x ∈ ⨅ l, U (y (cupFront p q l)).1
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupFront p q l) hx).1)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv U (scalarPresheaf f F) p a
                (fun l ↦ (y (cupFront p q l)).1))))
            (((fun (Q : Y.Opens) (W : (Limits.pullback f g).Opens)
                (h : W ≤ pullback.snd f g ⁻¹ᵁ Q) (s : Γ(G, Q)) ↦
              ((tensorPullback (pullback.snd f g)).obj G).presheaf.map (homOfLE h).op
                (((Classical.choose (exists_tensorPullbackAdjunction
                  (pullback.snd f g))).unit.app G).val.app (op Q) s))
              (⨅ l, V (y (cupBack p q l)).2) _
              (by
                intro x hx
                change (pullback.snd f g).base x ∈ ⨅ l, V (y (cupBack p q l)).2
                rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
                intro l
                exact (iInf_le (fun j ↦ pullback.fst f g ⁻¹ᵁ U (y j).1 ⊓
                  pullback.snd f g ⁻¹ᵁ V (y j).2) (cupBack p q l) hx).2)
              (TopCat.Presheaf.cechComplexFunctorXAddEquiv V (scalarPresheaf g G) q b
                (fun l ↦ (y (cupBack p q l)).2))))

/-- Existence of a single external cup cochain map, without coefficient naturality.
Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech;
Cohomology, Tag 07MB.
(blueprint: lem-sc-picard-external-cech-cup-component).
Proof: Pull front and back face sections along the canonical adjunction units,
restrict to the common product intersection, and tensor. Both structure maps are
over Spec k, so the resulting pairing is k-bilinear. Use the tensor universal
property and the product universal property to give a map on each (p,q) summand,
then the coproduct universal property gives the map in each total degree.
Expand the alternating restriction differential. The front omitted vertices
produce d(a) cup b, the back vertices produce (-1)^p a cup d(b), and the two
shared-vertex terms cancel. Restriction composition and tensor-section restriction
compatibility identify these terms. This gives the cochain-map equation in adjacent
degrees; in all other degrees both differentials are zero. The universal-property
inclusion equations give the claimed coordinates. Empty covers yield empty
products, and zero coefficients yield zero pairings, so no cover hypotheses enter. -/
theorem picardExternalCechCupComponent_exists
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules) :
    ∃ c : HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ) ⟶
      (picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G),
      IsPicardExternalCechCupComponent f g U V F G c := by
  classical
  choose l hl using (fun p q ↦ picardExternalCechCupBidegree_exists f g U V F G p q)
  let c := CochainComplex.ofHom (picardExternalCechCupDegreeMaps f g U V F G l)
    (picardExternalCechCupDegreeMaps_comm f g U V F G l hl)
  refine ⟨c, ?_⟩
  intro p q a b y
  have he := ConcreteCategory.congr_hom
    (picardExternalCechCupDegreeMaps_ι f g U V F G l p q) (a ⊗ₜ[k] b)
  have hc := hl p q a b y
  apply Eq.trans _ hc
  exact congrArg (fun z ↦ TopCat.Presheaf.cechComplexFunctorXAddEquiv
    (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
      pullback.snd f g ⁻¹ᵁ V ij.2)
    (scalarPresheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (p + q) z y) he


end
end AlgebraicGeometry.Scheme.Modules
