/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-! # Tensor and pullback comparisons for normalized finite coefficients

Only left derived pullbacks and the native derived tensor bifunctors occur in the
comparison asserted here. No projection morphism or direct-image property is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

private def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (Functor.postcompose₂.obj F).obj T ≅ (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) :
    (Functor.postcompose₂.obj G).obj T ≅ (((Functor.whiskeringLeft₂ D).obj G).obj G).obj U :=
  (Functor.postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((Functor.whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((Functor.whiskeringLeft₂ D).mapIso e).app G).app U

private theorem comparisonCompatible_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {F' : D' ⥤ C'}
    {N : D ⥤ D'} {M : C ⥤ C'} {N' : D ⥤ D'} {M' : C ⥤ C'}
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    {T' : D' ⥤ D' ⥤ D'} {U' : C' ⥤ C' ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M) (e : N ≅ N') (d : M ≅ M')
    (t : (Functor.postcompose₂.obj F).obj T ⟶ (((Functor.whiskeringLeft₂ C).obj F).obj F).obj U)
    (t' : (Functor.postcompose₂.obj F').obj T' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj U')
    (m : (Functor.postcompose₂.obj M).obj U ≅ (((Functor.whiskeringLeft₂ C').obj M).obj M).obj U')
    (n : (Functor.postcompose₂.obj N).obj T ≅ (((Functor.whiskeringLeft₂ D').obj N).obj N).obj T')
    (h : Adjunction.ComparisonCompatible a t t' m n) :
    Adjunction.ComparisonCompatible
      (Functor.isoWhiskerRight e.symm F' ≪≫ a ≪≫ Functor.isoWhiskerLeft F d)
      t t' (tensorTransport U U' d m) (tensorTransport T T' e n) := by
  intro X Y
  have hh := h X Y
  dsimp [tensorTransport]
  rw [d.inv.naturality_assoc, reassoc_of% hh]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← F'.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have ht₁ := NatTrans.congr_app (t'.naturality (e.hom.app X)) (N'.obj Y)
  have ht₂ := (t'.app (N.obj X)).naturality (e.hom.app Y)
  dsimp at ht₁ ht₂
  rw [reassoc_of% ht₁, reassoc_of% ht₂]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [NatTrans.naturality_assoc]
  erw [(U'.map (d.hom.app (F.obj X))).naturality
    (a.hom.app Y ≫ d.hom.app (F.obj Y))]
  simp only [NatTrans.comp_app, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    NatTrans.comp_app, Category.assoc]
  simp only [Functor.map_comp]
  rfl

private theorem comparisonCompatible_congr
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N : D ⥤ D'} {M : C ⥤ C'}
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    {T' : D' ⥤ D' ⥤ D'} {U' : C' ⥤ C' ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M)
    {t s : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj U}
    {t' s' : (Functor.postcompose₂.obj F').obj T' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj U'}
    {m : (Functor.postcompose₂.obj M).obj U ≅
      (((Functor.whiskeringLeft₂ C').obj M).obj M).obj U'}
    {n : (Functor.postcompose₂.obj N).obj T ≅
      (((Functor.whiskeringLeft₂ D').obj N).obj N).obj T'}
    (ht : t = s) (ht' : t' = s') (h : Adjunction.ComparisonCompatible a t t' m n) :
    Adjunction.ComparisonCompatible a s s' m n := by
  subst s s'
  exact h

private theorem comparisonCompatible_of_tensorHom
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    {F : D ⥤ C} {F' : D' ⥤ C'} {N : D ⥤ D'} {M : C ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M)
    (t : (Functor.postcompose₂.obj F).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (t' : (Functor.postcompose₂.obj F').obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj (curriedTensor C'))
    (m : (Functor.postcompose₂.obj M).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ C').obj M).obj M).obj (curriedTensor C'))
    (n : (Functor.postcompose₂.obj N).obj (curriedTensor D) ≅
      (((Functor.whiskeringLeft₂ D').obj N).obj N).obj (curriedTensor D'))
    (h : ∀ X Y, M.map ((t.app X).app Y) ≫ (m.hom.app (F.obj X)).app (F.obj Y) =
      a.inv.app (X ⊗ Y) ≫ F'.map ((n.hom.app X).app Y) ≫
        (t'.app (N.obj X)).app (N.obj Y) ≫ (a.hom.app X ⊗ₘ a.hom.app Y)) :
    Adjunction.ComparisonCompatible a t t' m n := by
  intro X Y
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, curriedTensor_obj_map,
    Functor.comp_obj, MonoidalCategory.tensorHom_def, Category.assoc] using h X Y

section DerivedSquare

universe a b c d

variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F₁ : A ⥤ B) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : B ⥤ D) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : A ⥤ C) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : C ⥤ D) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
  (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]

private theorem derivedComparisonCompatible :
    Adjunction.ComparisonCompatible
      (Functor.leftDerivedFunctorCompNatIso F₁ F₂ G₁ G₂ τ)
      F₁.leftDerivedTensorComparison G₂.leftDerivedTensorComparison
      (asIso F₂.leftDerivedTensorComparison) (asIso G₁.leftDerivedTensorComparison) :=
  comparisonCompatible_of_tensorHom _ _ _ _ _
    (fun X Y ↦ Functor.map_leftDerivedTensorComparison_comp_eq_of_iso F₁ F₂ G₁ G₂ τ X Y)

end DerivedSquare

namespace CategoryTheory.Adjunction

/-- Tensor comparison data for a square of pullbacks. The tensor bifunctors are inferred
from the two specified pullback comparisons, preserving their native structure arguments.
Source: blueprint finite coefficient transport, tensor/pullback compatibility
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
structure TensorPullbackCompatibility
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : D ⥤ C} {F' : D' ⥤ C'} (N_D : D ⥤ D') (N_C : C ⥤ C')
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
    (φ : (Functor.postcompose₂.obj F).obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T_C)
    (φ' : (Functor.postcompose₂.obj F').obj T_D' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj T_C') where
  pullback : N_D ⋙ F' ≅ F ⋙ N_C
  tensorX : (Functor.postcompose₂.obj N_C).obj T_C ≅
    (((Functor.whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C'
  tensorY : (Functor.postcompose₂.obj N_D).obj T_D ≅
    (((Functor.whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D'
  compatible : ComparisonCompatible pullback φ φ' tensorX tensorY

/-- Tensor-compatible equivalences preserve and reflect canonical projection isomorphisms.
Source: the adjunction projection mate comparison and equivalence reflection
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
theorem TensorPullbackCompatibility.projection_isIso_iff_of_equivalences
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
    {N_D : D ⥤ D'} {N_C : C ⥤ C'} [N_D.IsEquivalence] [N_C.IsEquivalence]
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
    {φ : (Functor.postcompose₂.obj F).obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T_C}
    {φ' : (Functor.postcompose₂.obj F').obj T_D' ⟶
      (((Functor.whiskeringLeft₂ C').obj F').obj F').obj T_C'}
    (s : TensorPullbackCompatibility N_D N_C φ φ') (K : C) (M : D) :
    IsIso (((adj.rightAdjointProjectionMap φ).app K).app M) ↔
      IsIso (((adj'.rightAdjointProjectionMap φ').app (N_C.obj K)).app (N_D.obj M)) := by
  let α := s.pullback
  let m_C := s.tensorX
  let m_D := s.tensorY
  have H := s.compatible
  have (N : C) : IsIso ((mateEquiv adj adj' α.hom).app N) :=
    isIso_mateEquiv_app_of_isIso adj adj' α
      N_D.asEquivalence.toAdjunction N_C.asEquivalence.toAdjunction N
  constructor
  · intro h
    have := h
    exact isIso_rightAdjointProjectionMap_of_mateEquiv adj adj' H K M
  · intro h
    have := h
    have hs := map_rightAdjointProjectionMap_comp_mateEquiv adj adj' H K M
    have : IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app K).app M) ≫
        (mateEquiv adj adj' α.hom).app ((T_C.obj K).obj (F.obj M)) ≫
        G'.map ((m_C.hom.app K).app (F.obj M) ≫
          (T_C'.obj (N_C.obj K)).map (α.inv.app M))) := by
      rw [hs]
      infer_instance
    have : IsIso (N_D.map (((adj.rightAdjointProjectionMap φ).app K).app M)) :=
      IsIso.of_isIso_comp_right _
        ((mateEquiv adj adj' α.hom).app ((T_C.obj K).obj (F.obj M)) ≫
          G'.map ((m_C.hom.app K).app (F.obj M) ≫
            (T_C'.obj (N_C.obj K)).map (α.inv.app M)))
    exact isIso_of_reflects_iso _ N_D

/-- An adjunction with the two tensor bifunctors and its pullback tensor comparison.
The fields are the native constructions, bundled to retain their structure arguments.
Source: the canonical adjunction projection construction
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
structure ProjectionContext (C D : Type*) [Category* C] [Category* D] where
  pull : D ⥤ C
  push : C ⥤ D
  adj : pull ⊣ push
  tensorC : C ⥤ C ⥤ C
  tensorD : D ⥤ D ⥤ D
  comparison : (Functor.postcompose₂.obj pull).obj tensorD ⟶
    (((Functor.whiskeringLeft₂ C).obj pull).obj pull).obj tensorC

/-- The canonical projection associated to a bundled context.
Source: the adjunction projection construction
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
def ProjectionContext.projection
    {C D : Type*} [Category* C] [Category* D] (P : ProjectionContext C D)
    (K : C) (M : D) :=
  ((P.adj.rightAdjointProjectionMap P.comparison).app K).app M

/-- The mate comparison preserves and reflects invertibility in bundled contexts.
Source: the projection-mate comparison and reflection by equivalences
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
theorem ProjectionContext.projection_isIso_iff
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (P : ProjectionContext C D) (Q : ProjectionContext C' D')
    {N_D : D ⥤ D'} {N_C : C ⥤ C'} [N_D.IsEquivalence] [N_C.IsEquivalence]
    (s : TensorPullbackCompatibility N_D N_C P.comparison Q.comparison) (K : C) (M : D) :
    IsIso (P.projection K M) ↔ IsIso (Q.projection (N_C.obj K) (N_D.obj M)) :=
  s.projection_isIso_iff_of_equivalences P.adj Q.adj K M

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

/-- The native internal projection data, with resolving constructions behind one bundle.
Source: the internal derived geometric adjunction and tensor comparison
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
@[irreducible] def internalProjectionContext
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Adjunction.ProjectionContext
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj R X)))
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj R Y))) where
  pull := _
  push := _
  adj := CondensedRing.derivedUpperStarLowerStarAdjunction R p
  tensorC := _
  tensorD := _
  comparison := CondensedRing.leftDerivedUpperStarTensor R p

/-- The native ordinary projection data in the fixed scalar universe.
Source: the ordinary derived geometric adjunction and tensor comparison
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
@[irreducible] def ordinaryProjectionContext
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Adjunction.ProjectionContext
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) where
  pull := _
  push := _
  adj := ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  tensorC := _
  tensorD := _
  comparison := ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

open Scheme

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalCategory Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Functor.mapDerivedCategory
  DerivedCategory.Qh Functor.leftDerivedFunctorCompNatIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.mapDerivedCategoryCompIso
  CondensedRing.leftDerivedUpperStarTensor
  ProEtale.leftDerivedUpperStarTensorComparison Functor.leftDerivedTensorComparison

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

-- Cache the tensor hypotheses before instantiating the generic derived-square theorem.
private abbrev internalBraided (T : Scheme.{u}) :
    BraidedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T)) := Mod.braidedCategory

attribute [local instance] internalBraided

private abbrev internalClosed (T : Scheme.{u}) :
    MonoidalClosed (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T)) := Mod.monoidalClosed

attribute [local instance] internalClosed

private instance internalFlatResolution (T : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T)) :=
  Mod.hasFunctorialFlatResolution

/-- Finite internal-etale realization restricts to an equivalence for every ordered
Tor interval and commutes naturally with the specified unbounded total direct images
on all bounded-below etale inputs. The encodings are normalized section-action
encodings; thus the assertion applies to each choice of the equivalence in the node.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-ctf-finite-foundations/sk-prop-ctf-finite-proper/
sk-prop-ctf-finite-proper.proof.md, comparison paragraph;
Stacks 09AL, 09C2, 09A6; Bhatt--Scholze, Lemma 5.4.3
(blueprint: lem-sfb-finite-ctf-internal-etale-realization-all-char).

Proof:
1. The standing geometric hypotheses make T qcqs. Match the ordinary fixed-scalar
constructibility convention with the source's finite-stratification convention by resizing
cover indices; the etale boundedness conventions agree by isGE_iff and isLE_iff.
2. Apply the existing fixed-module bounded constructible descent theorem to the
constructible cohomology sheaves. Bounded-below derived Hom bijectivity gives full
faithfulness on the etale source subcategory.
3. The existing fixed-module Tor comparison preserves and reflects each interval.
4. encoding_constructibility and encoding_tensor_tor give the same two identifications
for every supplied normalized encoding E T. Lift the composite of site comparison and
its inverse encoding to the two full subcategories. The counit proves membership;
descent and the unit prove essential surjectivity. Its ambient functor is definitionally
the specified realization.
5. Reuse encodingDerivedPushforwardIso, the proved comparison of the separately specified
unbounded direct images. It derives the normalized sectionwise action comparison by
exact-equivalence transport through K-injective resolutions.
6. Apply the existing fixed-module bounded-below direct-image comparison, then use
rightDerivedFunctorPlusCompatibility and mapDerivedCategoryPlusCompatibility to view it
in the full unbounded derived categories.
7. None of these comparisons uses the characteristic of the ground field.
Conjugate step 5 by the inverse encodings and compose it with step 6. All factors are
natural isomorphisms. Zero rings, empty schemes and degenerate intervals need no exclusions.
-/
theorem finiteCtfInternalEtaleRealization_allChar
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, Encoding A T) :
    (∀ (T : Over (Spec (.of k)))
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (a b : ℤ), a ≤ b →
      ∃ e : ObjectProperty.FullSubcategory
        (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1} A) T.left K ∧
          Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ≌
        ObjectProperty.FullSubcategory
          (fun (K : DerivedCategory (Internal A T.left)) ↦
            constantModelBoundedConstructible (coefficient A) T.left K ∧
            _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K),
        Nonempty (e.functor ⋙ ObjectProperty.ι (fun (K : DerivedCategory (Internal A T.left)) ↦
            constantModelBoundedConstructible (coefficient A) T.left K ∧
              _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K) ≅
          ObjectProperty.ι (fun K ↦ Etale.DerivedCategory.isBoundedConstructible
              (ULift.{u + 1} A) T.left K ∧
            Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K) ⋙
              internalEtaleRealization A T.left (E T.left))) ∧
    (∀ (V T : Over (Spec (.of k)))
      [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
      [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
      (f : V ⟶ T) [QuasiCompact f.left] [QuasiSeparated f.left],
      Nonempty (DerivedCategory.Plus.ι ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f.left).rightDerivedFunctor ⋙
            internalEtaleRealization A T.left (E T.left) ≅
        DerivedCategory.Plus.ι ⋙ internalEtaleRealization A V.left (E V.left) ⋙
          CondensedRing.moduleObjectDerivedPushforward (coefficient A) f.left)) := by
  classical
  constructor
  · intro T _ _ _ a b hab
    have : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
    have : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
    let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T.left
    let e := (E T.left).fixedDerived
    let P : ObjectProperty (Etale.DerivedCategoryModule (ULift.{u + 1} A) T.left) :=
      fun K ↦ Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) T.left K ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K
    let Q : ObjectProperty (DerivedCategory (Internal A T.left)) := fun K ↦
      constantModelBoundedConstructible (coefficient A) T.left K ∧
        _root_.DerivedCategory.torAmplitudeIn (Internal A T.left) a b K
    have hb := (encoding_constructibility A T.left (E T.left)).2
    have ht := (encoding_tensor_tor A T.left (E T.left)).2.2
    have htC (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) T.left) :
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T.left a b K ↔
          _root_.DerivedCategory.torAmplitudeIn _ a b (C.mapDerivedCategory.obj K) :=
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.trans
        (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K).symm
    let F := P.ι ⋙ C.mapDerivedCategory
    have hplus (K : P.FullSubcategory) : DerivedCategory.TStructure.t.plus K.obj := by
      obtain ⟨c, d, _, hv⟩ := K.property.1.2
      exact ⟨c, (DerivedCategory.isGE_iff K.obj c).2 fun i hi ↦ hv i (Or.inl hi)⟩
    have : F.Full := ⟨fun {K L} f ↦ by
      obtain ⟨g, hg⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).2 f
      exact ⟨ObjectProperty.homMk g, hg⟩⟩
    have : F.Faithful := ⟨fun {K L} f g h ↦ ObjectProperty.hom_ext _
      ((bijective_comparisonUpperStar_mapDerivedCategory_map
        K.obj L.obj (hplus L)).1 h)⟩
    let R := Q.lift (F ⋙ e.inverse) (fun K ↦ by
      have hbc := DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        ((etaleBC_iff A T.left _).mp K.property.1)
      have htor := (htC K.obj).mp K.property.2
      have he := e.counitIso.app (C.mapDerivedCategory.obj K.obj)
      exact ⟨(hb _).mpr ((ordinaryBC_iff A T.left _).mpr
        ((DerivedCategory.boundedConstructible _ _).prop_of_iso he.symm
          hbc)),
        (ht _ a b hab).mpr ((_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso
          he.symm htor)⟩)
    have : R.Full := by dsimp [R]; infer_instance
    have : R.Faithful := by dsimp [R]; infer_instance
    have : R.EssSurj := by
      constructor
      intro K
      obtain ⟨L, hL, ⟨j⟩⟩ := (ordinaryBC_iff A T.left _).mp ((hb K.obj).mp K.property.1)
      have htor := (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso j.symm
        ((ht K.obj a b hab).mp K.property.2)
      let L' : P.FullSubcategory :=
        ⟨L, (etaleBC_iff A T.left L).mpr hL, (htC L).mpr htor⟩
      exact ⟨L', ⟨Q.isoMk (e.inverse.mapIso j ≪≫ (e.unitIso.app K.obj).symm)⟩⟩
    have : R.IsEquivalence := {}
    exact ⟨R.asEquivalence, ⟨Iso.refl _⟩⟩
  · intro V T _ _ _ _ _ _ f _ _
    let C := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let g := Etale.lowerStar C f.left
    let h := lowerStar C f.left
    let v := comparisonUpperStar C V.left
    let t := comparisonUpperStar C T.left
    let eV := (E V.left).fixedDerived
    let eT := (E T.left).fixedDerived
    obtain ⟨c⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar C f.left
    let j : DerivedCategory.Plus.ι ⋙ g.rightDerivedFunctor ⋙ t.mapDerivedCategory ≅
        DerivedCategory.Plus.ι ⋙ v.mapDerivedCategory ⋙ h.rightDerivedFunctor :=
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight g.rightDerivedFunctorPlusCompatibility.symm
        t.mapDerivedCategory ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft g.rightDerivedFunctorPlus
        t.mapDerivedCategoryPlusCompatibility.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c DerivedCategory.Plus.ι ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft v.mapDerivedCategoryPlus h.rightDerivedFunctorPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight v.mapDerivedCategoryPlusCompatibility h.rightDerivedFunctor ≪≫
      Functor.associator _ _ _
    let d := encodingDerivedPushforwardIso A f.left (E T.left) (E V.left)
    let di := Iso.inverseCompIso (G := eV)
      (Iso.isoCompInverse (H := eT) d ≪≫ Functor.associator _ _ _)
    exact ⟨Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight j eT.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.isoWhiskerLeft v.mapDerivedCategory di.symm)⟩

private instance internalGoodTensorLeft (T : Scheme.{u})
    (P Q S : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T))) : GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  infer_instance

private instance internalGoodTensorRight (T : Scheme.{u})
    (P Q S : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T))) : GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  infer_instance

private instance internalTensorFour (T : Scheme.{u})
    (P Q S W : GradedObject ℤ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T))) : GradedObject.HasTensor₄ObjExt P Q S W := by
  infer_instance

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
/-- The normalized encoding identifies derived tensors compatibly with geometric pullback.

Source: blueprint proper-base-change-finite, transport paragraph and clause (3);
lem-sfb-finite-coefficient-projection-encoding, proof steps 1--2; Stacks 03D3,
08BJ and 08FZ. (blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding).

Proof: restriction along the inverse coefficient isomorphism identifies balanced tensors:
the two balancing relations coincide after applying the ring isomorphism. Compose with the
section-action comparison and restriction to constant scalar sections. The normalization of
Encoding sends each constant scalar to that same scalar; therefore all three comparisons
send a pure tensor to the same pure tensor. They are natural isomorphisms, compatible with
associators and unitors. On sections over a fibre product the direct-image encoding is the
identity. Conjugate its adjunction to obtain the pullback comparison. Before deriving, the
two composites expressing compatibility with the pullback tensorator agree on pure tensors,
hence agree by the balanced tensor universal property. Apply the comparisons termwise to
flat-term K-flat resolutions and use signed direct-sum totalization. Exact monoidal
equivalences and their inverses preserve flatness and K-flatness. The universal property of
the left derived bifunctor extends the tensor isomorphisms to all derived objects, and the
universal property of derived pullback extends the pullback isomorphism. The underived
pure-tensor equality gives ComparisonCompatible for the published derived comparisons.
This uses no properness, boundedness or constructibility. For an empty scheme or the zero
coefficient ring the same tensor universal properties apply, including the zero tensor. -/
theorem finiteCoefficientTensorPullbackEncoding
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Nonempty (Adjunction.TensorPullbackCompatibility
      (coefficientEncoding A e Y (E Y)) (coefficientEncoding A e X (E X))
      (internalProjectionContext R p).comparison
      (ordinaryProjectionContext (ULift.{u + 1} A) p).comparison) := by
  let (T : Scheme.{u}) : ((E T).ordinary.trans (E T).fixed).functor.Additive :=
    inferInstanceAs ((E T).ordinary.functor ⋙ (E T).fixed.functor).Additive
  let NX := coefficientHeartEncoding A e X (E X)
  let NY := coefficientHeartEncoding A e Y (E Y)
  obtain ⟨mX, mY, hm⟩ := coefficientHeartPullIso_monoidal A e p (E X) (E Y)
  let := mX
  let := mY
  let F := CondensedRing.upperStar R p
  let G := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p
  have : F.PreservesFlat := CondensedRing.upperStar_preservesFlat R p
  have : NX.PreservesFlat := Functor.preservesFlat_of_isEquivalence NX
  have : NY.PreservesFlat := Functor.preservesFlat_of_isEquivalence NY
  let τ : NY ⋙ G ≅ F ⋙ NX := coefficientHeartPullIso A e p (E X) (E Y)
  have : NatTrans.IsMonoidal τ.hom := hm
  let α := Functor.leftDerivedFunctorCompNatIso F NX NY G τ
  let d : NX.leftDerivedFunctor ≅ coefficientEncoding A e X (E X) :=
    NX.leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap e.inv.hom X))
      ((E X).ordinary.functor ⋙ (E X).fixed.functor)
  let c : NY.leftDerivedFunctor ≅ coefficientEncoding A e Y (E Y) :=
    NY.leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap e.inv.hom Y))
      ((E Y).ordinary.functor ⋙ (E Y).fixed.functor)
  let tx := asIso NX.leftDerivedTensorComparison
  let ty := asIso NY.leftDerivedTensorComparison
  have h : Adjunction.ComparisonCompatible α F.leftDerivedTensorComparison
      G.leftDerivedTensorComparison tx ty := derivedComparisonCompatible F NX NY G τ
  have hn := comparisonCompatible_congr α
    (CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison R p).symm
    (ProEtale.leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).symm h
  have ht := comparisonCompatible_transport α c d
    (CondensedRing.leftDerivedUpperStarTensor R p)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)
    tx ty hn
  unfold internalProjectionContext ordinaryProjectionContext
  exact ⟨⟨_, _, _, ht⟩⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
