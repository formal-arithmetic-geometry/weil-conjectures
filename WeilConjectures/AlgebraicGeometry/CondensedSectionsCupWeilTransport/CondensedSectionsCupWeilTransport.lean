/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsCupWeilTransportDefs
import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsGeometricLaws
import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsScalarLaws
import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedDegreeZeroLineTrivialization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit

/-! Frobenius transport of condensed sections, cups and coefficient lines.

The original native statement is assembled from its geometric and scalar components.
Source: the cup/sections sub-step of `sk-thm-frobenius` in blueprint latest.
(blueprint: lem-pod-condensed-sections-cup-weil-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance 30000] CategoryTheory.Functor.monObjObj
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport

private theorem inducedArrowData_intertwining
    {A : Type u} {B : Type v} [Category A] [Category B]
    {PT : A ⥤ A} {PS : B ⥤ B} (H : A ⥤ B)
    (e : H ⋙ PS ⟶ PT ⋙ H) [IsIso e] {X Y : A}
    (f : X ⟶ Y) (φX : PT.obj X ≅ X) (φY : PT.obj Y ≅ Y)
    (hf : IsIntertwining PT f φX φY) :
    IsIntertwining PS (H.map f) (inducedArrowData H e φX)
      (inducedArrowData H e φY) := by
  change (e.app X ≫ H.map φX.hom) ≫ H.map f =
    PS.map (H.map f) ≫ e.app Y ≫ H.map φY.hom
  rw [Category.assoc, ← H.map_comp, hf, H.map_comp]
  have hn : PS.map (H.map f) ≫ e.app Y = e.app X ≫ H.map (PT.map f) :=
    e.naturality f
  rw [← Category.assoc, ← hn, Category.assoc]

private theorem inducedCompactData_intertwining
    {A : Type u} {B : Type v} [Category A] [Category B]
    {PT : A ⥤ A} {PS : B ⥤ B} (F₀ F₁ : A ⥤ B)
    (e : F₀ ⋙ PS ⟶ PT ⋙ F₁) [IsIso e]
    {X Y : A} (f : X ⟶ Y)
    (φX : PT.obj X ≅ X) (φY : PT.obj Y ≅ Y)
    (τX : F₁.obj X ≅ F₀.obj X) (τY : F₁.obj Y ≅ F₀.obj Y)
    (hτ : F₁.map f ≫ τY.hom = τX.hom ≫ F₀.map f)
    (hf : IsIntertwining PT f φX φY) :
    IsIntertwining PS (F₀.map f) (inducedCompactData F₀ F₁ e φX ≪≫ τX)
      (inducedCompactData F₀ F₁ e φY ≪≫ τY) := by
  change ((e.app X ≫ F₁.map φX.hom) ≫ τX.hom) ≫ F₀.map f =
    PS.map (F₀.map f) ≫ ((e.app Y ≫ F₁.map φY.hom) ≫ τY.hom)
  have hn : PS.map (F₀.map f) ≫ e.app Y = e.app X ≫ F₁.map (PT.map f) :=
    e.naturality f
  simp only [Category.assoc]
  rw [← hτ, ← Category.assoc (F₁.map φX.hom), ← F₁.map_comp, hf, F₁.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]

private theorem pointOperator_intertwining
    {A : Type u} {B : Type v} [Category A] [Category B]
    (Γ : A ⥤ B) {P : A ⥤ A} (rho : 𝟭 A ≅ P) {X Y : A}
    (f : X ⟶ Y) (φX : P.obj X ≅ X) (φY : P.obj Y ≅ Y)
    (hf : IsIntertwining P f φX φY) :
    (pointOperator Γ rho φX).hom ≫ Γ.map f =
      Γ.map f ≫ (pointOperator Γ rho φY).hom := by
  change Γ.map ((rho.app X).hom ≫ φX.hom) ≫ Γ.map f =
    Γ.map f ≫ Γ.map ((rho.app Y).hom ≫ φY.hom)
  rw [← Γ.map_comp, ← Γ.map_comp]
  apply congrArg Γ.map
  have hr : f ≫ (rho.app Y).hom = (rho.app X).hom ≫ P.map f :=
    rho.hom.naturality f
  rw [Category.assoc, hf, ← Category.assoc, ← hr, Category.assoc]

private theorem evaluatedTensorIntertwining_of_tensor_compatibility
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (Γ : A ⥤ B) {P : A ⥤ A} [P.Monoidal] (rho : 𝟭 A ≅ P)
    (mu : ∀ X Y : A, Γ.obj X ⊗ Γ.obj Y ⟶ Γ.obj (X ⊗ Y))
    (hmu : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      (Γ.map f ⊗ₘ Γ.map g) ≫ mu X' Y' = mu X Y ≫ Γ.map (f ⊗ₘ g))
    {X Y Z : A} (f : X ⊗ Y ⟶ Z)
    (φX : P.obj X ≅ X) (φY : P.obj Y ≅ Y) (φZ : P.obj Z ≅ Z)
    (hrho : (rho.app (X ⊗ Y)).hom ≫ (Functor.Monoidal.μIso P X Y).inv =
      (rho.app X).hom ⊗ₘ (rho.app Y).hom)
    (hf : IsIntertwining P f (inducedTensorData P φX φY) φZ) :
    EvaluatedTensorIntertwining Γ rho mu f φX φY φZ := by
  have ht : (pointOperator Γ rho (inducedTensorData P φX φY)).hom =
      Γ.map (((rho.app X).hom ≫ φX.hom) ⊗ₘ ((rho.app Y).hom ≫ φY.hom)) := by
    change Γ.map ((rho.app (X ⊗ Y)).hom ≫
      ((Functor.Monoidal.μIso P X Y).inv ≫ (φX.hom ⊗ₘ φY.hom))) = _
    rw [← Category.assoc, hrho, tensorHom_comp_tensorHom]
  have hnat := pointOperator_intertwining Γ rho f (inducedTensorData P φX φY) φZ hf
  change (Γ.map ((rho.app X).hom ≫ φX.hom) ⊗ₘ
    Γ.map ((rho.app Y).hom ≫ φY.hom)) ≫ mu X Y ≫ Γ.map f = _
  rw [← Category.assoc, hmu, Category.assoc, ← ht]
  simpa only [Category.assoc, Functor.id_obj] using
    congrArg (fun t ↦ mu X Y ≫ t) hnat

private theorem conjugatedTensor_naturality
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (Γ S : A ⥤ B) [S.LaxMonoidal] (eta : Γ ≅ S)
    {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y') :
    (Γ.map f ⊗ₘ Γ.map g) ≫
        (((eta.app X').hom ⊗ₘ (eta.app Y').hom) ≫
          Functor.LaxMonoidal.μ S X' Y' ≫ (eta.app (X' ⊗ Y')).inv) =
      (((eta.app X).hom ⊗ₘ (eta.app Y).hom) ≫
        Functor.LaxMonoidal.μ S X Y ≫ (eta.app (X ⊗ Y)).inv) ≫ Γ.map (f ⊗ₘ g) := by
  have hf : Γ.map f ≫ (eta.app X').hom = (eta.app X).hom ≫ S.map f :=
    eta.hom.naturality f
  have hg : Γ.map g ≫ (eta.app Y').hom = (eta.app Y).hom ≫ S.map g :=
    eta.hom.naturality g
  have hi : S.map (f ⊗ₘ g) ≫ (eta.app (X' ⊗ Y')).inv =
      (eta.app (X ⊗ Y)).inv ≫ Γ.map (f ⊗ₘ g) := eta.inv.naturality _
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, hf, hg, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, hi]

private theorem laxTensor_unit_isIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (S : A ⥤ B) [S.LaxMonoidal] [IsIso (Functor.LaxMonoidal.ε S)] (X : A) :
    IsIso (Functor.LaxMonoidal.μ S X (𝟙_ A)) := by
  have h : Functor.LaxMonoidal.μ S X (𝟙_ A) =
      inv (S.obj X ◁ Functor.LaxMonoidal.ε S) ≫
        (ρ_ (S.obj X)).hom ≫ S.map (ρ_ X).inv := by
    apply (cancel_epi (S.obj X ◁ Functor.LaxMonoidal.ε S)).1
    apply (cancel_mono (S.map (ρ_ X).hom)).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← S.map_comp,
      Iso.inv_hom_id, S.map_id, Category.comp_id]
    exact (Functor.LaxMonoidal.right_unitality S X).symm
  rw [h]
  infer_instance

private theorem laxTensor_line_isIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [MonoidalCategory A] [MonoidalCategory B]
    (S : A ⥤ B) [S.LaxMonoidal] [IsIso (Functor.LaxMonoidal.ε S)]
    (X L : A) (hL : Nonempty (L ≅ 𝟙_ A)) :
    IsIso (Functor.LaxMonoidal.μ S X L) := by
  obtain ⟨e⟩ := hL
  have := laxTensor_unit_isIso S X
  have h : Functor.LaxMonoidal.μ S X L =
      S.obj X ◁ S.map e.hom ≫ Functor.LaxMonoidal.μ S X (𝟙_ A) ≫
        S.map (X ◁ e.inv) := by
    apply (cancel_mono (S.map (X ◁ e.hom))).1
    simp only [Category.assoc, ← S.map_comp, ← MonoidalCategory.whiskerLeft_comp,
      e.inv_hom_id, MonoidalCategory.whiskerLeft_id, S.map_id, Category.comp_id]
    exact (Functor.LaxMonoidal.μ_natural_right S X e.hom).symm
  rw [h]
  infer_instance

private theorem coefficientUnitTransport_eq_id
    {R : Type w} [CommRing R] {V : ModuleCat.{w} R}
    (unitMap : ModuleCat.of R R ⟶ V) [IsIso unitMap]
    (action : V ⟶ V) (haction : action = 𝟙 V) :
    coefficientUnitTransport unitMap action = 𝟙 _ := by
  simp only [coefficientUnitTransport, haction, Category.id_comp, IsIso.hom_inv_id]

private theorem tensorIso_unit_hom_eq
    {A : Type u} [Category A] [MonoidalCategory A]
    (P : A ⥤ A) [P.Monoidal] (rho : 𝟭 A ≅ P)
    (hrho : ∀ X Y : A, (rho.app (X ⊗ Y)).hom ≫
        (Functor.Monoidal.μIso P X Y).inv =
      (rho.app X).hom ⊗ₘ (rho.app Y).hom) :
    (rho.app (𝟙_ A)).hom = Functor.LaxMonoidal.ε P := by
  let U := 𝟙_ A
  let u := (rho.app U).hom
  let e := Functor.LaxMonoidal.ε P
  have ht : (rho.app (U ⊗ U)).hom =
      (u ⊗ₘ u) ≫ Functor.LaxMonoidal.μ P U U := by
    have h := congrArg (fun f ↦ f ≫ (Functor.Monoidal.μIso P U U).hom) (hrho U U)
    simpa only [← Functor.Monoidal.μIso_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using h
  have hn : (ρ_ U).hom ≫ u =
      (rho.app (U ⊗ U)).hom ≫ P.map (ρ_ U).hom := rho.hom.naturality _
  have hten : (u ⊗ₘ e) = (u ⊗ₘ u) := by
    apply (cancel_mono (Functor.LaxMonoidal.μ P U U ≫ P.map (ρ_ U).hom)).1
    calc
      (u ⊗ₘ e) ≫ (Functor.LaxMonoidal.μ P U U ≫ P.map (ρ_ U).hom) =
          (u ▷ U) ≫ (P.obj U ◁ e) ≫
            Functor.LaxMonoidal.μ P U U ≫ P.map (ρ_ U).hom := by
        rw [MonoidalCategory.tensorHom_def, Category.assoc]
      _ = (u ▷ U) ≫ (ρ_ (P.obj U)).hom := by
        rw [← Functor.LaxMonoidal.right_unitality]
      _ = (ρ_ U).hom ≫ u := rightUnitor_naturality u
      _ = (u ⊗ₘ u) ≫ (Functor.LaxMonoidal.μ P U U ≫ P.map (ρ_ U).hom) := by
        rw [hn, ht, Category.assoc]
  have hleft : (𝟙 U ⊗ₘ e) = (𝟙 U ⊗ₘ u) := by
    have h := congrArg (fun f ↦ f ≫ ((rho.app U).inv ⊗ₘ 𝟙 (P.obj U))) hten
    simpa only [tensorHom_comp_tensorHom, u, e, U, Functor.id_obj, Iso.hom_inv_id,
      Category.comp_id] using h
  have h := congrArg (fun f ↦ (λ_ U).inv ≫ f ≫ (λ_ (P.obj U)).hom) hleft
  change u = e
  simpa only [U, Functor.id_obj, id_tensorHom, leftUnitor_naturality, Category.assoc,
    Iso.inv_hom_id_assoc] using h.symm

-- Identify the native projection with the right-adjoint projection at the unit.
set_option maxHeartbeats 0 in
-- Elaborating the native derived adjunction involves large module parameters.
private theorem ordinaryProjection_unit_isIso
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (t : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso (canonicalOrdinaryProjection (D := D) Λ t N (𝟙_ _)) := by
  let := leftDerivedUpperStarOplaxMonoidal Λ t
  have : IsIso (Functor.OplaxMonoidal.η L((t)^*⟦Λ⟧)) := by
    rw [leftDerivedUpperStarOplaxMonoidal_η]
    infer_instance
  exact Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit
    (AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction Λ t)
    (leftDerivedUpperStarTensor Λ t)
    (fun _ _ ↦ rfl) N

private theorem isIso_app_of_iso
    {A : Type u} {B : Type v} [Category A] [Category B]
    {F G : A ⥤ B} (τ : F ⟶ G) {X Y : A} (e : X ≅ Y)
    [IsIso (τ.app X)] : IsIso (τ.app Y) := by
  have h : τ.app Y = F.map e.inv ≫ τ.app X ≫ G.map e.hom := by
    rw [← τ.naturality e.hom, ← F.map_comp_assoc, e.inv_hom_id,
      F.map_id, Category.id_comp]
  rw [h]
  infer_instance

set_option maxHeartbeats 0 in
-- The native projection is a mate involving large derived module instances.
private theorem ordinaryProjection_line_isIso
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (t : X ⟶ Spec (.of D.k))
    [LocallyOfFiniteType t] [QuasiCompact t] [IsSeparated t]
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D.k)))))
    (hL : Nonempty (L ≅ 𝟙_ _)) :
    IsIso (canonicalOrdinaryProjection (D := D) Λ t N L) := by
  obtain ⟨e⟩ := hL
  let τ := ((AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction
    Λ t).rightAdjointProjectionMap (leftDerivedUpperStarTensor Λ t)).app N
  have : IsIso (τ.app (𝟙_ _)) := ordinaryProjection_unit_isIso (D := D) Λ t N
  exact isIso_app_of_iso τ e.symm

private theorem nativeExchanges_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : Compactification (D.geometricFiber T₀).hom) :
    let q := CohomologyTransport.geometricFrobeniusGeometry D T₀
    IsIso (WeilConjectures.FrobeniusSquareExchange.direct (Mon.mk Λ) q.a
      (CommSq.mk q.comm)) ∧
    IsIso (CompactificationReindexing.squareExchange Λ
      (CohomologyTransport.frobeniusReindexedSquare q c)) := by
  dsimp only
  constructor
  · exact (condensed_isomorphism_square_exchange (Mon.mk Λ)
      (CommSq.mk (CohomologyTransport.geometricFrobeniusGeometry D T₀).comm)).2.2.2.2.2.2
  · have : IsIso (CohomologyTransport.frobeniusReindexedSquare
        (CohomologyTransport.geometricFrobeniusGeometry D T₀) c).middle := by
      change IsIso (𝟙 c.Z)
      infer_instance
    exact (CompactificationReindexing.square_isIso Λ
      (CohomologyTransport.frobeniusReindexedSquare
        (CohomologyTransport.geometricFrobeniusGeometry D T₀) c)
      (CommSq.mk (CohomologyTransport.geometricFrobeniusGeometry D T₀).comm)).2

set_option maxHeartbeats 0 in
-- Unfolding the native transport package requires a larger elaboration budget.
/-- Frobenius transport for condensed sections, mixed-support cup products and
pro-etale locally free degree-zero coefficient lines.

Source: the cup/sections sub-step of `sk-thm-frobenius`, in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-frobenius/sec-purity-duality-and-frobenius/
sk-thm-frobenius/_section.md`.
(blueprint: lem-pod-condensed-sections-cup-weil-transport).

Proof (the six DAG steps):
1. Compactify over k₀ and base change to k. Frobenius and its inverse commute
   with both factors. The native unit-square-counit direct exchange and the
   proper/open compact exchange are inverse to the exchanges for inverse Frobenius.
2. Normalize comparisons through common refinements. On a dense refinement the
   clopen projector is identity. The native refinement and projection equations,
   followed by the cocycle, transport the exchange to the chosen compactification.
3. Put φ_H = H(φ) e_H for H = G,F. The factors are invertible; naturality of e_H
   and the intertwining hypothesis on f prove the squares for G(f) and F(f).
4. Apply the cup/projection intertwining calculation to the intrinsic cup. The
   native tensor-shift comparison has sign (-1)^(s i) in first degree i. Pullback
   is exact and termwise, so both orders give the same sign and the shifted square.
5. A pro-etale trivializing cover of s has a section through one member. Pull
   the trivialization back to obtain L ≅ Λ_s, without choosing a Weil generator.
   Terminal coefficient evaluation gives L(*) ≅ R. The native line projections
   are invertible; their squares use φ_N tensored with the pullback datum of φ_L.
6. Restriction along g_s is the inverse native point comparison. It preserves
   section tensors, so μΓ followed by each cup/projection intertwines Γ(φ)ρ.
   The coefficient unit comparison gives id_R. Under any temporary trivialization
   of L, μΓ and the ordinary projection reduce to the right unitor. Their homology
   is [z]⊗v ↦ [z⊗v], independent of that trivialization, and its square is precisely
   F_N⊗F_L. Point-perfect realization is used only on Dctf. -/
theorem condensedSectionsCupWeilTransport
    {D₀ : WeilConjectures.FiniteFieldDatum.{u}}
    (C₀ : D₀.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsAdmissibleCoefficientFor C₀ (Mon.mk Λ))
    (T₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (c : Compactification (D₀.geometricFiber T₀).hom)
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D₀.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D₀.k)))))
    (hL : DegreeZeroLine L)
    (φL : (AlgebraicGeometry.ProEtale.CondensedRing.StrictWeilCondensed.action Λ
      (StrictWeilCondensed.pointFrobenius D₀)).obj L ≅ L)
    : Laws C₀ Λ
        (localizingAdmissibleCoefficientOfAdmissible C₀ Λ hΛ)
        T₀ c L hL φL := by
  have hg := condensedSectionsGeometricLaws C₀ Λ hΛ T₀ c L hL φL
  have hs := condensedSectionsScalarLaws C₀ Λ hΛ T₀ c L hL φL
  have he := nativeExchanges_isIso D₀ Λ T₀ c
  let := (pairingExactScalarPointCup Λ D₀.k).derived
  let : (moduleObjectDerivedPullback Λ
      (StrictWeilCondensed.pointFrobenius D₀).hom).Monoidal := by
    dsimp [moduleObjectDerivedPullback]
    infer_instance
  dsimp only [GeometricLaws] at hg
  dsimp only [ScalarLaws] at hs
  dsimp only [Laws]
  have hunit := hs.1
  have hrho := hs.2.1
  have hcohom := hs.2.2
  have hline := degreeZeroLine_trivial (D := D₀) L hL
  have hfree : FreeRankOneModule (coefficientSectionLine Λ L) := by
    refine hline.elim ?_
    intro e
    let := hunit
    exact ⟨(scalarCohomologyFunctor (D := D₀) Λ 0).mapIso e ≪≫
      (asIso (coefficientUnitMap (D := D₀) Λ)).symm⟩
  refine ⟨hfree, hline, he.1, he.2, hunit, ?_⟩
  intro hD hC
  let := hD
  let := hC
  refine (hg hD hC).elim ?_
  intro compare hgeo
  have href := hgeo.1
  have hnat := hgeo.2.1
  have hcup := @hgeo.2.2.1
  have hshift := @hgeo.2.2.2.1
  have hproj := @hgeo.2.2.2.2
  refine ⟨compare, href, hnat, ?_, ?_, hshift, ?_, ?_, ?_⟩
  · intro M N hM hN f φM φN hf
    constructor
    · exact inducedArrowData_intertwining _ _ f φM φN hf
    · exact inducedCompactData_intertwining _ _ _ f φM φN _ _
        (hnat _ _ hM hN f) hf
  · intro M N hM hN hMN φM φN
    refine ⟨hcup hM hN hMN φM φN, ?_⟩
    exact evaluatedTensorIntertwining_of_tensor_compatibility _ _ _
      (fun f g ↦ conjugatedTensor_naturality _ _
        (canonicalPointEvaluationIso (D := D₀) Λ) f g) _ _ _ _ (hrho _ _) (hcup hM hN hMN φM φN)
  · intro N hN hNL φN
    have hfiso := (hproj hN hNL φN).1
    have hgint := (hproj hN hNL φN).2.1
    have hfint := (hproj hN hNL φN).2.2
    have hgiso := ordinaryProjection_line_isIso (D := D₀) Λ
      (CohomologyTransport.geometricFrobeniusGeometry D₀ T₀).a N L hline
    refine ⟨hgiso, hfiso, hgint, hfint, ?_, ?_, ?_⟩
    · exact evaluatedTensorIntertwining_of_tensor_compatibility _ _ _
        (fun f g ↦ conjugatedTensor_naturality _ _
          (canonicalPointEvaluationIso (D := D₀) Λ) f g) _ _ _ _ (hrho _ _) hgint
    · exact evaluatedTensorIntertwining_of_tensor_compatibility _ _ _
        (fun f g ↦ conjugatedTensor_naturality _ _
          (canonicalPointEvaluationIso (D := D₀) Λ) f g) _ _ _ _ (hrho _ _) hfint
    · let := hgiso
      have : IsIso (Functor.LaxMonoidal.ε
          (CohomologyTransport.sections Λ (Spec (.of D₀.k))).mapDerivedCategory) :=
        pairingExactScalarPointCup_unit_isIso Λ D₀.k
      have : IsIso ((pairingExactScalarPointCup Λ D₀.k).derived.μ
          ((moduleObjectDerivedPushforward Λ
            (CohomologyTransport.geometricFrobeniusGeometry D₀ T₀).a).obj N) L) :=
        laxTensor_line_isIso
          (CohomologyTransport.sections Λ (Spec (.of D₀.k))).mapDerivedCategory _ L hline
      infer_instance
  · intro hUnit
    let := hUnit
    apply coefficientUnitTransport_eq_id
    have hu := tensorIso_unit_hom_eq
      (moduleObjectDerivedPullback Λ (StrictWeilCondensed.pointFrobenius D₀).hom)
      (pointPullbackIso (D := D₀) Λ).symm hrho
    have he : Functor.LaxMonoidal.ε
        (moduleObjectDerivedPullback Λ (StrictWeilCondensed.pointFrobenius D₀).hom) =
        (leftDerivedUpperStarUnitIso Λ (StrictWeilCondensed.pointFrobenius D₀).hom).inv := rfl
    rw [hu, he]
    change (scalarCohomologyFunctor (D := D₀) Λ 0).map
      ((leftDerivedUpperStarUnitIso Λ (StrictWeilCondensed.pointFrobenius D₀).hom).inv ≫
        (leftDerivedUpperStarUnitIso Λ (StrictWeilCondensed.pointFrobenius D₀).hom).hom) = _
    rw [Iso.inv_hom_id]
    exact (scalarCohomologyFunctor (D := D₀) Λ 0).map_id _
  · intro N hN φN j
    refine hline.elim ?_
    intro frame
    have hNL : condensedConstructibleFiniteTor Λ
        (CohomologyTransport.geometricFrobeniusGeometry D₀ T₀).X
        (N ⊗ (moduleObjectDerivedPullback Λ
          (CohomologyTransport.geometricFrobeniusGeometry D₀ T₀).a).obj L) := by
      let U := moduleObjectDerivedPullback Λ
        (CohomologyTransport.geometricFrobeniusGeometry D₀ T₀).a
      let e : N ⊗ U.obj L ≅ N :=
        whiskerLeftIso N (U.mapIso frame ≪≫ leftDerivedUpperStarUnitIso Λ _) ≪≫ ρ_ N
      exact ⟨(boundedConstructible _).prop_of_iso e.symm hN.1,
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso e.symm hN.2⟩
    exact hcohom hD hN φN j (hproj hN hNL φN).2.1

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
