/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Derived.DualizableRetract
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidalStructure

/-!
# Pulling back a chain-level coevaluation

Let `g : Z ⟶ Y` be a morphism of schemes such that `g^*` preserves flat sheaves, so that the
derived pullback `Lg^*` is monoidal (`AlgebraicGeometry.ProEtale.monoidalLeftDerivedUpperStar`)
and sends a duality `K ⊣ D` of `D(Y_proét)` to a duality `Lg^* K ⊣ Lg^* D`. If the coevaluation
of `K ⊣ D`, with `K ≅ Q(M)` and `D ≅ Q(F)`, is represented by a chain map `φ` out of the unit
(up to a quasi-isomorphism `s`), then the coevaluation of the pulled back duality is represented
by `g^* φ`, through the chain-level comparison `g^*(M ⊗ F) ≅ g^* M ⊗ g^* F`. The precise form
used here is the retract statement `AlgebraicGeometry.ProEtale.exists_retract_of_upperStar`: if
the representative of the pulled back coevaluation factors through `L' ⊗ g^* F` for a
subcomplex `ι : L' ⟶ g^* M`, then `Q(g^* M)` is a retract of `Q(L')`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory DerivedCategory Functor.LaxMonoidal
  Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]

set_option maxHeartbeats 1600000 in -- the coherence computation in the derived category is slow
/-- **Retracts from a pulled back coevaluation.** Let `K ⊣ D` be a duality in `D(Y_proét)`,
with `K ≅ Q(M)` and `D ≅ Q(F)`, whose coevaluation followed by `Q(s)` is `Q(φ)` for a chain map
`φ` out of the unit and a quasi-isomorphism `s : M ⊗ F ⟶ I`. Suppose `g^* F` is K-flat, and let
`ι : L' ⟶ g^* M` be a morphism of complexes, `φt` a chain map out of the unit with
`Q(g^* φ) = Q(φt ≫ g^* s)` (after `𝟙_ ≅ g^* 𝟙_`), and `τ` a lift of `φt ≫ δ` through
`ι ▷ g^* F`, where `δ : g^*(M ⊗ F) ⟶ g^* M ⊗ g^* F` is the comparison. Then `Q(g^* M)` is a
retract of `Q(L')` along `Q(ι)`. -/
theorem exists_retract_of_upperStar
    (K D : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) [ExactPairing K D]
    (M F I : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ)
    (e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj M))
    (eD : D ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj F))
    (s : M ⊗ F ⟶ I) [QuasiIso s]
    (φ : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ) ⟶ I)
    (v : 𝟙_ _ ⟶ Qh.obj ((HomotopyCategory.quotient _ _).obj
      (𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ))))
    (hφ : η_ K D ≫ (e.hom ⊗ₘ eD.hom) ≫ μ Qh _ _ ≫ Qh.map ((HomotopyCategory.quotient _ _).map s) =
      v ≫ Qh.map ((HomotopyCategory.quotient _ _).map φ))
    (hF : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F))
    {L' : CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ}
    (ι : L' ⟶ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj M)
    (φt : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ) ⟶
      ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj (M ⊗ F))
    (hφt : Q.map (inv (η ((g)^*[A].mapHomologicalComplex (.up ℤ))) ≫
      ((g)^*[A].mapHomologicalComplex (.up ℤ)).map φ) =
        Q.map (φt ≫ ((g)^*[A].mapHomologicalComplex (.up ℤ)).map s))
    (τ : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ) ⟶
      L' ⊗ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F)
    (hτ : τ ≫ ι ▷ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F =
      φt ≫ δ ((g)^*[A].mapHomologicalComplex (.up ℤ)) M F) :
    ∃ r : Q.obj (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj M) ⟶ Q.obj L',
      r ≫ Q.map ι = 𝟙 _ := by
  let G := L((g)^*[A])
  let GC := (g)^*[A].mapHomologicalComplex (.up ℤ)
  let GH := (g)^*[A].mapHomotopyCategory (.up ℤ)
  let qY := HomotopyCategory.quotient (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)
  let qZ := HomotopyCategory.quotient (Sheaf (Scheme.ProEt.topology Z) A) (.up ℤ)
  let c' := (g)^*[A].leftDerivedFunctorCounit
  let fac := (g)^*[A].mapHomotopyCategoryFactors (.up ℤ)
  let _ := monoidalLeftDerivedUpperStar A g
  let _ := ExactPairing.map G K D
  let Q' := qZ ⋙ Qh
  have hQ' {N N' : CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ} {f f' : N ⟶ N'}
      (h : Q.map f = Q.map f') : Q'.map f = Q'.map f' := by
    rw [← cancel_mono ((quotientCompQhIso _).hom.app N')]
    exact ((quotientCompQhIso _).hom.naturality f).trans
      ((congrArg _ h).trans ((quotientCompQhIso _).hom.naturality f').symm)
  -- the comparison `Lg^* Q(N) ≅ Q(g^* N)`
  let cI (N : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ) :
      G.obj (Qh.obj (qY.obj N)) ≅ Q'.obj (GC.obj N) :=
    asIso (c'.app (qY.obj N)) ≪≫ Qh.mapIso (fac.app N)
  have hcI {N N' : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ} (f : N ⟶ N') :
      G.map (Qh.map (qY.map f)) ≫ (cI N').hom = (cI N).hom ≫ Q'.map (GC.map f) := by
    have h₁ : G.map (Qh.map (qY.map f)) ≫ c'.app (qY.obj N') =
        c'.app (qY.obj N) ≫ Qh.map (GH.map (qY.map f)) := c'.naturality (qY.map f)
    have h₂ : GH.map (qY.map f) ≫ fac.hom.app N' = fac.hom.app N ≫ qZ.map (GC.map f) :=
      fac.hom.naturality f
    simp only [cI, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Category.assoc, Iso.app_hom]
    rw [reassoc_of% h₁, ← Qh.map_comp, h₂, Qh.map_comp]
    rfl
  have hQs : IsIso (Qh.map (qY.map s)) := by
    have : IsIso (Q.map s) := (isIso_Q_map_iff_quasiIso (C := Sheaf (Scheme.ProEt.topology Y) A)
      s).2 inferInstance
    have h : Qh.map (qY.map s) = (quotientCompQhIso _).hom.app _ ≫ Q.map s ≫
        (quotientCompQhIso _).inv.app _ := by
      rw [← quotientCompQhIso_hom_naturality_assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [h]
    infer_instance
  have hQ's : IsIso (Q'.map (GC.map s)) := by
    have h : Q'.map (GC.map s) = (cI _).inv ≫ G.map (Qh.map (qY.map s)) ≫ (cI _).hom := by
      rw [hcI s, Iso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  have C2 : Qh.map (δ GH (qY.obj M) (qY.obj F) ≫ (fac.hom.app M ⊗ₘ fac.hom.app F) ≫
      μ qZ (GC.obj M) (GC.obj F)) = Qh.map (fac.hom.app (M ⊗ F) ≫ qZ.map (δ GC M F)) := by
    congr 1
    have hμ : μ qZ (GC.obj M) (GC.obj F) = 𝟙 _ := rfl
    have h₁ (N : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ) : fac.hom.app N = 𝟙 _ := rfl
    rw [hμ, h₁, h₁, h₁]
    erw [MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.comp_id, Category.id_comp]
    rfl
  have C1 : δ G (Qh.obj (qY.obj M)) (Qh.obj (qY.obj F)) ≫ ((cI M).hom ⊗ₘ (cI F).hom) ≫
      μ Q' (GC.obj M) (GC.obj F) =
      G.map (μ Qh (qY.obj M) (qY.obj F)) ≫ (cI (M ⊗ F)).hom ≫ Q'.map (δ GC M F) := by
    have hfac := leftDerivedUpperStarTensorComparison_fac A g (qY.obj M) (qY.obj F)
    have hnat := μ_natural Qh (fac.hom.app M) (fac.hom.app F)
    have hμQ' : μ Q' (GC.obj M) (GC.obj F) =
        μ Qh (qZ.obj (GC.obj M)) (qZ.obj (GC.obj F)) ≫ Qh.map (μ qZ (GC.obj M) (GC.obj F)) :=
      Functor.LaxMonoidal.comp_μ _ _ _ _
    calc _ = (δ G _ _ ≫ (c'.app (qY.obj M) ⊗ₘ c'.app (qY.obj F)) ≫
          μ Qh (GH.obj (qY.obj M)) (GH.obj (qY.obj F))) ≫
          Qh.map ((fac.hom.app M ⊗ₘ fac.hom.app F) ≫ μ qZ (GC.obj M) (GC.obj F)) := by
          simp only [cI, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom]
          rw [hμQ', ← tensorHom_comp_tensorHom, Category.assoc, Category.assoc,
            reassoc_of% hnat, Qh.map_comp]
          simp only [Category.assoc]
          rfl
      _ = _ := by
          erw [hfac]
          simp only [Category.assoc]
          rw [← Qh.map_comp]
          erw [C2]
          rw [Qh.map_comp]
          simp only [cI, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom,
            Category.assoc]
          rfl
  let e' : G.obj K ≅ Q'.obj (GC.obj M) := G.mapIso e ≪≫ cI M
  let ψD : G.obj D ≅ Q'.obj (GC.obj F) := G.mapIso eD ≪≫ cI F
  let Z₀ : 𝟙_ _ ⟶ Q'.obj (𝟙_ _) := ε G ≫ G.map v ≫ (cI _).hom ≫ Q'.map (η GC)
  have hE : η_ (G.obj K) (G.obj D) ≫ ((G.map e.hom ≫ (cI M).hom) ⊗ₘ (G.map eD.hom ≫ (cI F).hom)) ≫
      μ Q' _ _ = (ε G ≫ G.map v ≫ (cI _).hom ≫ Q'.map (η GC)) ≫ Q'.map (τ ≫ ι ▷ GC.obj F) := by
    have hη : η_ (G.obj K) (G.obj D) = ε G ≫ G.map (η_ K D) ≫ δ G K D := rfl
    have hcoc : Q'.map (GC.map φ) = Q'.map (η GC) ≫ Q'.map (φt ≫ GC.map s) := by
      rw [← hQ' hφt, ← Q'.map_comp, IsIso.hom_inv_id_assoc]
    have hφ' : G.map (η_ K D) ≫ G.map (e.hom ⊗ₘ eD.hom) ≫ G.map (μ Qh _ _) ≫
        G.map (Qh.map (qY.map s)) = G.map v ≫ G.map (Qh.map (qY.map φ)) := by
      simp only [← G.map_comp]
      exact congrArg G.map hφ
    rw [hη, hτ, ← tensorHom_comp_tensorHom_assoc (G.map e.hom) (G.map eD.hom) (cI M).hom (cI F).hom,
      Category.assoc, Category.assoc, δ_natural_assoc, C1,
      ← IsIso.hom_inv_id_assoc (Q'.map (GC.map s)) (Q'.map (δ GC M F)),
      ← reassoc_of% (hcI s), reassoc_of% hφ',
      reassoc_of% (hcI φ), hcoc]
    simp only [Category.assoc, Functor.map_comp, IsIso.hom_inv_id_assoc]
    rfl
  have hk := (HomotopyCategory.kFlat_quotient_obj_iff _).2 hF
  have hμ (N : CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ) :
      IsIso (μ Q' N (GC.obj F)) := by
    have : IsIso (μ Qh (qZ.obj N) (qZ.obj (GC.obj F))) :=
      isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hk
    rw [Functor.LaxMonoidal.comp_μ]
    infer_instance
  let ψ := G.map eD.hom ≫ (cI F).hom
  obtain ⟨w0, hw0⟩ := exists_comp_eq_of_coevaluation_comp_whiskerRight
    (G.map e.hom ≫ (cI M).hom) (Q'.map ι)
    ((ε G ≫ G.map v ≫ (cI _).hom ≫ Q'.map (η GC)) ≫ Q'.map τ ≫ inv (μ Q' L' (GC.obj F)) ≫
      (Q'.obj L' ◁ inv ψ)) (by
      rw [← cancel_mono (Q'.obj (GC.obj M) ◁ ψ ≫ μ Q' (GC.obj M) (GC.obj F))]
      conv_rhs => rw [Category.assoc, ← tensorHom_def_assoc, hE]
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc, IsIso.inv_hom_id, whiskerLeft_id,
        Category.id_comp, μ_natural_left, IsIso.inv_hom_id_assoc, ← Q'.map_comp])
  refine ⟨(quotientCompQhIso _).inv.app _ ≫ inv (G.map e.hom ≫ (cI M).hom) ≫ w0 ≫
    (quotientCompQhIso _).hom.app L', ?_⟩
  rw [Category.assoc, Category.assoc, Category.assoc, ← quotientCompQhIso_hom_naturality]
  erw [reassoc_of% hw0]
  rw [← Category.assoc (G.map e.hom) (cI M).hom, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app]


/-- The coevaluation of a duality `K ⊣ D` of `D(Y_proét)`, transported to a morphism
`Q(𝟙_[0]) ⟶ Q(M ⊗ F)` along `K ≅ Q(M)` and `D ≅ Q(F)` and the tensor comparison of `Qh`. -/
noncomputable def coevaluationQ
    (K D : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) [ExactPairing K D]
    (M F : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ)
    (e : K ≅ Q.obj M) (eD : D ≅ Q.obj F) :
    Q.obj (𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ)) ⟶ Q.obj (M ⊗ F) :=
  (singleFunctorObjUnitIso (Sheaf (Scheme.ProEt.topology Y) A)).hom ≫ η_ K D ≫
    ((e ≪≫ ((quotientCompQhIso _).app M).symm).hom ⊗ₘ
      (eD ≪≫ ((quotientCompQhIso _).app F).symm).hom) ≫
    μ Qh ((HomotopyCategory.quotient _ (.up ℤ)).obj M)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj F) ≫
      (quotientCompQhIso _).hom.app (M ⊗ F)

/-- `exists_retract_of_upperStar`, with the coevaluation given in the form
`coevaluationQ K D M F e eD = Q(φ) ≫ Q(s)⁻¹`. -/
theorem exists_retract_of_upperStar_of_coevaluationQ
    (K D : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) [ExactPairing K D]
    (M F I : CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ)
    (e : K ≅ Q.obj M) (eD : D ≅ Q.obj F)
    (s : M ⊗ F ⟶ I) [QuasiIso s]
    (φ : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Y) A) ℤ) ⟶ I)
    (hu : coevaluationQ K D M F e eD = Q.map φ ≫ inv (Q.map s))
    (hF : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F))
    {L' : CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ}
    (ι : L' ⟶ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj M)
    (φt : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ) ⟶
      ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj (M ⊗ F))
    (hφt : Q.map (inv (η ((g)^*[A].mapHomologicalComplex (.up ℤ))) ≫
      ((g)^*[A].mapHomologicalComplex (.up ℤ)).map φ) =
        Q.map (φt ≫ ((g)^*[A].mapHomologicalComplex (.up ℤ)).map s))
    (τ : 𝟙_ (CochainComplex (Sheaf (Scheme.ProEt.topology Z) A) ℤ) ⟶
      L' ⊗ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F)
    (hτ : τ ≫ ι ▷ ((g)^*[A].mapHomologicalComplex (.up ℤ)).obj F =
      φt ≫ δ ((g)^*[A].mapHomologicalComplex (.up ℤ)) M F) :
    ∃ r : Q.obj (((g)^*[A].mapHomologicalComplex (.up ℤ)).obj M) ⟶ Q.obj L',
      r ≫ Q.map ι = 𝟙 _ := by
  let qc := quotientCompQhIso (Sheaf (Scheme.ProEt.topology Y) A)
  let v₀ := singleFunctorObjUnitIso (Sheaf (Scheme.ProEt.topology Y) A)
  refine exists_retract_of_upperStar g K D M F I (e ≪≫ (qc.app M).symm)
    (eD ≪≫ (qc.app F).symm) s φ (inv v₀.hom ≫ qc.inv.app _) ?_ hF ι φt hφt τ hτ
  have hu' := hu =≫ Q.map s
  simp only [coevaluationQ, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hu'
  rw [← cancel_mono (qc.hom.app I), ← cancel_epi v₀.hom]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  erw [quotientCompQhIso_hom_naturality s, quotientCompQhIso_hom_naturality φ,
    Iso.inv_hom_id_app_assoc]
  exact hu'

end ProEtale

end AlgebraicGeometry
