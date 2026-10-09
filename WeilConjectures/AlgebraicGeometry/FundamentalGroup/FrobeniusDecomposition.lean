/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction

/-!
# Frobenius lifts in the decomposition group

In the situation of `AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut_hom_app_eq_of_mem_inertia`,
let the special geometric point `Spec κ ⟶ Spec B ⟶ Y` lie over a point `x` with finite residue
field, `κ` being an algebraic closure of `κ(x)`. An element `σ` of `Gal(Ω / K)` inducing on `κ`
the inverse of the arithmetic Frobenius `y ↦ y ^ #κ(x)` maps to a Frobenius element at `x`
(`AlgebraicGeometry.Scheme.FiniteEtale.isFrobeniusElement_galoisToFundamentalGroup`): through the
specialization, it acts on the fibres as the geometric Frobenius at the special point.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} [ConnectedSpace Y] {R K Ω : Type u} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
  [IsScalarTower R K Ω] [IsGalois K Ω] [IsSepClosed Ω] (a : Spec (.of R) ⟶ Y)
  {κ : Type u} [Field κ] [IsSepClosed κ] [Algebra (integralClosure R Ω) κ]
  (x : Y) [Finite (Y.residueField x)] [Algebra (Y.residueField x) κ]
  [IsAlgClosure (Y.residueField x) κ]
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ Y}
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

omit [IsDomain R] [IsFractionRing R K] [IsGalois K Ω] in
/-- **The residue Frobenius lift is a Frobenius element.** Let the special geometric point
`Spec κ ⟶ Spec B ⟶ Y` factor through `Spec κ(x) ⟶ Y`, with `κ` an algebraic closure of `κ(x)`,
and let `σ ∈ Gal(Ω / K)` induce on `κ` the inverse `σκ` of the arithmetic Frobenius. Then the image
of `σ` in `π₁(Y, s)` along any path is a Frobenius element at `x`. -/
theorem isFrobeniusElement_galoisToFundamentalGroup
    (hpt : pointOfAlgebra κ (integralClosurePoint Ω a) =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField x) κ)) ≫ Y.fromSpecResidueField x)
    (σ : Ω ≃ₐ[K] Ω) (σκ : κ ≃+* κ)
    (hσκ : (algebraMap (integralClosure R Ω) κ).comp
      (galoisIntegralClosure (R := R) σ : integralClosure R Ω →+* integralClosure R Ω) =
        (σκ : κ →+* κ).comp (algebraMap (integralClosure R Ω) κ))
    (hfrob : ∀ y, σκ y ^ Nat.card (Y.residueField x) = y)
    (τ : fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)) ≅ fiber s) :
    IsFrobeniusElement s G x
      (galoisToFundamentalGroup (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a) τ G σ) := by
  let ap := integralClosurePoint Ω a
  have hΩ := pointOfAlgebra_integralClosurePoint (K := K) (Ω := Ω) a
  -- the algebraic closure `κ` of `κ(x)`
  let eAlg : AlgebraicClosure (Y.residueField x) ≃ₐ[Y.residueField x] κ :=
    IsAlgClosure.equiv (Y.residueField x) _ κ
  let E : Spec (.of κ) ≅ Spec (.of (AlgebraicClosure (Y.residueField x))) :=
    Scheme.Spec.mapIso eAlg.toRingEquiv.toCommRingCatIso.op
  have hE : E.hom ≫ residueFieldPoint Y x = pointOfAlgebra κ ap := by
    rw [hpt, residueFieldPoint_eq, ← Category.assoc]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 2
    ext c
    exact eAlg.commutes c
  let eF := fiberIsoOfIso E hE
  let sp := asIso (specialization Ω κ ap)
  let eq : fiber (pointOfAlgebra Ω ap) ≅
      fiber (pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)) :=
    fiberIsoOfIso (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, hΩ])
  refine ⟨eF ≪≫ sp.symm ≪≫ eq ≪≫ τ, fun P z ↦ ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  rw [galoisToFundamentalGroup_smul]
  congr 1
  -- the key identity `σκ ∘ e = e ∘ Frob⁻¹`
  have hσκq (c : κ) : σκ (c ^ Nat.card (Y.residueField x)) = c := by
    obtain ⟨d, rfl⟩ := σκ.surjective c
    rw [hfrob]
  have hring : E.hom ≫ Spec.map (CommRingCat.ofHom
      (arithmeticFrobeniusAt x).symm.toRingEquiv.toRingHom) =
      Spec.map (CommRingCat.ofHom σκ.toRingHom) ≫ E.hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun w ↦ ?_)
    obtain ⟨v, rfl⟩ := (arithmeticFrobeniusAt x).surjective w
    change eAlg ((arithmeticFrobeniusAt x).symm (arithmeticFrobeniusAt x v)) =
      σκ (eAlg (arithmeticFrobeniusAt x v))
    rw [AlgEquiv.symm_apply_apply, arithmeticFrobeniusAt_apply, map_pow, hσκq]
  have heΩ : (specMapIso σ.toRingEquiv).hom ≫ pointOfAlgebra Ω ap = pointOfAlgebra Ω ap := by
    rw [hΩ]
    exact specMapIso_hom_comp_pointOfAlgebra _ σ
  have heκ : (specMapIso σκ).hom ≫ pointOfAlgebra κ ap = pointOfAlgebra κ ap := by
    rw [← hE, ← Category.assoc, specMapIso_hom, ← hring, Category.assoc, ← specMapIso_hom,
      specMapIso_hom_comp_residueFieldPoint]
  let w := sp.inv.app P (eF.hom.app P z)
  have key := specialization_app_fiberPrecompIso ap (galoisIntegralClosure σ) σ.toRingEquiv σκ
    (specMap_galoisIntegralClosure_comp a σ) (by ext; rfl) hσκ heΩ heκ P w
  have hspw : sp.hom.app P w = eF.hom.app P z :=
    ConcreteCategory.congr_hom (sp.inv_hom_id_app P) _
  have hκ : (fiberPrecompIso _ (specMapIso σκ) heκ).hom.app P (eF.hom.app P z) =
      eF.hom.app P ((geometricFrobeniusAt x).hom.app P z) := by
    apply fiber_ext
    rw [fiberPrecompIso_hom_app_left, fiberIsoOfIso_hom_app_left, fiberIsoOfIso_hom_app_left]
    unfold geometricFrobeniusAt
    rw [fiberPrecompIso_hom_app_left, specMapIso_hom, specMapIso_hom, ← Category.assoc, ← hring,
      Category.assoc]
  have hspw' : (specialization Ω κ ap).app P w = eF.hom.app P z := hspw
  rw [hspw', hκ] at key
  have hpre : (fiberPrecompIso _ (specMapIso σ.toRingEquiv) heΩ).hom.app P w =
      sp.inv.app P (eF.hom.app P ((geometricFrobeniusAt x).hom.app P z)) := by
    rw [← key]
    exact (ConcreteCategory.congr_hom (sp.hom_inv_id_app P) _).symm
  apply fiber_ext
  rw [galoisToAut_hom_app_left, fiberIsoOfIso_hom_app_left, fiberIsoOfIso_hom_app_left,
    ← congrArg Over.Hom.left hpre, fiberPrecompIso_hom_app_left]
  simp only [Iso.refl_hom, Category.id_comp]
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale
