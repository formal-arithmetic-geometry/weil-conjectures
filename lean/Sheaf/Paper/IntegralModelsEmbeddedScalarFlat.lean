/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import Sheaf.Paper.IntegralModelsEmbedded
import Sheaf.Paper.EmbeddedIntegralScalarKernelSquare
import Sheaf.AlgebraicGeometry.IntegralModelsFlatResidue
import all Sheaf.Paper.IntegralCoefficientExtComparison
import Sheaf.AlgebraicGeometry.IntegralConstantModelRealization
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Flatness of the embedded constant-to-continuous scalar map

Source: Stacks Project, Tag 093M, and the integral-models proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private theorem scalarFlat_transport
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    {R S B D : Sheaf J CommRingCat.{v}}
    (a : R ≅ S) (b : B ≅ D) (φ : R ⟶ B) (ψ : S ⟶ D)
    (hsquare : a.hom ≫ ψ = φ ≫ b.hom)
    (hflat : SheafOfModules.IsFlat ((ConstantCompletion.res φ).obj
      (SheafOfModules.unit (siteModuleRings B)))) :
    SheafOfModules.IsFlat ((ConstantCompletion.res ψ).obj
      (SheafOfModules.unit (siteModuleRings D))) := by
  let N := (ConstantCompletion.res φ).obj (SheafOfModules.unit (siteModuleRings B))
  let M := (ConstantCompletion.res ψ).obj (SheafOfModules.unit (siteModuleRings D))
  let ea (U : Cᵒᵖ) : R.obj.obj U ≃+* S.obj.obj U := Iso.commRingCatIsoToRingEquiv
    (((sheafToPresheaf J CommRingCat).mapIso a).app U)
  let eb (U : Cᵒᵖ) : B.obj.obj U ≃+* D.obj.obj U := Iso.commRingCatIsoToRingEquiv
    (((sheafToPresheaf J CommRingCat).mapIso b).app U)
  have hw (U : Cᵒᵖ) (r : R.obj.obj U) :
      ψ.hom.app U (ea U r) = eb U (φ.hom.app U r) :=
    congrArg (fun f ↦ f.hom.app U r) hsquare
  have hwi (U : Cᵒᵖ) (r : S.obj.obj U) :
      φ.hom.app U ((ea U).symm r) = (eb U).symm (ψ.hom.app U r) := by
    apply (eb U).injective
    simpa only [RingEquiv.apply_symm_apply] using (hw U ((ea U).symm r)).symm
  have hf : SheafOfModules.IsFlatOnSite.{v, v, v, v} (R := R) N := by
    unfold SheafOfModules.IsFlatOnSite
    unfold SheafOfModules.IsFlat at hflat
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R N).symm hflat
  have hM : SheafOfModules.IsFlatOnSite.{v, v, v, v} (R := S) M := by
    apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion S M
    intro U n x y hxy
    let x₀ : Fin n → R.obj.obj (op U) := fun i ↦ (ea (op U)).symm (x i)
    let y₀ : Fin n → B.obj.obj (op U) := fun i ↦ (eb (op U)).symm (y i)
    have hxy₀ : (∑ i, x₀ i • (show N.val.obj (op U) from y₀ i)) = 0 := by
      change (∑ i, ψ.hom.app (op U) (x i) * (show D.obj.obj (op U) from y i)) = 0 at hxy
      change (∑ i, φ.hom.app (op U) (x₀ i) * y₀ i) = 0
      simpa only [map_sum, map_mul, map_zero, ← hwi, x₀, y₀] using
        congrArg (eb (op U)).symm hxy
    obtain ⟨K, hK, hl⟩ :=
      SheafOfModules.local_equationalCriterion_of_isFlatOnSite R N hf U n x₀ y₀ hxy₀
    refine ⟨K, hK, ?_⟩
    intro V f hV
    obtain ⟨l, c, t, hy, hx⟩ := hl V f hV
    refine ⟨l, fun i j ↦ ea (op V) (c i j), fun j ↦ eb (op V) (t j), ?_, ?_⟩
    · intro i
      have hi := congrArg (eb (op V)) (hy i)
      change eb (op V) (B.obj.map f.op (y₀ i)) =
        eb (op V) (∑ j, φ.hom.app (op V) (c i j) * (show B.obj.obj (op V) from t j)) at hi
      have hn := ConcreteCategory.congr_hom (b.hom.hom.naturality f.op) (y₀ i)
      change eb (op V) (B.obj.map f.op (y₀ i)) =
        D.obj.map f.op (eb (op U) (y₀ i)) at hn
      change D.obj.map f.op (y i) =
        ∑ j, ψ.hom.app (op V) (ea (op V) (c i j)) * eb (op V) (t j)
      simpa only [map_sum, map_mul, ← hw, hn, y₀, RingEquiv.apply_symm_apply] using hi
    · intro j
      have hi := congrArg (ea (op V)) (hx j)
      have hn (i : Fin n) :
          ea (op V) (R.obj.map f.op (x₀ i)) = S.obj.map f.op (x i) := by
        have hh := ConcreteCategory.congr_hom (a.hom.hom.naturality f.op) (x₀ i)
        change ea (op V) (R.obj.map f.op (x₀ i)) =
          S.obj.map f.op (ea (op U) (x₀ i)) at hh
        simpa only [x₀, RingEquiv.apply_symm_apply] using hh
      simpa only [map_sum, map_mul, map_zero, hn] using hi
  unfold SheafOfModules.IsFlat
  unfold SheafOfModules.IsFlatOnSite at hM
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso S M) hM

private def smallRingIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S) :
    IntegralModelsStacks.smallRing X R ≅ IntegralModelsStacks.smallRing X S where
  hom := IntegralModelsStacks.smallMap X e.hom.hom
  inv := IntegralModelsStacks.smallMap X e.inv.hom
  hom_inv_id := by
    let i := (Mon.forget _).mapIso e
    ext U x
    change i.inv.hom.app (op (AsSmall.down.obj U.unop))
      (i.hom.hom.app (op (AsSmall.down.obj U.unop)) x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x)
      ((Mon.forget _).mapIso e).hom_inv_id
  inv_hom_id := by
    let i := (Mon.forget _).mapIso e
    ext U x
    change i.hom.hom.app (op (AsSmall.down.obj U.unop))
      (i.inv.hom.app (op (AsSmall.down.obj U.unop)) x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x)
      ((Mon.forget _).mapIso e).inv_hom_id

attribute [-instance] integralModel_coefficientMonObj in
/-- The actual embedded integral scalar map is flat.

Source: Stacks Project, sites-modules.tex, lemma-completion-flat (Tag 093M);
blueprint integral-models proof, paragraph (1)
(blueprint: lem-sfb-embedded-integral-scalar-flat).

Proof: the embedded integer ring of the finite extension is a discrete valuation
ring, hence Noetherian. Identify its continuous coefficient sheaf with the inverse
limit of its positive constant quotients using completedCondensedIntegral. Its
projection formulas fix this identification. The scalar map sends an integer to its
constant continuous function, so its composites with all these projections are the
constant quotient maps. Consequently it is the canonical completion map, not merely
some map between isomorphic rings. Apply ConstantCompletion.flat_and_quotients, or
its integral_constant_completion specialization after the spectral/embedded integer
ring comparison. Exact inverse image and the section-ring reconstruction identify
the corresponding scalar restriction and tensor functors. Precomposition with
AsSmall is an exact equivalence and preserves the tensor product; it therefore
preserves this flatness. This proves flatness of the displayed restricted regular
module. No nonempty-site hypothesis is used; on the empty site exactness is automatic.
-/
theorem integralModelsEmbeddedScalarFlat
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    let φ := IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
    SheafOfModules.IsFlat.{u + 1}
      ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)).obj
          (SheafOfModules.unit (siteModuleRings _))) := by
  let : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let e₀ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (integerRingSheafIso.{u} ℓ E)
  have : IsMonHom e₀.hom := Sheaf.isMonHom_sheafCompose_map _
    (integerRingSheafIso.{u} ℓ E).hom
  let e := Mon.mkIso' e₀ ≪≫ IntegralConstantModel.pointComparison ℓ (ULift.{u} E.val)
  obtain ⟨a, hsquare, _⟩ := embeddedIntegralScalarKernelSquare ℓ E π hπ e X
  let b := (upperStarFromPoint X).mapMon.mapIso e.symm
  have hsmall :
      (smallRingIso X a).hom ≫ IntegralModelsStacks.smallMap X
        (IntegralModelsEmbedded.scalarMap ℓ E X) =
      IntegralModelsStacks.smallMap X (IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X) ≫
        (smallRingIso X b).hom := by
    ext U x
    change (a.hom.hom ≫ IntegralModelsEmbedded.scalarMap ℓ E X).hom.app
        (op (AsSmall.down.obj U.unop)) x =
      (IntegralModelsStacks.scalarMap ℓ (ULift.{u} E.val) X ≫
        (upperStarFromPoint X).map e.inv.hom).hom.app
        (op (AsSmall.down.obj U.unop)) x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) hsquare
  exact scalarFlat_transport (smallRingIso X a) (smallRingIso X b) _ _ hsmall
    (IntegralModelsStacks.integralModels_flat_residue ℓ (ULift.{u} E.val) X).2.1

end AlgebraicGeometry.ProEtale
