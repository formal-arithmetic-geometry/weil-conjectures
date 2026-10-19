/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffineResidueEvaluationHomologyNaturality
import Sheaf.AlgebraicGeometry.AffinePerfectResidueModelNaturality
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Naturality of strictly perfect affine residue models

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-affine-residue-model-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 1600000 in
-- The model isomorphisms compare multiple derived and residue-module structures.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The affine model comparison can be chosen naturally for every represented arrow.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-affine-residue-model-naturality)

Proof: Terminal sections and associated sheaves give an adjunction whose counit
is invertible on finite free modules and their retracts. Its termwise natural
counit reconstructs every strictly perfect complex. The section complex is
bounded and termwise projective, hence K-flat. Factor the residue point through
U and use the natural derived open-restriction comparison. The K-flat pullback
counit computes its derived pullback by termwise residue extension. The residue
field isomorphism obtained from hp identifies this tensor complex with the
explicit affineResidueTerm complex. The canonical identification of homology
with cycles modulo incoming boundaries is natural in chain maps. Compose these
natural comparisons with the specified model isomorphisms m and m'. The source
comparison is fixed before the target or arrow is chosen. Naturality identifies
the residue homology map with derivedFiberCohomologyFunctor applied to b when
Q(phi) is m.inv followed by the restricted b and m'.hom. All terms in this
identity depend only on Q(phi), so it holds for every such representative.
No geometric direct-image hypothesis enters this argument. -/
theorem affine_residue_model_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (w : W) (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (E : schemeDerivedCategory W)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (m : (SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    ∃ eK : affineResidueCycleHomology W U p K ≃+ derivedFiberCohomology W E 1 w,
      ∀ (E' : schemeDerivedCategory W) (b : E ⟶ E')
        (C : CochainComplex
          (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
        (_hC : IsStrictlyPerfect W U C)
        (m' : (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E' ≅ DerivedCategory.Q.obj C),
        ∃ eC : affineResidueCycleHomology W U p C ≃+ derivedFiberCohomology W E' 1 w,
          ∀ (φ : K ⟶ C), DerivedCategory.Q.map φ =
              m.inv ≫ (SheafOfModules.overFunctor.{v}
                (moduleRings W.toRingedSpace) U).mapDerivedCategory.map b ≫ m'.hom →
            ∀ z : affineResidueCycleHomology W U p K,
              eC (affineResidueCycleHomologyMap φ z) =
                (derivedFiberCohomologyFunctor W w 1).map b (eK z) := by
  classical
  let R := (SheafOfModules.overFunctor.{v}
    (moduleRings W.toRingedSpace) U).mapDerivedCategory
  let H := localDerivedFiberCohomologyFunctor W w U hwU 1
  let A := derivedFiberCohomologyFunctor W w 1
  obtain ⟨θ⟩ := derived_fiber_open_factorization W w U hwU 1
  obtain ⟨q, hq⟩ := affine_residue_evaluation_homology_naturality W w U hwU hU p hp
  obtain ⟨t⟩ := affine_perfect_residue_model_naturality W w U hwU hU
  let oK : H.obj (DerivedCategory.Q.obj K) ≅ A.obj E :=
    H.mapIso m.symm ≪≫ θ.app E
  let eK := (q K).trans (t.app ⟨K, hK⟩).toLinearEquiv.toAddEquiv
  refine ⟨eK.trans oK.toLinearEquiv.toAddEquiv, ?_⟩
  intro E' b C hC m'
  let oC : H.obj (DerivedCategory.Q.obj C) ≅ A.obj E' :=
    H.mapIso m'.symm ≪≫ θ.app E'
  let eC := (q C).trans (t.app ⟨C, hC⟩).toLinearEquiv.toAddEquiv
  refine ⟨eC.trans oC.toLinearEquiv.toAddEquiv, ?_⟩
  intro φ hφ z
  have hlocal : eC (affineResidueCycleHomologyMap φ z) =
      H.map (DerivedCategory.Q.map φ) (eK z) := by
    change (t.app ⟨C, hC⟩).hom (q C (affineResidueCycleHomologyMap φ z)) = _
    rw [hq K C φ z]
    exact ConcreteCategory.congr_hom
      (t.hom.naturality (X := ⟨K, hK⟩) (Y := ⟨C, hC⟩) (ObjectProperty.homMk φ))
        (q K z)
  have hsquare : H.map (DerivedCategory.Q.map φ) ≫ oC.hom = oK.hom ≫ A.map b := by
    dsimp only [oC, oK, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [hφ, H.map_comp, H.map_comp]
    simp only [Category.assoc]
    rw [← H.map_comp_assoc m'.hom m'.inv, m'.hom_inv_id, H.map_id, Category.id_comp]
    have hn := θ.hom.naturality b
    dsimp only [Functor.comp_map] at hn
    change H.map (R.map b) ≫ (θ.app E').hom = (θ.app E).hom ≫ A.map b at hn
    exact congrArg (fun a ↦ H.map m.inv ≫ a) hn
  change oC.hom (eC (affineResidueCycleHomologyMap φ z)) = A.map b (oK.hom (eK z))
  rw [hlocal]
  exact ConcreteCategory.congr_hom hsquare (eK z)

end AlgebraicGeometry.Scheme
