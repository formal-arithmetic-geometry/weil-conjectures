/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.NormalEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.AlgebraicGeometry.IntegralEtaleNormalizationOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Quasi-compactness of integral separated étale schemes over normal Noetherian bases

Source: the generic-normalization argument in
`lem-sf-normal-strict-local-split-components`, steps 3--5; Stacks Project, Tags 032L and 05K0
(blueprint: lem-sf-integral-etale-quasi-compact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- An integral separated étale scheme over a normal integral Noetherian scheme is
quasi-compact over its base. The source need not initially be quasi-compact.

Source: Stacks Project, Tags 032L, 05K0 and 0AB1; the generic-normalization argument in
`lem-sf-normal-strict-local-split-components`, steps 3--5
(blueprint: lem-sf-integral-etale-quasi-compact).

Proof:
1. An étale map is open, so the nonempty source has image containing the generic point
   of the integral base. Its generic fibre is integral: on each affine chart it is a
   localization of a domain, and every nonempty affine chart contains the generic point.
   The étale generic fibre is discrete, so it consists of one point, with residue field
   a finite separable extension L of the function field of the base.
2. Normalize the base in L. On each nonempty affine base chart A, normality of the local
   rings implies A is an integrally closed domain. Its integral closure in L is finite
   over A by Tag 032L. These affine descriptions show the normalization is finite.
3. Normality ascends along the étale map. The theorem
   `integral_etale_normalization_open` identifies the source with an open subscheme of
   that finite normalization, without assuming quasi-compactness of the source.
4. The normalization is Noetherian, being finite over a Noetherian scheme. Every open
   of it is quasi-compact, so the source is Noetherian and its map to the base is
   quasi-compact. The assertion also holds for open immersions with nonempty source.
-/
theorem integral_etale_quasiCompact
    {X E : Scheme.{u}} [IsNoetherian X] [IsIntegral X] [IsIntegral E]
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (f : E ⟶ X) [IsSeparated f] [Etale f] : QuasiCompact f := by
  have : IsDominant f :=
    ⟨f.isOpenMap.isOpen_range.dense (Set.range_nonempty f)⟩
  have hgen : f (genericPoint E) = genericPoint X := by
    apply ((genericPoint_spec X).eq _).symm
    have h := (genericPoint_spec E).image f.continuous
    rwa [Set.image_univ, f.denseRange.closure_range] at h
  let φ : X.functionField ⟶ E.functionField :=
    X.presheaf.stalkSpecializes (Inseparable.of_eq hgen).specializes ≫
      f.stalkMap (genericPoint E)
  have hw : E.fromSpecFunctionField ≫ f = Spec.map φ ≫ X.fromSpecFunctionField := by
    dsimp [φ, Scheme.fromSpecFunctionField]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  let G := pullback f X.fromSpecFunctionField
  let p : G ⟶ Spec X.functionField := pullback.snd f X.fromSpecFunctionField
  let g : Spec E.functionField ⟶ G :=
    pullback.lift E.fromSpecFunctionField (Spec.map φ) hw
  have : IsLocallyArtinian G := IsLocallyArtinian.of_locallyQuasiFinite p
  let z : G := g (IsLocalRing.closedPoint E.functionField)
  have hz : pullback.fst f X.fromSpecFunctionField z = genericPoint E := by
    change (g ≫ pullback.fst f X.fromSpecFunctionField) _ = _
    rw [pullback.lift_fst]
    exact E.fromSpecStalk_closedPoint
  have hzall (y : G) : z = y := by
    apply specializes_iff_eq.mp
    apply (pullback.fst f X.fromSpecFunctionField).isEmbedding.toIsInducing.specializes_iff.mp
    rw [hz]
    exact genericPoint_specializes _
  have : Subsingleton G := ⟨fun a b ↦ (hzall a).symm.trans (hzall b)⟩
  have : Nonempty G := ⟨z⟩
  have : IsReduced G := isReduced_of_etale p
  have : IrreducibleSpace G := ⟨inferInstance⟩
  have : IsIntegral G := isIntegral_of_irreducibleSpace_of_isReduced _
  let L := Γ(G, ⊤)
  let : Field L := (isField_of_isIntegral_of_subsingleton G).toField
  let d : X.functionField ⟶ .of L := (Scheme.ΓSpecIso X.functionField).inv ≫ p.appTop
  let : Algebra X.functionField L := d.hom.toAlgebra
  have hd : RingHom.Etale d.hom :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso X.functionField).inv))
      ((HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := p)).mp inferInstance)
  have : Algebra.Etale X.functionField L := RingHom.etale_algebraMap.mp hd
  have : Module.Finite X.functionField L :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable X.functionField L :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  let e : G ≅ Spec (.of L) := G.isoSpec
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) = p := by
    change G.isoSpec.hom ≫ Spec.map d = p
    dsimp only [d]
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.comp_id]
  have : IsFinite (X.fromNormalizationIn L) := by
    let Φ := X.fromSpecOfAlgebraFunctionField L
    refine Φ.isFinite_fromNormalization_of_finite fun U hU hne ↦ ?_
    let := (Φ.app U).hom.toAlgebra
    have hηU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
    have : Nonempty U := ⟨⟨_, hηU⟩⟩
    have hxU : Φ (IsLocalRing.closedPoint L) ∈ U := by
      rw [Scheme.Hom.comp_apply, Spec_closedPoint]
      convert hηU
      exact Scheme.fromSpecStalk_closedPoint
    have hΦU : Φ ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem Φ hxU
    let θ : Γ(Spec (.of L), Φ ⁻¹ᵁ U) ≅ .of L :=
      (Spec (.of L)).presheaf.mapIso (eqToIso hΦU.symm).op ≪≫ Scheme.ΓSpecIso (.of L)
    have hθΦ : Φ.app U ≫ θ.hom =
        X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
      have h1 := Scheme.germ_stalkClosedPointTo Φ U hxU
      have h2 := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
        (CommRingCat.ofHom (algebraMap X.functionField L)) U hxU
      exact h1.symm.trans h2
    let : Algebra Γ(X, U) L := (Φ.app U ≫ θ.hom).hom.toAlgebra
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq' <| by
      change (Φ.app U ≫ θ.hom).hom = _
      rw [hθΦ]
      rfl
    have : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : IsIntegrallyClosed Γ(X, U) :=
      Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk (fun x ↦ (hX x).2) U
    have : Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) :=
      IsIntegralClosure.finite Γ(X, U) X.functionField L _
    let eθ : Γ(Spec (.of L), Φ ⁻¹ᵁ U) →ₐ[Γ(X, U)] L :=
      { θ.hom.hom with commutes' _ := rfl }
    let ψ : integralClosure Γ(X, U) Γ(Spec (.of L), Φ ⁻¹ᵁ U) →ₗ[Γ(X, U)]
        integralClosure Γ(X, U) L :=
      { toFun x := ⟨eθ x, x.2.map eθ⟩
        map_add' x y := Subtype.ext (map_add eθ x.1 y.1)
        map_smul' a x := Subtype.ext (map_smul eθ a x.1) }
    refine Module.Finite.of_injective ψ fun x y h ↦ ?_
    exact Subtype.ext ((ConcreteCategory.bijective_of_isIso θ.hom).1 congr($h.1))
  obtain ⟨j, hj, hjopen, -⟩ := integral_etale_normalization_open hX f
    (Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain f hX) L e he
  have : IsOpenImmersion j := hjopen
  have : IsLocallyNoetherian (X.normalizationIn L) :=
    LocallyOfFiniteType.isLocallyNoetherian (X.fromNormalizationIn L)
  rw [← hj]
  infer_instance

end AlgebraicGeometry
