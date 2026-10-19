/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Cotangent
import Sheaf.AlgebraicGeometry.RationalPointTangentDerivationIdentification

/-!
# Rational tangent spaces and cotangent duality

Source: Stacks Project, Tags 0B2E, 0B2C and 0B2F
(blueprint: lem-sc-rational-tangent-cotangent-duality).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
private theorem structural_stalk_comp
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x)) ≫ f.stalkMap x =
      StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x := by
  apply Spec.map_inj.mp
  simp only [Spec.map_comp, Category.assoc]
  rw [← Spec.fromSpecStalk_eq' (R := CommRingCat.of k) (x := pY (f x)),
    Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← Spec.fromSpecStalk_eq' (R := CommRingCat.of k) (x := pX x),
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  simp only [Category.assoc, hf]

private theorem sharp_reconstruct
    {X : Scheme.{u}} {A : Type u} [CommRing A] [IsLocalRing A]
    (θ : Spec (.of A) ⟶ X) (x : X) (hx : θ (IsLocalRing.closedPoint A) = x) :
    Spec.map (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hx.symm) ≫
      Scheme.stalkClosedPointTo θ) ≫ X.fromSpecStalk x = θ := by
  subst x
  simpa using Scheme.Spec_stalkClosedPointTo_fromSpecStalk θ

private theorem sharp_naturality
    {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (f : X ⟶ Y)
    (φ : CommRingCat.of A ⟶ CommRingCat.of B)
    (θ : Spec (.of A) ⟶ X) (η : Spec (.of B) ⟶ Y)
    (hη : η = Spec.map φ ≫ θ ≫ f) (x : X)
    (hx : θ (IsLocalRing.closedPoint A) = x)
    (hy : η (IsLocalRing.closedPoint B) = f x) :
    eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hy.symm) ≫
        Scheme.stalkClosedPointTo η =
      f.stalkMap x ≫
        (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hx.symm) ≫
          Scheme.stalkClosedPointTo θ) ≫ φ := by
  apply Spec.map_inj.mp
  apply (cancel_mono (Y.fromSpecStalk (f x))).mp
  rw [sharp_reconstruct η (f x) hy]
  simp only [Spec.map_comp, Category.assoc]
  rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
  have H := sharp_reconstruct θ x hx
  rw [Spec.map_comp] at H
  simp only [Category.assoc] at H
  simpa only [Category.assoc] using
    hη.trans (congrArg (fun g ↦ Spec.map φ ≫ g ≫ f) H.symm)

/-- At rational points the dual-number tangent spaces are canonically the duals of the
maximal ideals modulo their squares, and the differential is dual to the stalk-induced map.
The maps `rX`, `rY` are the structural maps from `k` to the residue fields; their
bijectivity expresses rationality, and scalars on tangent and cotangent spaces are
restricted along them, in the forms of
`exists_rationalPoint_tangent_cotangent_linearEquiv`
(lem-sc-rational-point-tangent-derivation-identification). The equivalences `EX`, `EY`
are characterized exactly as there, by the epsilon coefficient `D` of the stalk map of a
tangent vector; `U` is characterized on maximal-ideal representatives.
Source: Stacks Project, Tags 0B2E, 0B2C and 0B2F
(blueprint: lem-sc-rational-tangent-cotangent-duality).

Proof for stage 3:
1. Apply lem-sc-rational-point-tangent-derivation-identification at `x` and `f x`.
   A tangent vector corresponds to a local map `a ↦ residue(a) + D(a) * epsilon`.
   Its derivation kills the square of the maximal ideal, giving the displayed equivalences.
2. By def-weil-locally-ringed-space-morphism the stalk map carries the maximal ideal and
   its square into their counterparts, giving `U` with the representative formula below.
   By def-weil-residue-field and `hf` the induced residue map is compatible with `rX`,
   `rY`; both being bijective it is bijective, and the tangent map of
   def-sc-scheme-tangent-space applies.
3. By lem-weil-pbc-scheme-stalk-map-composition, postcomposition of a tangent vector
   with `f` composes its local ring map with `f.stalkMap x`. Taking epsilon coefficients
   gives `D` precomposed with the stalk map. On maximal-ideal classes this is exactly
   `EY (schemeTangentMap ... theta) = (EX theta).comp U`, the asserted duality.
-/
theorem rational_tangent_cotangent_duality
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    let RX := X.presheaf.stalk x
    let RY := Y.presheaf.stalk (f x)
    let KX := X.residueField x
    let KY := Y.residueField (f x)
    let rX : k →+* KX :=
      (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom
    let rY : k →+* KY :=
      (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x) ≫ Y.residue (f x)).hom
    Function.Bijective rX → Function.Bijective rY →
    letI : Module k (schemeTangentSpace k X pX x) :=
      Module.compHom (schemeTangentSpace k X pX x) rX
    letI : Module k (schemeTangentSpace k Y pY (f x)) :=
      Module.compHom (schemeTangentSpace k Y pY (f x)) rY
    letI : Module KX (IsLocalRing.CotangentSpace RX) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField RX) (IsLocalRing.CotangentSpace RX))
    letI : Module KY (IsLocalRing.CotangentSpace RY) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField RY) (IsLocalRing.CotangentSpace RY))
    letI : Module k (IsLocalRing.CotangentSpace RX) :=
      Module.compHom (IsLocalRing.CotangentSpace RX) rX
    letI : Module k (IsLocalRing.CotangentSpace RY) :=
      Module.compHom (IsLocalRing.CotangentSpace RY) rY
    ∃ he : Function.Bijective (f.residueFieldMap x).hom,
      ∃ (EX : schemeTangentSpace k X pX x ≃ₗ[k] (IsLocalRing.CotangentSpace RX →ₗ[k] k))
        (EY : schemeTangentSpace k Y pY (f x) ≃ₗ[k] (IsLocalRing.CotangentSpace RY →ₗ[k] k))
        (U : IsLocalRing.CotangentSpace RY →ₗ[k] IsLocalRing.CotangentSpace RX),
        (∀ θ : schemeTangentSpace k X pX x,
          ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber KX)) = x,
            let sharp : RX →+* DualNumber KX :=
              (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hx.symm) ≫
                Scheme.stalkClosedPointTo θ.val).hom
            ∃! D : RX → k,
              (∀ a : RX, sharp a =
                TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (rX (D a))) ∧
              (∀ a : IsLocalRing.maximalIdeal RX,
                EX θ ((IsLocalRing.maximalIdeal RX).toCotangent a) = D a)) ∧
        (∀ θ : schemeTangentSpace k Y pY (f x),
          ∃ hy : θ.val (IsLocalRing.closedPoint (DualNumber KY)) = f x,
            let sharp : RY →+* DualNumber KY :=
              (eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hy.symm) ≫
                Scheme.stalkClosedPointTo θ.val).hom
            ∃! D : RY → k,
              (∀ a : RY, sharp a =
                TrivSqZeroExt.inl ((Y.residue (f x)).hom a) + TrivSqZeroExt.inr (rY (D a))) ∧
              (∀ a : IsLocalRing.maximalIdeal RY,
                EY θ ((IsLocalRing.maximalIdeal RY).toCotangent a) = D a)) ∧
        (∀ b : IsLocalRing.maximalIdeal RY,
          ∃ hb : (f.stalkMap x).hom b ∈ IsLocalRing.maximalIdeal RX,
            U ((IsLocalRing.maximalIdeal RY).toCotangent b) =
              (IsLocalRing.maximalIdeal RX).toCotangent ⟨(f.stalkMap x).hom b, hb⟩) ∧
        ∀ θ : schemeTangentSpace k X pX x,
          EY (schemeTangentMap k X Y pX pY f hf x he θ) = (EX θ).comp U := by
  dsimp only
  intro hrX hrY
  let RX := X.presheaf.stalk x
  let RY := Y.presheaf.stalk (f x)
  let KX := X.residueField x
  let KY := Y.residueField (f x)
  let sX : k →+* RX := (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x).hom
  let sY : k →+* RY := (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x)).hom
  let rX : k →+* KX :=
    (StructureSheaf.toStalk k (pX x) ≫ pX.stalkMap x ≫ X.residue x).hom
  let rY : k →+* KY :=
    (StructureSheaf.toStalk k (pY (f x)) ≫ pY.stalkMap (f x) ≫ Y.residue (f x)).hom
  let : Module k (schemeTangentSpace k X pX x) :=
    Module.compHom (schemeTangentSpace k X pX x) rX
  let : Module k (schemeTangentSpace k Y pY (f x)) :=
    Module.compHom (schemeTangentSpace k Y pY (f x)) rY
  let : Module KX (IsLocalRing.CotangentSpace RX) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField RX) (IsLocalRing.CotangentSpace RX))
  let : Module KY (IsLocalRing.CotangentSpace RY) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField RY) (IsLocalRing.CotangentSpace RY))
  let : Module k (IsLocalRing.CotangentSpace RX) :=
    Module.compHom (IsLocalRing.CotangentSpace RX) rX
  let : Module k (IsLocalRing.CotangentSpace RY) :=
    Module.compHom (IsLocalRing.CotangentSpace RY) rY
  have hs (a : k) : (f.stalkMap x).hom (sY a) = sX a :=
    congrArg (fun g : CommRingCat.of k ⟶ RX ↦ g.hom a)
      (structural_stalk_comp k X Y pX pY f hf x)
  have hr (a : k) : (f.residueFieldMap x).hom (rY a) = rX a := by
    have H := congrArg (fun g : RY ⟶ KX ↦ g.hom (sY a))
      (Scheme.residue_residueFieldMap f x)
    change (f.residueFieldMap x).hom (rY a) = (X.residue x).hom
      ((f.stalkMap x).hom (sY a)) at H
    rw [hs] at H
    exact H
  have he : Function.Bijective (f.residueFieldMap x).hom := by
    refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨c, rfl⟩ := hrX.2 a
    exact ⟨rY c, hr c⟩
  have hm : IsLocalRing.maximalIdeal RY ≤
      (IsLocalRing.maximalIdeal RX).comap (f.stalkMap x).hom := by
    rw [IsLocalRing.maximalIdeal_comap]
  let UZ := Ideal.mapCotangent (IsLocalRing.maximalIdeal RY)
    (IsLocalRing.maximalIdeal RX) (f.stalkMap x).hom.toIntAlgHom hm
  let : Algebra RX KX := inferInstanceAs (Algebra RX (IsLocalRing.ResidueField RX))
  let : Algebra RY KY := inferInstanceAs (Algebra RY (IsLocalRing.ResidueField RY))
  let : IsScalarTower RX KX (IsLocalRing.CotangentSpace RX) :=
    inferInstanceAs (IsScalarTower RX (IsLocalRing.ResidueField RX)
      (IsLocalRing.CotangentSpace RX))
  let : IsScalarTower RY KY (IsLocalRing.CotangentSpace RY) :=
    inferInstanceAs (IsScalarTower RY (IsLocalRing.ResidueField RY)
      (IsLocalRing.CotangentSpace RY))
  have hsmX (a : k) (v : IsLocalRing.CotangentSpace RX) : a • v = sX a • v :=
    IsScalarTower.algebraMap_smul KX (sX a) v
  have hsmY (a : k) (v : IsLocalRing.CotangentSpace RY) : a • v = sY a • v :=
    IsScalarTower.algebraMap_smul KY (sY a) v
  let U : IsLocalRing.CotangentSpace RY →ₗ[k] IsLocalRing.CotangentSpace RX :=
    { toFun := UZ
      map_add' := UZ.map_add
      map_smul' := by
        intro a v
        obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal RY) v
        rw [hsmY, ← map_smul]
        change (IsLocalRing.maximalIdeal RX).toCotangent
            ⟨(f.stalkMap x).hom (sY a * b),
              hm ((IsLocalRing.maximalIdeal RY).smul_mem (sY a) b.2)⟩ =
          a • (IsLocalRing.maximalIdeal RX).toCotangent
            ⟨(f.stalkMap x).hom b, hm b.2⟩
        rw [hsmX, ← map_smul]
        congr 1
        apply Subtype.ext
        exact (map_mul (f.stalkMap x).hom _ _).trans (by rw [hs]; rfl) }
  obtain ⟨EX, hEX⟩ := exists_rationalPoint_tangent_cotangent_linearEquiv k X pX x hrX
  obtain ⟨EY, hEY⟩ := exists_rationalPoint_tangent_cotangent_linearEquiv k Y pY (f x) hrY
  refine ⟨he, EX, EY, U, hEX, hEY, ?_, ?_⟩
  · intro b
    exact ⟨hm b.2, rfl⟩
  · intro θ
    let η := schemeTangentMap k X Y pX pY f hf x he θ
    obtain ⟨hx, D, ⟨hD, hDm⟩, _⟩ := hEX θ
    obtain ⟨hy, E, ⟨hE, hEm⟩, _⟩ := hEY η
    let e : KY ≃+* KX := RingEquiv.ofBijective (f.residueFieldMap x).hom he
    have her (a : k) : e.symm (rX a) = rY a := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (hr a).symm
    have hη : η.val = Spec.map (CommRingCat.ofHom
        (DualNumber.mapRingHom e.symm.toRingHom)) ≫ θ.val ≫ f :=
      Classical.choose_spec (exists_tangentMap_linear k X Y pX pY f hf x he) θ
    have hsharp := sharp_naturality f
      (CommRingCat.ofHom (DualNumber.mapRingHom e.symm.toRingHom))
      θ.val η.val hη x hx hy
    have hcoeff (b : RY) : E b = D ((f.stalkMap x).hom b) := by
      apply hrY.1
      have H := congrArg (fun g : RY ⟶ CommRingCat.of (DualNumber KY) ↦
        (g.hom b).snd) hsharp
      change (((eqToHom (congrArg (fun z : Y ↦ Y.presheaf.stalk z) hy.symm) ≫
        Scheme.stalkClosedPointTo η.val).hom b)).snd =
        (DualNumber.mapRingHom e.symm.toRingHom
          ((eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) hx.symm) ≫
            Scheme.stalkClosedPointTo θ.val).hom ((f.stalkMap x).hom b))).snd at H
      rw [hE b, hD ((f.stalkMap x).hom b)] at H
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add, DualNumber.snd_mapRingHom] at H
      exact H.trans (her (D ((f.stalkMap x).hom b)))
    apply LinearMap.ext
    intro v
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal RY) v
    change EY η ((IsLocalRing.maximalIdeal RY).toCotangent b) =
      EX θ ((IsLocalRing.maximalIdeal RX).toCotangent
        ⟨(f.stalkMap x).hom b, hm b.2⟩)
    rw [hEm, hDm]
    exact hcoeff b

end AlgebraicGeometry
