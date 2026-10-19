/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.PurityAffineLineOrientation
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Sheaf.Paper.PurityAffineLineSupportStalkMap

/-! # Supported affine-line classes and the geometric stalk of the Gysin sheaf

Source: blueprint main-20261015, prop-pur-affine-line-orientation-uniqueness,
proof steps 1–3 (blueprint: lem-pur-affine-line-support-stalk).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

local instance (P : PurityFiniteSetting.{u}) :
    PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} P.Coefficient)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

set_option backward.isDefEq.respectTransparency false in
private theorem gysin_stalk_rank_one (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (H : ProEtale.RetractedSupport.EtSheaves P Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj H ≅
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y) :
    Nonempty ((Scheme.pointSmallEtale y).sheafFiber.obj H ≅
      ModuleCat.of P.Coefficient P.Coefficient) := by
  obtain ⟨_, _, ⟨H₀, ⟨e₀⟩, V, hv⟩, _⟩ := P.gysin_structure h Y a
  let ν : ProEtale.RetractedSupport.EtSheaves P Y ⥤
      ProEtale.RetractedSupport.ProSheaves P Y :=
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let t : H ≅ H₀ := ν.preimageIso (e ≪≫ e₀.symm)
  obtain ⟨i, v, hv'⟩ := V.exists_eq (y.base (IsLocalRing.closedPoint Ω))
  have : Etale (V.f i) := V.map_prop i
  obtain ⟨ei⟩ := hv i
  obtain ⟨s⟩ := Etale.nonempty_sheafFiber_iso_of_iso H₀ (V.f i) ei y ⟨v, hv'⟩
  exact ⟨(Scheme.pointSmallEtale y).sheafFiber.mapIso t ≪≫ s⟩

private theorem rank_one_iso_of_unit_in_range {A : Type*} [CommRing A]
    {M N : ModuleCat A} (eM : M ≅ ModuleCat.of A A) (eN : N ≅ ModuleCat.of A A)
    (f : M ⟶ N) (x : M) (hx : eN.hom (f x) = 1) : IsIso f := by
  let g := eM.inv ≫ f ≫ eN.hom
  have hg (z : A) : g z = z * g 1 := by
    change g.hom z = z * g.hom 1
    simpa using g.hom.map_smul z (1 : A)
  have hx' : (eM.hom x) * g 1 = 1 := by
    rw [← hg]
    change eN.hom (f (eM.inv (eM.hom x))) = 1
    simpa using hx
  have hu : IsUnit (g 1) := isUnit_iff_exists_inv.mpr ⟨eM.hom x, by
    simpa only [mul_comm] using hx'⟩
  have hbij : Function.Bijective g := by
    obtain ⟨v, hv⟩ := hu
    simp only [show (g : A → A) = fun z ↦ z * g 1 from funext hg, ← hv]
    exact (Units.mulRight_bijective v)
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hbij
  have : IsIso (eM.inv ≫ f) := IsIso.of_isIso_comp_right _ eN.hom
  exact IsIso.of_isIso_comp_left eM.inv f

set_option backward.isDefEq.respectTransparency false in
/-- The normalized supported pullback, expressed on the etale-origin degree-zero
sheaf, is evaluation of the geometric stalk map at the canonical coefficient unit.
The comparison is for one geometric point and every sheaf morphism into that sheaf;
it does not assert any global injectivity or choose an orientation.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1,
prop-pur-affine-line-orientation-uniqueness.proof.md, steps 1–3; specifically the
canonical identification in step 3 and Milne, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-affine-line-support-stalk).

Proof:
1. The support-to-stalk map lemma constructs a linear map alpha in the opposite
 direction, compatible with evaluation on 1 for every b. The orientation theorem
 supplies a normalized fibre residue rho and a supported pair transport p.
2. The etale model in gysin_structure is locally the constant coefficient line.
 Lift e to an isomorphism between etale models using full faithfulness of comparison.
 Choose a member of its trivializing cover above y. The etale inverse-image/stalk
 comparison identifies the stalk of H with A.
3. Let m0 be the global orientation and D0 its chart. Surjectivity of
 gysinHomToSections produces a morphism m whose section in the specified chart D
 has the same supported class as m0 in D0. Fullness of comparison lifts H0(m) to
 b:A_Y -> H. For x=b_y(1), compatibility of alpha and the normalized orientation
 give rho(alpha(x))=1.
4. Choose the two coefficient-line coordinates. Any linear map between A-lines
 is multiplication by its value at 1. Since its image contains 1, that value is
 a unit in the commutative ring A, so the map is bijective and hence invertible.
 Apply this to alpha. Set gamma=alpha inverse and apply its inverse identity to
 the compatibility equation. All arguments concern the specified point, so no
 connectedness or finite-type condition on Omega is used. -/
theorem affineLine_support_stalk (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (D : OrientationSupportData P h Y)
    (H : ProEtale.RetractedSupport.EtSheaves P Y)
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj H ≅
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω]
    (y : Spec (CommRingCat.of Ω) ⟶ Y)
    (hy : y ≫ a = Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω))) :
    ∃ p : proEtaleSupportHomTransport P (zeroSection Y)
        (zeroSection (Spec (CommRingCat.of Ω))) (AffineSpace.map (ULift.{u} (Fin 1)) y),
    ∃ γ : P.gysinSupport h (Spec (CommRingCat.of Ω)) ≅
        (Scheme.pointSmallEtale y).sheafFiber.obj H,
      ∀ b : P.constantEtale Y ⟶ H,
        γ.hom (P.orientationSupportRestriction h y p
          (D.support.hom (P.gysinEvaluate Y
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).map b ≫
              e.hom)))) =
          ((Scheme.pointSmallEtale y).sheafFiber.map b)
            (((Scheme.pointSmallEtale y).sheafFiberConstantSheafIso
              (ModuleCat.of P.Coefficient P.Coefficient)).inv 1) := by
  classical
  obtain ⟨_, _, _, _, D₀, m₀, _, hfib⟩ := P.affineLine_orientation h Y a
  obtain ⟨_, p, ρ, _, hnorm⟩ := hfib Ω y hy
  obtain ⟨α, hα⟩ := P.affineLine_support_stalk_map h Y a D H e Ω y p
  obtain ⟨eM⟩ := gysin_stalk_rank_one P h Y a H e Ω y
  obtain ⟨_, _, _, hbij, _⟩ := P.gysin_structure h Y a
  obtain ⟨m, hm⟩ := hbij.2
    (D.support.inv (D₀.support.hom (P.gysinHomToSections h Y m₀)))
  let ν : ProEtale.RetractedSupport.EtSheaves P Y ⥤
      ProEtale.RetractedSupport.ProSheaves P Y :=
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let v : P.constant Y ⟶
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).obj (P.gysinValue h Y) :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ProEtale.RetractedSupport.ProSheaves P Y) 0).inv.app (P.constant Y) ≫
      (DerivedCategory.homologyFunctor
        (ProEtale.RetractedSupport.ProSheaves P Y) 0).map m
  obtain ⟨b, hb⟩ := ν.map_surjective (v ≫ e.inv)
  have hb' : ν.map b ≫ e.hom = v := by rw [hb]; simp
  have hv : D.support.hom (P.gysinEvaluate Y (ν.map b ≫ e.hom)) =
      D₀.support.hom (P.gysinHomToSections h Y m₀) := by
    rw [hb']
    change D.support.hom (P.gysinHomToSections h Y m) = _
    rw [hm, Iso.inv_hom_id_apply]
  let Φ := Scheme.pointSmallEtale y
  let x : (Φ.sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)).obj H := (Φ.sheafFiber.map b)
    ((Φ.sheafFiberConstantSheafIso (ModuleCat.of P.Coefficient P.Coefficient)).inv 1)
  have hx : ρ.hom (α x) = 1 := by
    dsimp only [x, Φ]
    rw [hα b, hv]
    exact hnorm
  have : IsIso α := rank_one_iso_of_unit_in_range eM ρ α x hx
  refine ⟨p, (asIso α).symm, ?_⟩
  intro c
  rw [← hα c]
  exact Iso.hom_inv_id_apply (asIso α) _

end WeilConjectures.PurityFiniteSetting
