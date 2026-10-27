/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.ZariskiLogStructure
public import Sheaf.AlgebraicGeometry.MonoidChartCharacteristicStalks
import Sheaf.AlgebraicGeometry.MonoidChartCharacteristicFanMap
import Mathlib.CategoryTheory.Limits.Final
import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections
import Sheaf.TraceFormula.FsFaceSharpening

/-!
# Sharpening a fixed fs log chart

Source: ILO, Exposé VIII 3.1.2--3.1.10, pp.98--100, 3.3.2--3.3.4(ii), p.107,
and 3.3.12, p.108 (blueprint: lem-trf-monoid-chart-characteristic-fan).

We use multiplicative monoids. The final open subscheme represents global étale
sections. Stalk bijectivity of the specified sheaf map expresses that its adjoint
inverse-image map is an isomorphism. All characteristic comparisons are normalized
on actual log-section germs, including after restriction to any open subset.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem sharp_face_stalk_properties
    {Q M : Type u} [CommMonoid Q] [CommMonoid M]
    (hQ : IsFineSaturatedMonoid Q) (F : Submonoid Q)
    (hF : ∀ a b : Q, a * b ∈ F → a ∈ F ∧ b ∈ F)
    (e : M ≃* Associates (Algebra.faceLocalization Q F)) :
    (MonoidHom.mrange (Algebra.GrothendieckGroup.of (M := M))).PowSaturated ∧
      ∀ (g : Algebra.GrothendieckGroup M) (n : ℕ), 0 < n → g ^ n = 1 → g = 1 := by
  classical
  let R := Associates (Algebra.faceLocalization Q F)
  let E : Algebra.GrothendieckGroup M ≃* Algebra.GrothendieckGroup R :=
    (Localization.monoidOf (⊤ : Submonoid M)).mulEquivOfMulEquiv
      (Localization.monoidOf (⊤ : Submonoid R)) (j := e) (by
        ext r
        constructor
        · intro _; trivial
        · intro _
          obtain ⟨m, rfl⟩ := e.surjective r
          exact ⟨m, Submonoid.mem_top _, rfl⟩)
  have E_of (m : M) : E (Algebra.GrothendieckGroup.of m) =
      Algebra.GrothendieckGroup.of (e m) :=
    Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq _ _ _
  obtain ⟨_, _, hR, _, φ, _, _, _, n, ⟨B⟩⟩ := face_sharpening Q hQ F hF
  constructor
  · intro k g hg
    by_cases hk : k = 0
    · exact Or.inl hk
    · right
      obtain ⟨m, hm⟩ := hg
      obtain ⟨r, hr⟩ := hR.2.2 (E g) k (Nat.pos_of_ne_zero hk) ⟨e m, by
        rw [← E_of, hm, map_pow]⟩
      refine ⟨e.symm r, E.injective ?_⟩
      rw [E_of, e.apply_symm_apply, hr]
  · let : Module.Free ℤ (Additive (Algebra.GrothendieckGroup R)) :=
      Module.Free.of_basis B
    let : IsAddTorsionFree (Additive (Algebra.GrothendieckGroup R)) :=
      IsAddTorsionFree.of_isTorsionFree ℤ _
    intro g k hk hg
    have hpow : (E g) ^ k = 1 := by rw [← map_pow, hg, map_one]
    have hzero : k • Additive.ofMul (E g) = 0 := hpow
    have heq : Additive.ofMul (E g) = 0 := by
      apply (nsmul_right_injective (Nat.ne_of_gt hk))
      simpa using hzero
    exact E.injective (by simpa using heq)

private theorem open_restriction_stalk_bijective
    (S : SheafedSpace CommMonCat.{u}) (W : Opens S) (x : W) :
    Function.Bijective (FineFan.stalkMap (S.ofRestrict W.isOpenEmbedding) x) := by
  let h := W.isOpenEmbedding
  let := CategoryTheory.Functor.initial_of_adjunction (h.adjunctionNhds x)
  let T := h.functor.op ⋙ S.presheaf
  let E : Limits.colimit ((OpenNhds.inclusion x).op ⋙ T) ≅
      Limits.colimit ((OpenNhds.inclusion x.val).op ⋙ S.presheaf) :=
    CategoryTheory.Functor.Final.colimitIso (h.functorNhds x).op
      ((OpenNhds.inclusion x.val).op ⋙ S.presheaf)
  let k : Limits.colimit ((OpenNhds.inclusion x.val).op ⋙ S.presheaf) ⟶
      Limits.colimit ((OpenNhds.inclusion x).op ⋙ T) := by
    refine Limits.colim.map (Functor.whiskerLeft (OpenNhds.inclusion x.val).op
      (S.toPresheafedSpace.ofRestrict h).c) ≫ ?_
    refine ?_ ≫ Limits.colimit.pre ((OpenNhds.inclusion x).op ⋙ T)
      (OpenNhds.map W.inclusion' x).op
    exact Limits.colim.map (Functor.whiskerRight
      (NatTrans.op (OpenNhds.inclusionMapIso W.inclusion' x).inv) T)
  have hi : E.inv = k := by
    refine Limits.colimit.hom_ext fun V ↦ ?_
    induction V with | op V => ?_
    let i : (h.functorNhds x).obj ((OpenNhds.map W.inclusion' x).obj V) ⟶ V :=
      homOfLE (Set.image_preimage_subset W.inclusion' _)
    erw [Iso.comp_inv_eq]
    dsimp only [k]
    rw [Limits.colimit.ι_map_assoc, Limits.colimit.ι_map_assoc]
    simp_rw [Category.assoc]
    erw [Limits.colimit.ι_pre_assoc]
    dsimp only [E, CategoryTheory.Functor.Final.colimitIso, asIso_hom]
    erw [Limits.colimit.ι_pre ((OpenNhds.inclusion x.val).op ⋙ S.presheaf)
      (h.functorNhds x).op]
    erw [← S.presheaf.map_comp_assoc]
    exact (Limits.colimit.w ((OpenNhds.inclusion x.val).op ⋙ S.presheaf) i.op).symm
  change Function.Bijective k
  rw [← hi]
  exact ConcreteCategory.bijective_of_isIso _

/-- A global fs chart sharpens to a local characteristic fan chart. The point formula
specifies the complement of the unit face. The numerator equations specify the fan
map and both face-localization identifications. The equation for every local log
section specifies the canonical Zariski-to-geometric characteristic comparison.
The last two clauses give restriction compatibility and saturated torsion-free
stalks at every prime of the fan, including primes outside the chart image.

Source: ILO VIII 3.1.2--3.1.10, 3.3.2--3.3.4(ii), 3.3.12
(blueprint: lem-trf-monoid-chart-characteristic-fan).

Proof:
1. Apply lem-trf-zariski-prelog-logification-comparison to the constant Zariski
   monoid sheaf of Q and the structural chart. The inverse-image adjunction and
   sheafification identify its maps to any étale log structure with compatible
   maps from Q into global sections. By lem-trf-associated-log-universal-stalks
   the given chart has the same universal property. The unique extensions in
   both directions are inverse; obtain Z, its chart, and its association with M.
2. The unit preimage is a face: if a product is invertible, so are its factors.
   Its complement is a proper prime monoid ideal, including the empty prime when
   all chart elements map to units. By lem-trf-fs-face-sharpening its localization
   has unit group E^gp, and its sharpening is saturated with torsion-free completion.
   Apply this at every prime, not only at primes in the image of the scheme.
3. In the associated-log pushout the characteristic class of [q,a] maps to q
   modulo E^gp; the inverse sends q/e to the class of [q,beta(e)^(-1)]. The
   pushout relation kills exactly E, hence E^gp after localization. These are
   inverse formulas on both ordinary and geometric stalks. The change-of-site
   comparison fixes q and extends a, hence induces the identity on the quotient.
4. The inverse image of D(a) is the open unit locus of beta(a). On that open the
   characteristic class of a is one. Localization therefore gives a map from
   Q[a^(-1)] killing its units. Use lem-trf-affine-fan-localization-sections to
   obtain maps from the sharp sections of D(a). They agree on overlaps because
   they agree on Q, so glue to the stated sheafed-space morphism.
5. Its stalk maps are exactly the identifications of Step 3. Thus they are
   bijective and local. Germwise lifting, uniqueness and gluing show that the
   adjoint inverse-image sheaf map is an isomorphism. Both spaces have sharp stalks.
6. Restricting to an open leaves the unit face and all formulas unchanged.
   The associated-log identifications restrict by the comparison theorem. The
   characteristic-stalk maps commute with open inclusion because both send
   each representative [q,a] to the same class q. The displayed open-stalk
   equations express this compatibility for all elements and all log sections.
-/
theorem monoid_chart_characteristic_fan
    (X : FineSaturatedLogScheme.{u}) (Q : Type u) [CommMonoid Q]
    (hQ : IsFineSaturatedMonoid Q)
    (c : Q →* X.logStructure.monoidSheaf.obj.obj
      (op (Scheme.Etale.mk (⊤ : X.scheme.Opens).ι)))
    (hc : X.logStructure.IsChart (Scheme.Etale.mk (⊤ : X.scheme.Opens).ι) c) :
    ∃ (Z : ZariskiLogStructure X.scheme)
      (e : Z.toZariskiPrelogStructure.EtaleMap X.logStructure)
      (z : Q →* Z.monoidSheaf.obj.obj (op ⊤))
      (f : Z.characteristicMonoidalSpace ⟶ FineFan.affine Q)
      (a : ∀ x : X.scheme,
        FineFan.stalk Z.characteristicMonoidalSpace.presheaf x ≃*
          Associates (Algebra.faceLocalization Q (X.logStructure.globalChartUnitFace c x)))
      (b : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
        X.logStructure.characteristic t ≃*
          Associates (Algebra.faceLocalization Q
            (X.logStructure.globalChartUnitFace c (t default)))),
      e.IsAssociation ∧ Z.IsChart ⊤ z ∧ (e.sectionMap ⊤).comp z = c ∧
      FineFan.IsLocalMorphism f ∧
      (∀ x : X.scheme, FineFan.IsSharp
        (FineFan.stalk Z.characteristicMonoidalSpace.presheaf x)) ∧
      (∀ (x : X.scheme) (q : Q),
        q ∈ (f.hom.base x).carrier ↔ q ∉ X.logStructure.globalChartUnitFace c x) ∧
      (∀ x : X.scheme, Function.Bijective (FineFan.stalkMap f x)) ∧
      (∀ (x : X.scheme) (q : Q),
        FineFan.stalkMap f x (FineFan.affineGerm (f.hom.base x) q) =
          FineFan.germ Z.characteristicMonoidalSpace.presheaf ⊤ x (by trivial)
            (Z.characteristicSection ⊤ (z q))) ∧
      (∀ (x : X.scheme) (q : Q),
        ∃ r : Algebra.faceLocalization Q (X.logStructure.globalChartUnitFace c x),
          r.val = Algebra.GrothendieckGroup.of q ∧
          a x (FineFan.germ Z.characteristicMonoidalSpace.presheaf ⊤ x (by trivial)
            (Z.characteristicSection ⊤ (z q))) = Associates.mk r) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
        (V : X.scheme.Opens)
        (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.ι))
        (hx : t default ∈ V) (s : Z.monoidSheaf.obj.obj (op V)),
        b Ω t (Associates.mk (X.logStructure.toEtalePrelogStructure.germ t
          (Scheme.Etale.mk V.ι) w (e.sectionMap V s))) =
          a (t default) (FineFan.germ Z.characteristicMonoidalSpace.presheaf
            V (t default) hx (Z.characteristicSection V s))) ∧
      (∀ W : X.scheme.Opens,
        ∃ aW : ∀ (x : X.scheme) (hx : x ∈ W),
            FineFan.stalk
              (Z.characteristicMonoidalSpace.restrict W.isOpenEmbedding).presheaf ⟨x, hx⟩ ≃*
                Associates (Algebra.faceLocalization Q
                  (X.logStructure.globalChartUnitFace c x)),
          (∀ (x : X.scheme) (hx : x ∈ W)
            (m : FineFan.stalk Z.characteristicMonoidalSpace.presheaf x),
            aW x hx (FineFan.stalkMap
              (Z.characteristicMonoidalSpace.ofRestrict W.isOpenEmbedding) ⟨x, hx⟩ m) = a x m) ∧
          ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
            (hw : t default ∈ W) (V : X.scheme.Opens) (_hV : V ≤ W)
            (w : (Scheme.pointSmallEtale t).fiber.obj (Scheme.Etale.mk V.ι))
            (hv : t default ∈ V) (s : Z.monoidSheaf.obj.obj (op V)),
            b Ω t (Associates.mk (X.logStructure.toEtalePrelogStructure.germ t
              (Scheme.Etale.mk V.ι) w (e.sectionMap V s))) =
              aW (t default) hw (FineFan.stalkMap
                (Z.characteristicMonoidalSpace.ofRestrict W.isOpenEmbedding) ⟨t default, hw⟩
                (FineFan.germ Z.characteristicMonoidalSpace.presheaf
                  V (t default) hv (Z.characteristicSection V s)))) ∧
      (∀ p : FineFan.MonoidPrime Q,
        (MonoidHom.mrange (Algebra.GrothendieckGroup.of
          (M := FineFan.stalk (FineFan.affine Q).presheaf p))).PowSaturated ∧
        ∀ (g : Algebra.GrothendieckGroup (FineFan.stalk (FineFan.affine Q).presheaf p))
          (n : ℕ), 0 < n → g ^ n = 1 → g = 1) := by
  classical
  obtain ⟨Z, e, z, a, b, he, hz, hez, ha, hb⟩ :=
    chart_characteristic_stalk_comparison X Q hQ c hc
  obtain ⟨f, hp, hf, hfg⟩ := chart_characteristic_fan_map X Q hQ c Z e z hz hez a ha
  refine ⟨Z, e, z, f, a, b, he, hz, hez, ?_, ?_, hp, hf, hfg, ha, hb, ?_, ?_⟩
  · intro x
    let E := MulEquiv.ofBijective (FineFan.stalkMap f x).hom (hf x)
    exact isLocalHom_of_leftInverse E.symm.toMonoidHom E.left_inv
  · intro x m hm
    apply (a x).injective
    rw [map_one]
    exact (Associates.isUnit_iff_eq_one _).mp (hm.map (a x))
  · intro W
    have hj (x : X.scheme) (hx : x ∈ W) :
        Function.Bijective (FineFan.stalkMap
          (Z.characteristicMonoidalSpace.ofRestrict W.isOpenEmbedding) ⟨x, hx⟩) := by
      exact open_restriction_stalk_bijective Z.characteristicMonoidalSpace W ⟨x, hx⟩
    let aW (x : X.scheme) (hx : x ∈ W) :=
      (MulEquiv.ofBijective (FineFan.stalkMap
        (Z.characteristicMonoidalSpace.ofRestrict W.isOpenEmbedding) ⟨x, hx⟩).hom
          (hj x hx)).symm.trans (a x)
    have hW (x : X.scheme) (hx : x ∈ W)
        (m : FineFan.stalk Z.characteristicMonoidalSpace.presheaf x) :
        aW x hx (FineFan.stalkMap
          (Z.characteristicMonoidalSpace.ofRestrict W.isOpenEmbedding) ⟨x, hx⟩ m) = a x m := by
      exact congrArg (a x) (MulEquiv.symm_apply_apply _ m)
    refine ⟨aW, hW, ?_⟩
    intro Ω _ _ t hw V _hV w hv s
    rw [hW]
    exact hb Ω t V w hv s
  · obtain ⟨_, A, _, _, _⟩ := FineFan.affineFan_localization_sections Q ⟨⟨hQ.1⟩, hQ.2.1⟩
    intro p
    let F : Submonoid Q :=
      { carrier := {q | q ∉ p.carrier}
        one_mem' := by
          intro h
          apply p.proper
          exact Set.eq_univ_of_forall fun q ↦ by
            simpa using SemigroupIdeal.mul_mem p.toSubMulAction q h
        mul_mem' := fun ha hb ↦ p.complement_mul _ _ ha hb }
    have hF (a b : Q) (hab : a * b ∈ F) : a ∈ F ∧ b ∈ F := by
      change a * b ∉ p.carrier at hab
      change a ∉ p.carrier ∧ b ∉ p.carrier
      constructor
      · intro ha
        apply hab
        rw [mul_comm]
        exact SemigroupIdeal.mul_mem p.toSubMulAction b ha
      · intro hb
        exact hab (SemigroupIdeal.mul_mem p.toSubMulAction a hb)
    have hcl : Submonoid.closure {q : Q | q ∉ p.carrier} = F := by
      change Submonoid.closure (F : Set Q) = F
      exact Submonoid.closure_eq F
    have ep : FineFan.stalk (FineFan.affine Q).presheaf p ≃*
        Associates (Algebra.faceLocalization Q F) := by
      have ep := A p
      rw [hcl] at ep
      exact ep
    exact sharp_face_stalk_properties hQ F hF ep

end AlgebraicGeometry
