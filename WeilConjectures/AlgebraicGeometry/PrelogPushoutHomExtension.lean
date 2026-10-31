/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.LogUnitSectionLift
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.Ring.Adjunctions

/-!
# Extension of prelog maps through the sheafified unit pushout

Source: ILO, Exposé VI 1.1, printed p.69 (étale log conventions), and the explicit
quotient argument of the DAG; Stacks Project, Tag 00YR, assertion (epsilon)
(blueprint: lem-trf-prelog-pushout-hom-extension).

The existing `divisorialChartPushout` is the quotient by the unit relations.
The hypotheses give its natural pair maps, structural formula, and sheafification property.
The unique-extension clause below expresses the bijection by singleton fibres.
The inverse unit maps are characterized by their unique structural preimages on sections.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Compatible prelog maps extend uniquely over the sheafified unit pushout, with
pair formula `v(m) * jK(u)`; every structural log map preserves the unit inclusion.
Source: ILO VI 1.1, printed p.69 (conventions); Stacks Tag 00YR (epsilon).
(blueprint: lem-trf-prelog-pushout-hom-extension).

Proof (the DAG's explicit argument):
1. Ring restrictions preserve units. Naturality of the prelog map preserves the
   generating relations, giving the quotient presheaf and natural inclusions `i`, `j`.
   Each pair is the product of its two inclusions, and the structural formula gives
   `alpha_L i = gamma` and `alpha_L j(u) = u`.
2. The log unit isomorphism of `def-trf-fs-log-blowup` gives the unique lift `jK(u)`
   of a unit, naturally and multiplicatively. Thus `v(e) = jK(gamma(e))` whenever
   `gamma(e)` is a unit.
3. The monoid map `(m,u) ↦ v(m) * jK(u)` respects every generating relation.
   Its kernel congruence therefore contains the generated congruence, so it descends
   to the quotient. Its sectionwise maps are natural by naturality of `v` and `jK`.
4. The Hom bijection of `lem-trf-commutative-monoid-sheafification` extends this
   natural map uniquely to the monoid sheaf `L`.
5. Its structural composite equals `alpha_L` on pairs, hence everywhere by
   sheafification uniqueness with target the multiplicative structure sheaf. This
   target is a sheaf: étale covers are flat and locally finitely presented, hence
   open by Tag 01UA and fpqc on affine opens; functions are maps to `Spec Z[t]`
   by the affine adjunction and descend by fpqc representable descent. Restriction
   of the extension along `i` recovers `v` by the pair formula with unit `1`.
6. Conversely any structural map `f` sends `j(u)` to the unique lift `jK(u)`.
   Thus on pairs it has precisely the formula for the extension of `f i`.
   Sheafification uniqueness recovers `f`, proving both inverse identities and
   automatic preservation of units. -/
theorem prelog_pushout_hom_extension (X : Scheme.{u}) [IsLocallyNoetherian X]
    (M : X.Etaleᵒᵖ ⥤ CommMonCat.{u})
    (γ : M ⟶ X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat)
    (L : EtaleLogStructure X)
    (η : ∀ U : X.Etaleᵒᵖ,
      divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
        (γ.app U).hom.mrangeRestrict →* L.monoidSheaf.obj.obj U)
    (hη : ∀ (U V : X.Etaleᵒᵖ) (r : U ⟶ V) (m : M.obj U)
      (a : (X.etaleStructurePresheaf.obj U)ˣ),
      L.monoidSheaf.obj.map r
          (η U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
            (γ.app U).hom.mrangeRestrict).mk' (m, a))) =
        η V ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj V)
          (γ.app V).hom.mrangeRestrict).mk'
          (M.map r m, Units.map (X.etaleStructurePresheaf.map r).hom a)))
    (hα : ∀ (U : X.Etaleᵒᵖ) (m : M.obj U) (a : (X.etaleStructurePresheaf.obj U)ˣ),
      L.alpha.app U
          (η U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
            (γ.app U).hom.mrangeRestrict).mk' (m, a))) =
        @id (X.etaleStructurePresheaf.obj U) (γ.app U m) * a.val)
    (hsh : ∀ (H : Sheaf X.smallEtaleTopology CommMonCat.{u})
      (w : ∀ U : X.Etaleᵒᵖ,
        divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
          (γ.app U).hom.mrangeRestrict →* H.obj.obj U),
      (∀ (U V : X.Etaleᵒᵖ) (r : U ⟶ V) (m : M.obj U)
        (a : (X.etaleStructurePresheaf.obj U)ˣ),
        H.obj.map r
            (w U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
              (γ.app U).hom.mrangeRestrict).mk' (m, a))) =
          w V ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj V)
            (γ.app V).hom.mrangeRestrict).mk'
            (M.map r m, Units.map (X.etaleStructurePresheaf.map r).hom a))) →
      ∃! f : L.monoidSheaf ⟶ H, ∀ (U : X.Etaleᵒᵖ)
        (z : divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
          (γ.app U).hom.mrangeRestrict), f.hom.app U (η U z) = w U z)
    (i : M ⟶ L.monoidSheaf.obj)
    (hi : ∀ (U : X.Etaleᵒᵖ) (m : M.obj U),
      i.app U m = η U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
        (γ.app U).hom.mrangeRestrict).mk' (m, 1)))
    (K : EtaleLogStructure X) :
    ∃ jK : ∀ U : X.Etaleᵒᵖ, (X.etaleStructurePresheaf.obj U)ˣ →* K.monoidSheaf.obj.obj U,
      (∀ (U : X.Etaleᵒᵖ) (a : (X.etaleStructurePresheaf.obj U)ˣ),
        K.alpha.app U (jK U a) = a.val ∧
          ∀ m : K.monoidSheaf.obj.obj U, K.alpha.app U m = a.val → m = jK U a) ∧
      (∀ (v : M ⟶ K.monoidSheaf.obj), v ≫ K.alpha = γ →
        ∃! f : L.monoidSheaf ⟶ K.monoidSheaf,
          f.hom ≫ K.alpha = L.alpha ∧ i ≫ f.hom = v) ∧
      (∀ (v : M ⟶ K.monoidSheaf.obj), v ≫ K.alpha = γ →
        ∀ (f : L.monoidSheaf ⟶ K.monoidSheaf),
          f.hom ≫ K.alpha = L.alpha → i ≫ f.hom = v →
          ∀ (U : X.Etaleᵒᵖ) (m : M.obj U) (a : (X.etaleStructurePresheaf.obj U)ˣ),
            f.hom.app U
                (η U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
                  (γ.app U).hom.mrangeRestrict).mk' (m, a))) =
              v.app U m * jK U a) ∧
      (∀ (f : L.monoidSheaf ⟶ K.monoidSheaf), f.hom ≫ K.alpha = L.alpha →
        ∀ (U : X.Etaleᵒᵖ) (a : (X.etaleStructurePresheaf.obj U)ˣ),
          f.hom.app U
              (η U ((divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
                (γ.app U).hom.mrangeRestrict).mk' (1, a))) =
            jK U a) := by
  classical
  choose j hj hjuniq using fun U a ↦ K.existsUnique_unit_section_lift U a
  let jK : ∀ U : X.Etaleᵒᵖ,
      (X.etaleStructurePresheaf.obj U)ˣ →* K.monoidSheaf.obj.obj U := fun U ↦
    { toFun := j U
      map_one' := (hjuniq U 1 1 (by
        change K.alpha.app U 1 = 1
        exact map_one _)).symm
      map_mul' := fun a b ↦ (hjuniq U (a * b) (j U a * j U b)
        (by
          change K.alpha.app U (j U a * j U b) = (a * b).val
          rw [map_mul, hj, hj]
          rfl)).symm }
  have hjK (U : X.Etaleᵒᵖ) (a : (X.etaleStructurePresheaf.obj U)ˣ) :
      K.alpha.app U (jK U a) = a.val := hj U a
  have hjKn (U V : X.Etaleᵒᵖ) (r : U ⟶ V)
      (a : (X.etaleStructurePresheaf.obj U)ˣ) :
      K.monoidSheaf.obj.map r (jK U a) =
        jK V (Units.map (X.etaleStructurePresheaf.map r).hom a) := by
    apply hjuniq
    have hn := congrArg (fun k ↦ k (jK U a)) (K.alpha.naturality r)
    change K.alpha.app V (K.monoidSheaf.obj.map r (jK U a)) =
      (X.etaleStructurePresheaf.map r) (K.alpha.app U (jK U a)) at hn
    rw [hn, hjK]
    rfl
  let c (U : X.Etaleᵒᵖ) :=
    divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
      (γ.app U).hom.mrangeRestrict
  have hsplit (U : X.Etaleᵒᵖ) (m : M.obj U)
      (a : (X.etaleStructurePresheaf.obj U)ˣ) :
      η U ((c U).mk' (m, a)) = i.app U m * η U ((c U).mk' (1, a)) := by
    dsimp only [c]
    rw [hi, ← map_mul]
    congr 1
    simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
      (map_mul (c U).mk' (m, 1) (1, a))
  have hunit (f : L.monoidSheaf ⟶ K.monoidSheaf)
      (hf : f.hom ≫ K.alpha = L.alpha) (U : X.Etaleᵒᵖ)
      (a : (X.etaleStructurePresheaf.obj U)ˣ) :
      f.hom.app U (η U ((c U).mk' (1, a))) = jK U a := by
    apply hjuniq
    have he := congrArg (fun k ↦ k.app U (η U ((c U).mk' (1, a)))) hf
    change K.alpha.app U (f.hom.app U (η U ((c U).mk' (1, a)))) = _ at he
    rw [he, hα]
    rw [map_one]
    exact one_mul _
  have hpair (v : M ⟶ K.monoidSheaf.obj) (f : L.monoidSheaf ⟶ K.monoidSheaf)
      (hf : f.hom ≫ K.alpha = L.alpha) (hfi : i ≫ f.hom = v)
      (U : X.Etaleᵒᵖ) (m : M.obj U) (a : (X.etaleStructurePresheaf.obj U)ˣ) :
      f.hom.app U (η U ((c U).mk' (m, a))) = v.app U m * jK U a := by
    rw [hsplit, map_mul, hunit f hf]
    exact congrArg (fun z ↦ z * jK U a) (congrArg (fun k ↦ k.app U m) hfi)
  refine ⟨jK, ?_, ?_, ?_, hunit⟩
  · exact fun U a ↦ ⟨hjK U a, hjuniq U a⟩
  · intro v hv
    have hvα (U : X.Etaleᵒᵖ) (m : M.obj U) :
        K.alpha.app U (v.app U m) = γ.app U m :=
      congrArg (fun k ↦ k.app U m) hv
    let b (U : X.Etaleᵒᵖ) := (v.app U).hom.coprod (jK U)
    have hb (U : X.Etaleᵒᵖ) : c U ≤ Con.ker (b U) := by
      apply Con.conGen_le.mpr
      rintro x y ⟨m, a, ha, rfl, rfl⟩
      change v.app U m * jK U 1 = v.app U 1 * jK U a
      simp only [map_one, mul_one, one_mul]
      apply hjuniq
      exact (hvα U m).trans ha
    let w (U : X.Etaleᵒᵖ) :
        divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
          (γ.app U).hom.mrangeRestrict →* K.monoidSheaf.obj.obj U :=
      (c U).lift (b U) (hb U)
    have hw (U : X.Etaleᵒᵖ) (m : M.obj U)
        (a : (X.etaleStructurePresheaf.obj U)ˣ) :
        w U ((c U).mk' (m, a)) = v.app U m * jK U a := rfl
    have hwn (U V : X.Etaleᵒᵖ) (r : U ⟶ V) (m : M.obj U)
        (a : (X.etaleStructurePresheaf.obj U)ˣ) :
        K.monoidSheaf.obj.map r (w U ((c U).mk' (m, a))) =
          w V ((c V).mk' (M.map r m,
            Units.map (X.etaleStructurePresheaf.map r).hom a)) := by
      rw [hw, hw, map_mul, hjKn]
      have hn := congrArg (fun k ↦ k m) (v.naturality r)
      exact congrArg (fun z ↦ z * _) hn.symm
    obtain ⟨f, hf, hfu⟩ := hsh K.monoidSheaf w hwn
    have hfi : i ≫ f.hom = v := by
      ext U m
      change f.hom.app U (i.app U m) = v.app U m
      rw [hi, hf, hw, map_one, mul_one]
    let O : Sheaf X.smallEtaleTopology CommMonCat.{u} :=
      ⟨X.etaleStructurePresheaf ⋙ forget₂ CommRingCat CommMonCat, by
        exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
          X.isSheaf_etaleStructurePresheaf⟩
    let aO (U : X.Etaleᵒᵖ) := (L.alpha.app U).hom.comp (η U)
    have haOn (U V : X.Etaleᵒᵖ) (r : U ⟶ V) (m : M.obj U)
        (a : (X.etaleStructurePresheaf.obj U)ˣ) :
        O.obj.map r (aO U ((c U).mk' (m, a))) =
          aO V ((c V).mk' (M.map r m,
            Units.map (X.etaleStructurePresheaf.map r).hom a)) := by
      change O.obj.map r (L.alpha.app U (η U ((c U).mk' (m, a)))) = _
      have hn := congrArg (fun k ↦ k (η U ((c U).mk' (m, a))))
        (L.alpha.naturality r)
      change L.alpha.app V (L.monoidSheaf.obj.map r (η U ((c U).mk' (m, a)))) =
        O.obj.map r (L.alpha.app U (η U ((c U).mk' (m, a)))) at hn
      rw [← hn, hη]
      rfl
    obtain ⟨g, hg, hgu⟩ := hsh O aO haOn
    have hαf : f.hom ≫ K.alpha = L.alpha := by
      have he₁ : (ObjectProperty.homMk (f.hom ≫ K.alpha) : L.monoidSheaf ⟶ O) = g := by
        apply hgu
        intro U z
        obtain ⟨⟨m, a⟩, rfl⟩ := (c U).mk'_surjective z
        change K.alpha.app U (f.hom.app U (η U ((c U).mk' (m, a)))) =
          L.alpha.app U (η U ((c U).mk' (m, a)))
        rw [hf, hw, map_mul, hvα, hjK, hα]
        rfl
      have he₂ : (ObjectProperty.homMk L.alpha : L.monoidSheaf ⟶ O) = g := by
        apply hgu
        intro U z
        rfl
      exact congrArg (fun k : L.monoidSheaf ⟶ O ↦ k.hom) (he₁.trans he₂.symm)
    refine ⟨f, ⟨hαf, hfi⟩, ?_⟩
    intro f' hf'
    apply (hfu f' ?_).trans (hfu f hf).symm
    intro U z
    obtain ⟨⟨m, a⟩, rfl⟩ := (c U).mk'_surjective z
    rw [hpair v f' hf'.1 hf'.2, hw]
  · intro v _ f hf hfi
    exact hpair v f hf hfi

end AlgebraicGeometry
