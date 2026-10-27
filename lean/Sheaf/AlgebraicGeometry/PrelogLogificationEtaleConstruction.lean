/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PrelogLogificationData
import Sheaf.AlgebraicGeometry.PrelogPushoutLogAxiom
import Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension

/-!
# Étale logification with its normalized pushout presentation

Source: ILO VI 1.1 and VIII 3.3.2.
(blueprint: lem-trf-prelog-logification-etale-construction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private noncomputable def quotientPairEquiv {A B : Type u} [CommMonoid A] [CommMonoid B]
    (c : Con A) (q : A →* B) (hq : Function.Surjective q) (hc : Con.ker q = c) :
    c.Quotient ≃* B :=
  hc ▸ Con.quotientKerEquivOfSurjective q hq

private theorem quotientPairEquiv_mk {A B : Type u} [CommMonoid A] [CommMonoid B]
    (c : Con A) (q : A →* B) (hq : Function.Surjective q) (hc : Con.ker q = c)
    (a : A) : quotientPairEquiv c q hq hc (c.mk' a) = q a := by
  subst c
  rfl

/-- The existing étale pushout and extension theorems give a presentation with
exactly the quotient maps used by the comparison theorem.
Source: ILO VI 1.1, VIII 3.3.2.
(blueprint: lem-trf-prelog-logification-etale-construction).

Proof: identify the surjective pair maps of `prelog_pushout_log_axiom` with the
quotients by their stated kernels. Transfer natural maps across these quotient
isomorphisms. The sheafification Hom bijection then gives exactly the presentation
universal property. Finally `prelog_pushout_hom_extension` gives log universality;
its unique compatible map is bundled with its structural equality. -/
theorem prelog_logification_etale_construction (X : Scheme.{u}) [IsLocallyNoetherian X]
    (P : EtalePrelogStructure X) :
    ∃ (L : EtaleLogStructure X)
      (l : PrelogPushoutPresentation X.smallEtaleTopology P.monoidSheaf.obj
        X.etaleStructurePresheaf P.alpha L.monoidSheaf L.alpha),
      l.EtaleUniversal P L := by
  classical
  obtain ⟨Q, q, a, hq, hnat, _, ha, ⟨S, η, hη⟩, hlog⟩ :=
    prelog_pushout_log_axiom.{u, u} X P.monoidSheaf.obj P.alpha
  obtain ⟨α, i, j, hα, ⟨L, hL⟩, _, hi, _⟩ := hlog S η hη
  rcases L with ⟨⟨S', α'⟩, hr, hb⟩
  cases hL
  let L : EtaleLogStructure X := ⟨⟨S, α⟩, hr, hb⟩
  let e (U : X.Etaleᵒᵖ) :
      divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
        (P.alpha.app U).hom.mrangeRestrict ≃* Q.obj U := quotientPairEquiv
    (divisorialChartCongruence (A := X.etaleStructurePresheaf.obj U)
      (P.alpha.app U).hom.mrangeRestrict) (q U)
    (hq U).1 (hq U).2
  have he (U : X.Etaleᵒᵖ) (p : P.monoidSheaf.obj.obj U)
      (b : (X.etaleStructurePresheaf.obj U)ˣ) :
      e U (prelogPairClass _ (P.alpha.app U).hom p b) = q U (p, b) :=
    quotientPairEquiv_mk _ _ _ _ _
  let pairMap (U : X.Etaleᵒᵖ) :
      divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
        (P.alpha.app U).hom.mrangeRestrict →* S.obj.obj U :=
    (η.app U).hom.comp (e U).toMonoidHom
  have hpair (U : X.Etaleᵒᵖ) (p : P.monoidSheaf.obj.obj U)
      (b : (X.etaleStructurePresheaf.obj U)ˣ) :
      pairMap U (prelogPairClass _ (P.alpha.app U).hom p b) = η.app U (q U (p, b)) := by
    change η.app U (e U _) = _
    rw [he]
  have hnatural : PrelogPairNatural P.monoidSheaf.obj X.etaleStructurePresheaf P.alpha
      S.obj pairMap := by
    intro U V f p b
    rw [hpair, hpair]
    exact (ConcreteCategory.congr_hom (η.naturality f) (q U (p, b))).symm.trans
      (congrArg (η.app V) (hnat U V f p b))
  have hstructural : ∀ U p b,
      α.app U (pairMap U (prelogPairClass _ (P.alpha.app U).hom p b)) =
        @id (X.etaleStructurePresheaf.obj U) (P.alpha.app U p) * b.val := by
    intro U p b
    rw [hpair]
    exact (ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) hα) (q U (p, b))).trans
      (ha U p b)
  have huniversal : ∀ (H : Sheaf X.smallEtaleTopology CommMonCat.{u})
      (w : ∀ U : X.Etaleᵒᵖ,
        divisorialChartPushout (A := X.etaleStructurePresheaf.obj U)
          (P.alpha.app U).hom.mrangeRestrict →* H.obj.obj U),
      PrelogPairNatural P.monoidSheaf.obj X.etaleStructurePresheaf P.alpha H.obj w →
      ∃! f : S ⟶ H, ∀ U z, f.hom.app U (pairMap U z) = w U z := by
    intro H w hw
    let v : Q ⟶ H.obj :=
      { app := fun U ↦ CommMonCat.ofHom ((w U).comp (e U).symm.toMonoidHom)
        naturality := by
          intro U V f
          ext x
          obtain ⟨⟨p, b⟩, rfl⟩ := (hq U).1 x
          have hEU := (e U).symm_apply_apply
            (prelogPairClass _ (P.alpha.app U).hom p b)
          have hEV := (e V).symm_apply_apply
            (prelogPairClass _ (P.alpha.app V).hom (P.monoidSheaf.obj.map f p)
              (Units.map (X.etaleStructurePresheaf.map f).hom b))
          rw [he] at hEU hEV
          change w V ((e V).symm (Q.map f (q U (p, b)))) =
            H.obj.map f (w U ((e U).symm (q U (p, b))))
          rw [hnat, hEU, hEV]
          exact (hw U V f p b).symm }
    obtain ⟨f, hf⟩ := (hη H).2 v
    refine ⟨f, ?_, ?_⟩
    · intro U z
      have h := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U) hf) (e U z)
      change f.hom.app U (η.app U (e U z)) = w U ((e U).symm (e U z)) at h
      simpa only [MulEquiv.symm_apply_apply, pairMap, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using h
    · intro g hg
      apply (hη H).1
      rw [hf]
      ext U x
      obtain ⟨z, rfl⟩ := (e U).surjective x
      change g.hom.app U (pairMap U z) = w U ((e U).symm (e U z))
      simpa only [MulEquiv.symm_apply_apply, pairMap, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom] using hg U z
  let l : PrelogPushoutPresentation X.smallEtaleTopology P.monoidSheaf.obj
      X.etaleStructurePresheaf P.alpha L.monoidSheaf L.alpha :=
    { pairMap := pairMap
      naturality := hnatural
      structural := hstructural
      iota := i
      iota_pair := fun U p ↦ (hi U p).trans (hpair U p 1).symm
      universal := huniversal }
  refine ⟨L, l, ?_⟩
  intro K f hf
  obtain ⟨_, _, hext, _⟩ := prelog_pushout_hom_extension X P.monoidSheaf.obj P.alpha
    L l.pairMap l.naturality l.structural l.universal l.iota l.iota_pair K
  obtain ⟨g, ⟨hgα, hgi⟩, hg⟩ := hext f hf
  refine ⟨⟨g, hgα⟩, hgi, ?_⟩
  intro k hk
  apply Subtype.ext
  exact hg k.val ⟨k.property, hk⟩

end AlgebraicGeometry
