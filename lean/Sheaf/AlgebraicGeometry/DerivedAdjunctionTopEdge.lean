/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdgeData
import Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdgeLocalCalculation

/-! # Top cohomology of the derived adjunction
The normalized local edge is identified with the counit on an upper truncation.
Adjunction naturality then gives its action on every bounded-above source.
Source: Stacks, derived.tex, Tags 08J5 and 05TC; cohomology.tex, Tags 079W and 0BKJ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry

private theorem transpose_top_naturality
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (L : D ⥤ E) (R : E ⥤ D) (l : A ⥤ B) (r : B ⥤ A)
    (adj : L ⊣ R) (a : l ⊣ r) (H : D ⥤ A) (H' : E ⥤ B)
    {C P : D} {K : E} (f : C ⟶ P) (d : L.obj P ⟶ K)
    (kC : H'.obj (L.obj C) ⟶ l.obj (H.obj C))
    (kP : H'.obj (L.obj P) ⟶ l.obj (H.obj P)) [IsIso kC] [IsIso kP]
    (hk : H'.map (L.map f) ≫ kP = kC ≫ l.map (H.map f)) :
    a.homEquiv _ _ (inv kC ≫ H'.map ((adj.homEquiv _ _).symm
        (f ≫ adj.homEquiv _ _ d))) =
      H.map f ≫ a.homEquiv _ _ (inv kP ≫ H'.map d) := by
  have hi : inv kC ≫ H'.map (L.map f) = l.map (H.map f) ≫ inv kP := by
    apply (cancel_mono kP).1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc] using congrArg (fun z ↦ inv kC ≫ z) hk
  rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, H'.map_comp]
  rw [← Category.assoc, hi, Category.assoc, a.homEquiv_naturality_left]

private theorem sheafification_edge_ext
    {V : Type*} [Category V] (J : GrothendieckTopology V)
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (P : Vᵒᵖ ⥤ AddCommGrpCat.{u}) (M N : Sheaf J AddCommGrpCat.{u})
    (e : (presheafToSheaf J AddCommGrpCat.{u}).obj P ≅ M)
    (a b : M ⟶ N)
    (h : (sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P ≫
        (sheafToPresheaf J AddCommGrpCat.{u}).map e.hom ≫
        (sheafToPresheaf J AddCommGrpCat.{u}).map a =
      (sheafificationAdjunction J AddCommGrpCat.{u}).unit.app P ≫
        (sheafToPresheaf J AddCommGrpCat.{u}).map e.hom ≫
        (sheafToPresheaf J AddCommGrpCat.{u}).map b) : a = b := by
  apply (cancel_epi e.hom).1
  apply ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] using h

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The pinned derived adjunction induces the ordinary tensor-pullback adjunction in top
cohomology, with precisely the local-class edge e. The existential unique map is the
sheafification of Θλ, expressed by its universal defining equation on every open.
Source: Stacks, cohomology.tex, Tags 0BKJ, 0D5X and 079W; derived.tex, Tags 08J5, 0149,
06XS. The adjunct equality is the agent refinement in the DAG
(blueprint: lem-weil-pbc-derived-adjunction-top-edge).

Proof: Put P = τ≤q Rg_*K with inclusion i : P → Rg_*K; H^q(i) is invertible. Take for e
the truncated-counit edge: H^q(i)⁻¹ followed by the ordinary adjunct of κ_P⁻¹ H^q(d₀), where
d₀ is the derived transpose of i. Its local-class equation is
`topEdgeTruncatedCounit_localClass`. For d : Lg*C → K with C ≤ q, its adjunct factors as
f ≫ i through P; adjunction naturality writes d = Lg*(f) ≫ d₀, and naturality of κ with
ordinary adjunction naturality give the displayed equality after cancelling H^q(i).
Uniqueness: Θ is the sheafification unit followed by an isomorphism, so two maps agreeing
after Θ on every open are equal; forgetting module structure is faithful. The lower bound
on K is not used.
-/
theorem derivedAdjunction_topEdge {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE q)
    (K : schemeDerivedCategory T) (_hK : ∃ n : ℤ, K.IsGE n) :
    ∃! e : (DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
          ((schemeDerivedDirectImage g).obj K) ⟶
        (Scheme.Modules.pushforward g).obj
          ((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj K),
      (∀ V : (Opens S)ᵒᵖ,
        (RingedSpace.topEdgeLocalClass S.toRingedSpace q
          ((schemeDerivedDirectImage g).obj K)).app V ≫
          ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map e).hom.app V =
        (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
          (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V) ∧
      (∀ d : (derivedPullback g).obj C ⟶ K,
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv _ _
          (topEdgePullbackInverse g q C hC ≫
            (DerivedCategory.homologyFunctor.{w, u, u + 1}
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map d) =
          (DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
              ((@pinnedDerivedAdjunction.{u, w} _
                (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
                _ _ g).homEquiv C K d) ≫ e) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let HS := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let HT := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let P := (t.truncLE q).obj ((schemeDerivedDirectImage g).obj K)
  let i := (t.truncLEι q).app ((schemeDerivedDirectImage g).obj K)
  let adj := @pinnedDerivedAdjunction.{u, w} _
    (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f) _ _ g
  let a := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let d₀ := (adj.homEquiv P K).symm i
  have hP : P.IsLE q := by dsimp [P]; infer_instance
  have hi : IsIso (HS.map i) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ (q + 1) q (by omega)
  have := hi
  let e := topEdgeTruncatedCounit g q K
  have he := topEdgeTruncatedCounit_localClass g q K
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro d
    have := hC
    let f := t.liftTruncLE (adj.homEquiv C K d) q
    have hf : f ≫ i = adj.homEquiv C K d := t.liftTruncLE_ι _ q
    have hn := (derivedPullback_topCohomology g q C hC).choose_spec.2.2.1 P hP f
    have := (derivedPullback_topCohomology g q C hC).choose_spec.2.1
    have := (derivedPullback_topCohomology g q P hP).choose_spec.2.1
    have hh := transpose_top_naturality (derivedPullback g) (schemeDerivedDirectImage g)
      (Scheme.Modules.tensorPullback g) (Scheme.Modules.pushforward g) adj a HS HT f d₀
      (derivedPullbackTopCohomology g q C hC)
      (derivedPullbackTopCohomology g q P hP) hn
    have hfd : f ≫ adj.homEquiv P K d₀ = adj.homEquiv C K d := by
      simpa only [d₀, Equiv.apply_symm_apply] using hf
    rw [hfd, Equiv.symm_apply_apply] at hh
    change a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q C hC) ≫ HT.map d) =
      HS.map (adj.homEquiv C K d) ≫ e
    rw [hh, ← hf, HS.map_comp]
    change HS.map f ≫ a.homEquiv _ _
        (inv (derivedPullbackTopCohomology g q P hP) ≫ HT.map d₀) =
      (HS.map f ≫ HS.map i) ≫ (inv (HS.map i) ≫
        a.homEquiv _ _ (inv (derivedPullbackTopCohomology g q P hP) ≫ HT.map d₀))
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  · intro e' he'
    apply (SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map_injective
    apply sheafification_edge_ext (Opens.grothendieckTopology S)
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).obj
        ((schemeDerivedDirectImage g).obj K)) _ _
      (RingedSpace.localHypercohomologySheafificationAt q
        ((schemeDerivedDirectImage g).obj K))
    apply NatTrans.ext
    funext V
    exact (he'.1 V).trans (he V).symm

end AlgebraicGeometry
