/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData
import Sheaf.CategoryTheory.Sites.OrientedProductLargeProjections
import Sheaf.CategoryTheory.Sites.OrientedProductLargeLiftExistence
import Sheaf.CategoryTheory.Sites.OrientedProductLargeLiftRigidity
import Sheaf.CategoryTheory.Sites.OrientedProductUniversalComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Sites.Localization

/-! # Oriented triple sites with independent object and morphism universes

Source: ILO Exposé XI §§1.1–1.7
(blueprint: lem-trf-oriented-product-universal).

This generalizes the recorded triple-site construction and its universal statement to sites
with objects in `Type w` and morphisms in `Type v`, such as the small etale sites. Sheaves take
values in `Type (max v w)`, the containing universe of `def-weil-size-convention`. The comma
category and the three generators are unchanged; no homomorphism universe is enlarged. For
`v = w` this is exactly the recorded statement `CategoryTheory.OrientedProduct.universal`.
-/

@[expose] public section
set_option autoImplicit false
universe v w e ve
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OrientedProduct

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]
  (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

private theorem sheaf_isTopos {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) :
    IsGrothendieckTopos.{max v w} (Sheaf J (Type (max v w))) := by
  let e : C ≌ AsSmall.{0} C := AsSmall.equiv
  let K := e.inverse.inducedTopology J
  exact ⟨AsSmall.{0} C, inferInstance, K, ⟨e.sheafCongr J K (Type (max v w))⟩⟩

private noncomputable def firstAdjunction :
    (Comma.fst (𝟭 (C₁ × C₂)) (F.prod' G) ⋙ CategoryTheory.Prod.fst C₁ C₂) ⊣
      largeFirst F G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z U ↦
        { toFun := fun a ↦
            { left := (a, terminal.from _)
              right := terminal.from _
              w := Prod.ext ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
                ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _) }
          invFun := fun a ↦ a.left.1
          left_inv := fun _ ↦ rfl
          right_inv := fun a ↦ by
            apply CommaMorphism.ext
            · exact Prod.ext rfl (terminalIsTerminal.hom_ext _ _)
            · exact terminalIsTerminal.hom_ext _ _ }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun a b ↦ by
        apply CommaMorphism.ext
        · exact Prod.ext rfl (terminalIsTerminal.hom_ext _ _)
        · exact terminalIsTerminal.hom_ext _ _ }

private noncomputable def secondAdjunction :
    (Comma.fst (𝟭 (C₁ × C₂)) (F.prod' G) ⋙ CategoryTheory.Prod.snd C₁ C₂) ⊣
      largeSecond F G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z W ↦
        { toFun := fun a ↦
            { left := (terminal.from _, a)
              right := terminal.from _
              w := Prod.ext ((terminalIsTerminal.isTerminalObj F _).hom_ext _ _)
                ((terminalIsTerminal.isTerminalObj G _).hom_ext _ _) }
          invFun := fun a ↦ a.left.2
          left_inv := fun _ ↦ rfl
          right_inv := fun a ↦ by
            apply CommaMorphism.ext
            · exact Prod.ext (terminalIsTerminal.hom_ext _ _) rfl
            · exact terminalIsTerminal.hom_ext _ _ }
      homEquiv_naturality_left_symm := fun _ _ ↦ rfl
      homEquiv_naturality_right := fun a b ↦ by
        apply CommaMorphism.ext
        · exact Prod.ext (terminalIsTerminal.hom_ext _ _) rfl
        · exact terminalIsTerminal.hom_ext _ _ }

private theorem first_preservesFiniteLimits : PreservesFiniteLimits (largeFirst F G) := by
  have : PreservesLimits (largeFirst F G) := (firstAdjunction F G).rightAdjoint_preservesLimits
  infer_instance

private theorem second_preservesFiniteLimits : PreservesFiniteLimits (largeSecond F G) := by
  have : PreservesLimits (largeSecond F G) := (secondAdjunction F G).rightAdjoint_preservesLimits
  infer_instance

private theorem first_coverPreserving (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) :
    CoverPreserving J₁.toGrothendieck (largeTopology J₁ J₂ F G) (largeFirst F G) := by
  constructor
  intro U S hS
  obtain ⟨R, hR, hRS⟩ := (J₁.mem_toGrothendieck U S).1 hS
  obtain ⟨I, Uᵢ, r, rfl⟩ := R.exists_eq_ofArrows
  apply (largeTopology J₁ J₂ F G).superset_covering
    (Sieve.functorPushforward_monotone _ _ ((Sieve.generate_le_iff _ _).2 hRS))
  rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows]
  apply (largeGenerators J₁ J₂ F G).generate_mem_toGrothendieck
  exact Or.inl ⟨I, fun i ↦ (largeFirst F G).obj (Uᵢ i),
    fun i ↦ (largeFirst F G).map (r i), rfl, Or.inl ⟨hR, fun _ ↦
      ⟨by change IsIso (𝟙 _); infer_instance,
      by change IsIso (𝟙 _); infer_instance⟩⟩⟩

private theorem second_coverPreserving (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) :
    CoverPreserving J₂.toGrothendieck (largeTopology J₁ J₂ F G) (largeSecond F G) := by
  constructor
  intro W S hS
  obtain ⟨R, hR, hRS⟩ := (J₂.mem_toGrothendieck W S).1 hS
  obtain ⟨I, Wᵢ, r, rfl⟩ := R.exists_eq_ofArrows
  apply (largeTopology J₁ J₂ F G).superset_covering
    (Sieve.functorPushforward_monotone _ _ ((Sieve.generate_le_iff _ _).2 hRS))
  rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows]
  apply (largeGenerators J₁ J₂ F G).generate_mem_toGrothendieck
  exact Or.inl ⟨I, fun i ↦ (largeSecond F G).obj (Wᵢ i),
    fun i ↦ (largeSecond F G).map (r i), rfl, Or.inr ⟨hR, fun _ ↦
      ⟨by change IsIso (𝟙 _); infer_instance,
      by change IsIso (𝟙 _); infer_instance⟩⟩⟩

omit [PreservesFiniteLimits G] in
private theorem type_c_equalize {Z' Z T : largeTriples F G} (r : Z' ⟶ Z)
    [IsIso r.left.1]
    (hr : IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right))
    (p q : T ⟶ Z') (hpq : p ≫ r = q ≫ r) :
    ∃ (T' : largeTriples F G) (s : T' ⟶ T),
      IsIso s.left.1 ∧
      IsPullback s.left.2 T'.hom.2 T.hom.2 (G.map s.right) ∧ s ≫ p = s ≫ q := by
  have hleft : p.left.1 = q.left.1 := by
    apply (cancel_mono r.left.1).1
    exact congrArg (fun a ↦ a.left.1) hpq
  have hF : T.hom.1 ≫ F.map p.right = T.hom.1 ≫ F.map q.right := by
    have hp : p.left.1 ≫ Z'.hom.1 = T.hom.1 ≫ F.map p.right :=
      congrArg (fun a ↦ a.1) p.w
    have hq : q.left.1 ≫ Z'.hom.1 = T.hom.1 ≫ F.map q.right :=
      congrArg (fun a ↦ a.1) q.w
    rw [← hp, ← hq, hleft]
  let V := equalizer p.right q.right
  let a : T.left.1 ⟶ F.obj V :=
    equalizer.lift T.hom.1 hF ≫ inv (equalizerComparison p.right q.right F)
  have ha : a ≫ F.map (equalizer.ι p.right q.right) = T.hom.1 := by
    dsimp [a]
    rw [← equalizerComparison_comp_π, Category.assoc, IsIso.inv_hom_id_assoc,
      equalizer.lift_ι]
  let T' : largeTriples F G :=
    ⟨(T.left.1, pullback T.hom.2 (G.map (equalizer.ι p.right q.right))), V,
      (a, pullback.snd _ _)⟩
  let s : T' ⟶ T :=
    ⟨(𝟙 _, pullback.fst _ _), equalizer.ι p.right q.right,
      Prod.ext (by change 𝟙 _ ≫ T.hom.1 = a ≫ F.map _; simpa using ha.symm)
        pullback.condition⟩
  refine ⟨T', s, inferInstance, IsPullback.of_hasPullback _ _, ?_⟩
  apply CommaMorphism.ext
  · apply Prod.ext
    · change (𝟙 _ ≫ p.left.1) = (𝟙 _ ≫ q.left.1)
      simpa only [Category.id_comp] using hleft
    · apply hr.hom_ext
      · have h := congrArg (fun a ↦ a.left.2) hpq
        simpa [s, Category.assoc] using congrArg (fun a ↦ s.left.2 ≫ a) h
      · have hp : p.left.2 ≫ Z'.hom.2 = T.hom.2 ≫ G.map p.right :=
          congrArg (fun a ↦ a.2) p.w
        have hq : q.left.2 ≫ Z'.hom.2 = T.hom.2 ≫ G.map q.right :=
          congrArg (fun a ↦ a.2) q.w
        change (s.left.2 ≫ p.left.2) ≫ Z'.hom.2 = (s.left.2 ≫ q.left.2) ≫ Z'.hom.2
        simp only [Category.assoc]
        rw [hp, hq, ← Category.assoc, ← Category.assoc]
        have hs := congrArg (fun a ↦ a.2) s.w
        change s.left.2 ≫ T.hom.2 = T'.hom.2 ≫ G.map s.right at hs
        rw [hs]
        simp only [Category.assoc, ← G.map_comp]
        congr 2
        exact equalizer.condition p.right q.right
  · exact equalizer.condition p.right q.right

omit [PreservesFiniteLimits G] in
private theorem type_c_restriction_bijective (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    (M : Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
    {Z' Z : largeTriples F G} (r : Z' ⟶ Z) [IsIso r.left.1]
    (hr : IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right)) :
    Function.Bijective (M.obj.map r.op) := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).1 M.property
  have hs {A B : largeTriples F G} (s : A ⟶ B) [IsIso s.left.1]
      (hs : IsPullback s.left.2 A.hom.2 B.hom.2 (G.map s.right)) :
      Presieve.IsSheafFor M.obj (Presieve.singleton s) :=
    hM.isSheafFor_of_mem_precoverage (J := largeGenerators J₁ J₂ F G)
      (Or.inr ⟨A, s, rfl, inferInstance, hs⟩)
  refine ⟨(Presieve.isSeparatedFor_singleton).1 (hs r hr).isSeparatedFor, ?_⟩
  intro x
  obtain ⟨y, hy, _⟩ := (Presieve.isSheafFor_singleton.1 (hs r hr)) x (by
    intro T p q hpq
    obtain ⟨T', s, hi, hpb, heq⟩ := type_c_equalize F G r hr p q hpq
    have := hi
    apply (Presieve.isSeparatedFor_singleton.1 (hs s hpb).isSeparatedFor)
    simpa only [← Functor.map_comp_apply, ← op_comp] using
      congrArg (fun a ↦ M.obj.map a.op x) heq)
  exact ⟨y, hy⟩

omit [PreservesFiniteLimits G] in
private theorem type_c_associated_isIso (J₁ : Pretopology C₁) (J₂ : Pretopology C₂)
    {Z' Z : largeTriples F G} (r : Z' ⟶ Z) [IsIso r.left.1]
    (hr : IsPullback r.left.2 Z'.hom.2 Z.hom.2 (G.map r.right)) :
    IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map r) := by
  change IsIso ((presheafToSheaf (largeTopology J₁ J₂ F G) (Type (max v w))).map
    (uliftYoneda.{max v w}.map r))
  apply (GrothendieckTopology.W_iff _ (uliftYoneda.{max v w}.map r)).1
  intro P hP
  let M : Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)) := ⟨P, hP⟩
  have h := type_c_restriction_bijective F G J₁ J₂ M r hr
  have hnat (a : uliftYoneda.{max v w}.obj Z ⟶ P) :
      uliftYonedaEquiv.{max v w} (uliftYoneda.{max v w}.map r ≫ a) =
        P.map r.op (uliftYonedaEquiv.{max v w} a) :=
    (uliftYonedaEquiv_naturality a r.op).symm
  constructor
  · intro a b hab
    apply uliftYonedaEquiv.{max v w}.injective
    apply h.1
    exact (hnat a).symm.trans ((congrArg uliftYonedaEquiv.{max v w} hab).trans (hnat b))
  · intro a
    obtain ⟨x, hx⟩ := h.2 (uliftYonedaEquiv.{max v w} a)
    refine ⟨uliftYonedaEquiv.{max v w}.symm x, ?_⟩
    apply uliftYonedaEquiv.{max v w}.injective
    change uliftYonedaEquiv.{max v w}
      (uliftYoneda.{max v w}.map r ≫ uliftYonedaEquiv.{max v w}.symm x) = _
    rw [hnat, Equiv.apply_symm_apply]
    exact hx

/-- The triple-site construction on sites with independent object and morphism universes has its
stated projections, canonical orientation, universal compatible lift, and inverse-image pullback
formula; topoi are tested in the containing universe `max v w`. For `v = w` this is exactly
`CategoryTheory.OrientedProduct.universal`.

Source: ILO Exposé XI §§1.1, 1.3, Theorem 1.4, §1.6 formula (1.a), and Definition 1.7
(blueprint: lem-trf-oriented-product-universal).

Proof: The two projection functors are right adjoints to the component functors, and
carry covering families to generators. The continuous site pullback constructs their
geometric morphisms and the comparison on associated representables. For type-(c)
arrows, local equalizers and singleton descent make restriction bijective; the
sheafification adjunction then makes their associated arrows invertible. On middle
triples this defines the orientation, whose mate is computed using adjunction and Yoneda.
The separate existence and rigidity theorems give the universal compatible lift and
its specified pullback formula. Finally the two universal properties give comparison
morphisms in both directions; uniqueness identifies their composites with identities.
This proves the site-independence equivalence and its projection-compatible uniqueness.
-/
theorem universalWithLargeSites (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    [F.IsContinuous K.toGrothendieck J₁.toGrothendieck]
    [G.IsContinuous K.toGrothendieck J₂.toGrothendieck]
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck) :
    ∃ (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
        (Sheaf J₁.toGrothendieck (Type (max v w))))
      (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
        (Sheaf J₂.toGrothendieck (Type (max v w))))
      (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
        largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
      (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
        largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
      (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct),
      IsUniversal.{max v w, e, ve} f g p₁ p₂ τ ∧
      LargeHasLiftFormula.{v, w, e, ve} F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ ∧
      (∀ (Q : Type (max v w + 1)) [Category.{max v w} Q], IsGrothendieckTopos.{max v w} Q →
        ∀ (q₁ : GeometricMorphism Q (Sheaf J₁.toGrothendieck (Type (max v w))))
          (q₂ : GeometricMorphism Q (Sheaf J₂.toGrothendieck (Type (max v w))))
          (σ : (q₂.comp g).direct ⟶ (q₁.comp f).direct),
          IsUniversal.{max v w, max v w + 1, max v w} f g q₁ q₂ σ →
          ∃ (h : GeometricMorphism Q (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
            (α : (h.comp p₁).direct ≅ q₁.direct) (β : (h.comp p₂).direct ≅ q₂.direct),
            paste f g p₁ p₂ τ h q₁ q₂ α β = σ ∧ h.direct.IsEquivalence ∧
            ∀ (h' : GeometricMorphism Q (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
              (α' : (h'.comp p₁).direct ≅ q₁.direct)
              (β' : (h'.comp p₂).direct ≅ q₂.direct),
              paste f g p₁ p₂ τ h' q₁ q₂ α' β' = σ →
              ∃! γ : h.direct ≅ h'.direct,
                Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
                Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β) ∧
      ∀ V : D,
        ∃ (_ : IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map
          (largeToFirst F G (largeMiddle F G V)))),
        (GeometricMorphism.inverseMate τ).app ((largeAssociated K.toGrothendieck).obj V) =
          p₁.inverse.map (ηF.hom.app V) ≫ π₁.hom.app (F.obj V) ≫
          inv ((largeAssociated (largeTopology J₁ J₂ F G)).map
            (largeToFirst F G (largeMiddle F G V))) ≫
          (largeAssociated (largeTopology J₁ J₂ F G)).map
            (largeToSecond F G (largeMiddle F G V)) ≫
          π₂.inv.app (G.obj V) ≫ p₂.inverse.map (ηG.inv.app V) := by
  have hc (V : D) : IsIso ((largeAssociated (largeTopology J₁ J₂ F G)).map
      (largeToFirst F G (largeMiddle F G V))) := by
    have : IsIso (largeToFirst F G (largeMiddle F G V)).left.1 := by
      change IsIso (𝟙 _)
      infer_instance
    have : IsIso (largeMiddle F G V).hom.2 := by
      change IsIso (𝟙 _)
      infer_instance
    have : IsIso ((largeFirst F G).obj (largeMiddle F G V).left.1).hom.2 := by
      change IsIso (inv (terminalComparison G))
      infer_instance
    apply type_c_associated_isIso F G J₁ J₂
    apply IsPullback.of_vert_isIso
    exact ⟨congrArg (fun a ↦ a.2) (largeToFirst F G (largeMiddle F G V)).w⟩
  let := first_preservesFiniteLimits F G
  let := second_preservesFiniteLimits F G
  let : RepresentablyFlat (largeFirst F G) := flat_of_preservesFiniteLimits _
  let : RepresentablyFlat (largeSecond F G) := flat_of_preservesFiniteLimits _
  let : (largeFirst F G).IsContinuous J₁.toGrothendieck
      (largeTopology J₁ J₂ F G) :=
    Functor.isContinuous_iff_coverPreserving.mpr (first_coverPreserving F G J₁ J₂)
  let : (largeSecond F G).IsContinuous J₂.toGrothendieck
      (largeTopology J₁ J₂ F G) :=
    Functor.isContinuous_iff_coverPreserving.mpr (second_coverPreserving F G J₁ J₂)
  let p₁ := largeSiteMorphism J₁.toGrothendieck (largeTopology J₁ J₂ F G) (largeFirst F G)
  let p₂ := largeSiteMorphism J₂.toGrothendieck (largeTopology J₁ J₂ F G) (largeSecond F G)
  let π₁ := largeAssociatedComparison J₁.toGrothendieck
    (largeTopology J₁ J₂ F G) (largeFirst F G)
  let π₂ := largeAssociatedComparison J₂.toGrothendieck
    (largeTopology J₁ J₂ F G) (largeSecond F G)
  obtain ⟨τ, hτ⟩ := largeOrientationExists F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ hc
  have hu : IsUniversal.{max v w, e, ve} f g p₁ p₂ τ := by
    intro E _ hE a b t
    obtain ⟨h, α, β, hh⟩ :=
      largeCompatibleLiftExists F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ hτ E hE a b t
    refine ⟨h, α, β, hh, ?_⟩
    intro h' α' β' hh'
    exact (largeCompatibleLiftRigidity F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ hτ).2
      E hE a b t h h' α β α' β' hh hh'
  have hu' : IsUniversal.{max v w, max v w + 1, max v w} f g p₁ p₂ τ := by
    intro E _ hE a b t
    obtain ⟨h, α, β, hh⟩ :=
      largeCompatibleLiftExists F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ hτ E hE a b t
    refine ⟨h, α, β, hh, ?_⟩
    intro h' α' β' hh'
    exact (largeCompatibleLiftRigidity F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ hτ).2
      E hE a b t h h' α β α' β' hh hh'
  refine ⟨p₁, p₂, π₁, π₂, τ, hu, ?_, ?_, hτ⟩
  · exact (largeCompatibleLiftRigidity F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ hτ).1
  · intro Q _ hQ q₁ q₂ σ hq
    exact universalComparison f g p₁ p₂ τ q₁ q₂ σ
      (sheaf_isTopos (largeTopology J₁ J₂ F G)) hQ hu' hq

end CategoryTheory.OrientedProduct
