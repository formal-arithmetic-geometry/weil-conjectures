/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.Sites.ToposComplementFactorization
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.TraceFormula.EtaleClosedComplementSets
public import Mathlib.CategoryTheory.Sites.Subcanonical
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Closed complementary subtopoi and supported constant-coefficient modules

Source: Stacks Project, Sites, Tags 08LY, 08LZ, 08M0, 08M1 and 00YV;
Modules on Sites, Tag 08M3; Etale Cohomology, Tag 04CA(1)
(blueprint: lem-trf-oriented-closed-base-localization).

The three parts of the statement are packaged below. Small-site presentations in the
module part allow use of the recorded category of modules over a constant ring sheaf.
Its inverse images are the normalized lifts of the actual geometric adjunctions, so the
unit and counit in the conclusion are their actual adjunction maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v uH vH uG vG t

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ClosedBaseLocalization

/-- The construction and universal properties of the closed complement of `U`.
The `baseChange` field spells out its inverse-image property: a morphism into the new
closed complement exists exactly when its composite factors through the old one, and
right whiskering is bijective on all direct-image natural transformations.

Source: Stacks, Sites, Tags 08LY, 08LZ, 08M0, 08M1
(blueprint: lem-trf-oriented-closed-base-localization). -/
structure ComplementData {E : Type u} [Category.{v} E] [HasBinaryProducts E] (U : E) where
  closedTopos : IsGrothendieckTopos.{w} (closedComplementObjects U).FullSubcategory
  openTopos : IsGrothendieckTopos.{w} (Over U)
  i : GeometricMorphism (closedComplementObjects U).FullSubcategory E
  j : GeometricMorphism (Over U) E
  inclusion : i.direct ≅ (closedComplementObjects U).ι
  openInverse : j.inverse ≅ Over.star U
  fullyFaithful : i.direct.FullyFaithful
  factorization : ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
    (∀ a : GeometricMorphism H E,
      (∃ b : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
        Nonempty ((b.comp i).direct ≅ a.direct)) ↔
      Nonempty (IsInitial (a.inverse.obj U))) ∧
    (∀ b d : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
      Function.Bijective (fun τ : b.direct ⟶ d.direct ↦ Functor.whiskerRight τ i.direct))
  baseChange : ∀ (H : Type uH) [Category.{vH} H], IsGrothendieckTopos.{w} H →
    ∀ a : GeometricMorphism H E, ∃ products : HasBinaryProducts H,
      IsGrothendieckTopos.{w}
        (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory ∧
      ∃ k : GeometricMorphism
          (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory H,
        Nonempty (k.direct ≅
          (@closedComplementObjects H _ products (a.inverse.obj U)).ι) ∧
        Nonempty k.direct.FullyFaithful ∧
        ∃ r : GeometricMorphism
            (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory
            (closedComplementObjects U).FullSubcategory,
          Nonempty ((r.comp i).direct ≅ (k.comp a).direct) ∧
          ∀ (G : Type uG) [Category.{vG} G], IsGrothendieckTopos.{w} G →
            (∀ b : GeometricMorphism G H,
              (∃ d : GeometricMorphism G
                  (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory,
                Nonempty ((d.comp k).direct ≅ b.direct)) ↔
              (∃ c : GeometricMorphism G (closedComplementObjects U).FullSubcategory,
                Nonempty ((c.comp i).direct ≅ (b.comp a).direct))) ∧
            (∀ d e : GeometricMorphism G
                (@closedComplementObjects H _ products (a.inverse.obj U)).FullSubcategory,
              Function.Bijective
                (fun τ : d.direct ⟶ e.direct ↦ Functor.whiskerRight τ k.direct))

/-- The module clauses on any small-site presentations of the closed and open embeddings.
The hypotheses on `i` and `j` say precisely that these are the closed complement and the
open slice of `U`. The supplied lifts are those of the recorded constant-module interface,
including its scalar normalization and compatibility with the original adjunction unit.
Exactness of `i_*` is expressed by preservation of finite limits and finite colimits.

Source: Stacks, Sites, 00YV and 08M1; Modules on Sites, 08M3
(blueprint: lem-trf-oriented-closed-base-localization). -/
def ModuleAssertion {C D O : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory O]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology O)
    (U : Sheaf J (Type w))
    (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w))) : Prop :=
  Nonempty i.direct.FullyFaithful →
  (∀ H : Sheaf J (Type w), i.direct.essImage H ↔ closedComplementObjects U H) →
  (∃ e : Sheaf L (Type w) ≌ Over U, Nonempty (j.inverse ⋙ e.functor ≅ Over.star U)) →
  ∀ (Λ : Type w) [CommRing Λ]
    (di : ConstantLeftModuleInverseImageLift J K Λ i.inverse i.direct i.adj i.leftExact)
    (dj : ConstantLeftModuleInverseImageLift J L Λ j.inverse j.direct j.adj j.leftExact),
    PreservesFiniteLimits di.moduleDirect ∧ PreservesFiniteColimits di.moduleDirect ∧
    di.moduleDirect.Full ∧ di.moduleDirect.Faithful ∧
    (∀ N : ConstantLeftModuleInverseImage.Modules K Λ, IsIso (di.moduleAdj.counit.app N)) ∧
    (∀ M : ConstantLeftModuleInverseImage.Modules J Λ,
      di.moduleDirect.essImage M ↔ IsZero (dj.moduleFunctor.obj M)) ∧
    (∀ M : ConstantLeftModuleInverseImage.Modules J Λ,
      IsZero (dj.moduleFunctor.obj M) → IsIso (di.moduleAdj.unit.app M))

/-- The subterminal represented by the complementary open of a scheme closed immersion.
We use the existing sheafified Yoneda functor, lifted to the universe of small etale
sheaves; the small etale topology is subcanonical, so this is the represented sheaf.

Source: Stacks, Etale Cohomology, 04CA(1); Sites, 08LY
(blueprint: lem-trf-oriented-closed-base-localization). -/
def representedOpenComplement {F S : AlgebraicGeometry.Scheme.{t}} (k : F ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion k] : Sheaf S.smallEtaleTopology (Type (t + 1)) :=
  (presheafToSheaf S.smallEtaleTopology (Type (t + 1))).obj
    (uliftYoneda.{t + 1}.obj (AlgebraicGeometry.Scheme.Etale.mk k.openComplement.ι))

end CategoryTheory.ClosedBaseLocalization

namespace CategoryTheory

private theorem inverse_subterminal {E : Type u} {H : Type uH}
    [Category.{v} E] [Category.{vH} H] [HasBinaryProducts E]
    (a : GeometricMorphism H E) (U : E) (hU : IsSubterminal U) :
    IsSubterminal (a.inverse.obj U) := by
  let := a.leftExact
  let := hU.isIso_diag
  have he : a.inverse.map (diag U) ≫ prodComparison a.inverse U U =
      diag (a.inverse.obj U) := by
    apply prod.hom_ext <;> simp [← Functor.map_comp]
  have : IsIso (diag (a.inverse.obj U)) := by
    rw [← he]
    infer_instance
  exact isSubterminal_of_isIso_diag

private theorem closed_factorization_criterion {E : Type u} [Category.{v} E]
    [HasBinaryProducts E] (hE : IsGrothendieckTopos.{w} E) (U : E)
    (hU : IsSubterminal U)
    (i : GeometricMorphism (closedComplementObjects U).FullSubcategory E)
    (ei : i.direct ≅ (closedComplementObjects U).ι)
    {H : Type uH} [Category.{vH} H] (hH : IsGrothendieckTopos.{w} H)
    (a : GeometricMorphism H E) :
    (∃ b : GeometricMorphism H (closedComplementObjects U).FullSubcategory,
      Nonempty ((b.comp i).direct ≅ a.direct)) ↔
      Nonempty (IsInitial (a.inverse.obj U)) := by
  obtain ⟨products, _, _, j, k, _, ⟨ek⟩, _, _, hf⟩ :=
    topos_complement_factorization hE U hU
  let e : k.direct ≅ i.direct := ek ≪≫ ei.symm
  constructor
  · rintro ⟨b, ⟨eb⟩⟩
    exact ((hf H hH).1.1 a).mp ⟨b, ⟨Functor.isoWhiskerLeft b.direct e ≪≫ eb⟩⟩
  · intro ha
    obtain ⟨b, ⟨eb⟩⟩ := ((hf H hH).1.1 a).mpr ha
    exact ⟨b, ⟨Functor.isoWhiskerLeft b.direct e.symm ≪≫ eb⟩⟩

private theorem module_unit_isIso_iff
    {C D : Type w} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (Λ : Type w) [CommRing Λ]
    (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (d : ConstantLeftModuleInverseImageLift J K Λ i.inverse i.direct i.adj i.leftExact)
    (M : ConstantLeftModuleInverseImage.Modules J Λ) :
    IsIso (d.moduleAdj.unit.app M) ↔
      IsIso (i.adj.unit.app ((ConstantLeftModuleInverseImage.W J Λ).obj M)) := by
  open ConstantLeftModuleInverseImage in
    have h₁ : IsIso ((V J Λ).map (d.moduleAdj.unit.app M)) ↔
        IsIso (d.abelianAdj.unit.app ((V J Λ).obj M)) := by
      rw [← d.unit_compatibility M]
      simp only [isIso_comp_right_iff]
    have h₂ : IsIso ((U J).map (d.abelianAdj.unit.app ((V J Λ).obj M))) ↔
        IsIso (i.adj.unit.app ((W J Λ).obj M)) := by
      change IsIso ((U J).map (d.abelianAdj.unit.app ((V J Λ).obj M))) ↔
        IsIso (i.adj.unit.app ((U J).obj ((V J Λ).obj M)))
      rw [← d.abelian_unit ((V J Λ).obj M)]
      simp only [isIso_comp_right_iff]
    exact (isIso_iff_of_reflects_iso _ (V J Λ)).symm.trans
      (h₁.trans ((isIso_iff_of_reflects_iso _ (U J)).symm.trans h₂))

private theorem module_zero_iff_terminal
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] (M : ConstantLeftModuleInverseImage.Modules J Λ) :
    IsZero M ↔ Nonempty (IsTerminal ((ConstantLeftModuleInverseImage.W J Λ).obj M)) := by
  constructor
  · intro h
    exact ⟨h.isTerminal.isTerminalObj (ConstantLeftModuleInverseImage.W J Λ) _⟩
  · rintro ⟨h⟩
    exact (h.isTerminalOfObj (ConstantLeftModuleInverseImage.W J Λ) M).isZero

private theorem star_terminal_iff {E : Type u} [Category.{v} E] [HasBinaryProducts E]
    (U A : E) : Nonempty (IsTerminal ((Over.star U).obj A)) ↔
      closedComplementObjects U A := by
  let f : (Over.star U).obj A ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from _
  have hf : f.left = (prod.fst : U ⨯ A ⟶ U) := by
    dsimp only [f]
    rw [Over.mkIdTerminal_from_left]
    simp [Over.star_obj_hom]
  constructor
  · rintro ⟨h⟩
    have : IsIso f := isIso_of_isTerminal h Over.mkIdTerminal f
    have : IsIso f.left := inferInstance
    simpa only [closedComplementObjects, ← hf] using this
  · intro h
    have : IsIso f.left := by simpa only [hf, closedComplementObjects] using h
    have : IsIso ((Over.forget U).map f) := by
      change IsIso f.left
      assumption
    have : IsIso f := isIso_of_reflects_iso f (Over.forget U)
    exact ⟨Over.mkIdTerminal.ofIso (asIso f).symm⟩

private theorem module_open_zero_iff
    {C O : Type w} [SmallCategory C] [SmallCategory O]
    (J : GrothendieckTopology C) (L : GrothendieckTopology O)
    (U : Sheaf J (Type w))
    (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w)))
    (e : Sheaf L (Type w) ≌ Over U) (he : j.inverse ⋙ e.functor ≅ Over.star U)
    (Λ : Type w) [CommRing Λ]
    (d : ConstantLeftModuleInverseImageLift J L Λ j.inverse j.direct j.adj j.leftExact)
    (M : ConstantLeftModuleInverseImage.Modules J Λ) :
    IsZero (d.moduleFunctor.obj M) ↔
      closedComplementObjects U ((ConstantLeftModuleInverseImage.W J Λ).obj M) := by
  rw [module_zero_iff_terminal]
  constructor
  · rintro ⟨h⟩
    apply (star_terminal_iff U _).mp
    exact ⟨(h.ofIso (d.moduleSetIso.app M)).isTerminalObj e.functor _ |>.ofIso (he.app _)⟩
  · intro h
    obtain ⟨h⟩ := (star_terminal_iff U _).mpr h
    exact ⟨((h.ofIso (he.app _).symm).isTerminalOfObj e.functor _).ofIso
      (d.moduleSetIso.app M).symm⟩

private theorem closed_module_assertion
    {C D O : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory O]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology O)
    (U : Sheaf J (Type w))
    (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w))) :
    ClosedBaseLocalization.ModuleAssertion J K L U i j := by
  open ConstantLeftModuleInverseImage in
    intro hfi himage hopen Λ _ di dj
    obtain ⟨fi⟩ := hfi
    let := fi.full
    let := fi.faithful
    obtain ⟨e, ⟨he⟩⟩ := hopen
    let eD : di.moduleDirect ⋙ W J Λ ≅ W K Λ ⋙ i.direct :=
      Functor.isoWhiskerRight di.directUnderlyingIso (ConstantLeftModuleInverseImage.U J) ≪≫
        Functor.isoWhiskerLeft (V K Λ) di.abelianDirectSetIso
    let : (di.moduleDirect ⋙ W J Λ).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_iso eD.symm
    let : di.moduleDirect.ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_comp di.moduleDirect (W J Λ)
    have hu (M : Modules J Λ) : IsIso (di.moduleAdj.unit.app M) ↔
        IsZero (dj.moduleFunctor.obj M) :=
      (module_unit_isIso_iff J K Λ i di M).trans
        (i.adj.isIso_unit_app_iff_mem_essImage.trans
          ((himage _).trans (module_open_zero_iff J L U j e he Λ dj M).symm))
    have hz (N : Modules K Λ) : IsZero (dj.moduleFunctor.obj (di.moduleDirect.obj N)) := by
      apply (module_open_zero_iff J L U j e he Λ dj _).mpr
      exact (himage _).mp ⟨(W K Λ).obj N, ⟨(eD.app N).symm⟩⟩
    have hc (N : Modules K Λ) : IsIso (di.moduleAdj.counit.app N) := by
      have := (hu _).mpr (hz N)
      have : IsIso (di.moduleDirect.map (di.moduleAdj.counit.app N)) :=
        isIso_of_hom_comp_eq_id (di.moduleAdj.unit.app (di.moduleDirect.obj N))
          (di.moduleAdj.right_triangle_components N)
      exact isIso_of_reflects_iso _ di.moduleDirect
    have : IsIso di.moduleAdj.counit := NatIso.isIso_of_isIso_app _
    let fm := di.moduleAdj.fullyFaithfulROfIsIsoCounit
    let := fm.full
    let := fm.faithful
    have himage (M : Modules J Λ) :
        di.moduleDirect.essImage M ↔ IsZero (dj.moduleFunctor.obj M) :=
      di.moduleAdj.isIso_unit_app_iff_mem_essImage.symm.trans (hu M)
    let : PreservesLimits di.moduleDirect := di.moduleAdj.rightAdjoint_preservesLimits
    have hcolim : PreservesFiniteColimits di.moduleDirect := by
      let := dj.preservesFiniteColimits
      refine ⟨fun A _ _ ↦ ⟨fun {F} ↦ ?_⟩⟩
      have hzero : IsZero ((F ⋙ di.moduleDirect) ⋙ dj.moduleFunctor) :=
        (Functor.isZero_iff _).mpr (fun a ↦ hz (F.obj a))
      have hQ : IsZero (dj.moduleFunctor.obj (colimit (F ⋙ di.moduleDirect))) :=
        (isColimitOfPreserves dj.moduleFunctor (colimit.isColimit _)).isZero_pt hzero
      obtain ⟨N, ⟨eN⟩⟩ := (himage _).mpr hQ
      let : CreatesColimit F di.moduleDirect := createsColimitOfFullyFaithfulOfIso N eN
      infer_instance
    exact ⟨inferInstance, hcolim, inferInstance, inferInstance, hc, himage,
      fun M hM ↦ (hu M).mpr hM⟩

private theorem fst_bijective_iff (A B : Type w) :
    Function.Bijective (_root_.Prod.fst : A × B → A) ↔
      (Nonempty A → Nonempty (Unique B)) := by
  classical
  constructor
  · intro h ⟨a⟩
    obtain ⟨⟨_, b⟩, _⟩ := h.surjective a
    exact ⟨{ default := b, uniq := fun b' ↦
      congrArg _root_.Prod.snd (h.injective (show (a, b').1 = (a, b).1 from rfl)) }⟩
  · intro h
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ haa
      obtain ⟨hB⟩ := h ⟨a⟩
      exact _root_.Prod.ext haa (hB.uniq b |>.trans (hB.uniq b').symm)
    · intro a
      obtain ⟨hB⟩ := h ⟨a⟩
      exact ⟨(a, hB.default), rfl⟩

private theorem closed_iff_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (U H : Sheaf J (Type w)) :
    closedComplementObjects U H ↔ ∀ V : C,
      Nonempty (U.obj.obj (Opposite.op V)) → Nonempty (Unique (H.obj.obj (Opposite.op V))) := by
  let p : U ⨯ H ⟶ U := prod.fst
  have he (V : C) :
      IsIso (p.hom.app (Opposite.op V)) ↔
        (Nonempty (U.obj.obj (Opposite.op V)) →
          Nonempty (Unique (H.obj.obj (Opposite.op V)))) := by
    let ev : Sheaf J (Type w) ⥤ Type w :=
      sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj (Opposite.op V)
    change IsIso (ev.map p) ↔ _
    rw [← prodComparison_fst ev U H, isIso_comp_left_iff]
    rw [← Types.binaryProductIso_hom_comp_fst, isIso_comp_left_iff,
      isIso_iff_bijective]
    exact fst_bijective_iff _ _
  change IsIso p ↔ _
  rw [← isIso_iff_of_reflects_iso p (sheafToPresheaf J (Type w)),
    NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h V ↦ (he V).mp (h (Opposite.op V)),
    fun h V ↦ (he V.unop).mpr (h V.unop)⟩

private theorem terminal_iff_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (H : Sheaf J (Type w)) :
    Nonempty (IsTerminal H) ↔
      ∀ V : C, Nonempty (Unique (H.obj.obj (Opposite.op V))) := by
  classical
  constructor
  · rintro ⟨h⟩ V
    exact ⟨Types.isTerminalEquivUnique _
      ((h.isTerminalObj (sheafToPresheaf J (Type w)) _).isTerminalObj
        ((evaluation Cᵒᵖ (Type w)).obj (Opposite.op V)) _)⟩
  · intro h
    exact ⟨(Functor.isTerminal (fun V ↦
      (Types.isTerminalEquivUnique _).symm (Classical.choice (h V.unop)))).isTerminalOfObj
        (sheafToPresheaf J (Type w)) H⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def represented_open_iso {F S : AlgebraicGeometry.Scheme.{t}} (k : F ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion k] :
    ClosedBaseLocalization.representedOpenComplement k ≅
      S.smallEtaleTopology.uliftYoneda.{t + 1}.obj
        (AlgebraicGeometry.Scheme.Etale.mk k.openComplement.ι) :=
  asIso ((sheafificationAdjunction S.smallEtaleTopology (Type (t + 1))).counit.app
    (S.smallEtaleTopology.uliftYoneda.{t + 1}.obj
      (AlgebraicGeometry.Scheme.Etale.mk k.openComplement.ι)))

private theorem represented_open_subterminal {F S : AlgebraicGeometry.Scheme.{t}}
    (k : F ⟶ S) [AlgebraicGeometry.IsClosedImmersion k] :
    IsSubterminal (ClosedBaseLocalization.representedOpenComplement k) := by
  intro Z f g
  apply (cancel_mono (represented_open_iso k).hom).mp
  ext V x
  let W := AlgebraicGeometry.Scheme.Etale.mk k.openComplement.ι
  have : Subsingleton (V.unop ⟶ W) := ⟨fun a b ↦ by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono k.openComplement.ι).mp
    exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm⟩
  apply ULift.ext
  exact Subsingleton.elim (α := V.unop ⟶ W) _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_open_support_iff {F S : AlgebraicGeometry.Scheme.{t}}
    (k : F ⟶ S) [AlgebraicGeometry.IsClosedImmersion k]
    (H : Sheaf S.smallEtaleTopology (Type (t + 1))) :
    closedComplementObjects (ClosedBaseLocalization.representedOpenComplement k) H ↔
      Nonempty (IsTerminal
        ((AlgebraicGeometry.etaleSetInverseImage k.openComplement.ι).obj H)) := by
  classical
  let j := k.openComplement.ι
  let W := AlgebraicGeometry.Scheme.Etale.mk j
  let m := MorphismProperty.Over.map (P := @AlgebraicGeometry.Etale) ⊤
    (inferInstance : AlgebraicGeometry.Etale j)
  let : m.IsContinuous k.openComplement.toScheme.smallEtaleTopology S.smallEtaleTopology :=
    AlgebraicGeometry.Scheme.isContinuous_overMap
      (inferInstance : AlgebraicGeometry.Etale j) le_rfl
  let : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j).IsContinuous
      S.smallEtaleTopology k.openComplement.toScheme.smallEtaleTopology :=
    AlgebraicGeometry.Scheme.isContinuous_overPullback _ _ le_rfl j
  let R := m.sheafPushforwardContinuous (Type (t + 1))
    k.openComplement.toScheme.smallEtaleTopology S.smallEtaleTopology
  let adj : R ⊣ AlgebraicGeometry.etaleSetDirectImage j :=
    (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ j
      (inferInstance : AlgebraicGeometry.Etale j) _root_.trivial).sheafPushforwardContinuous
        k.openComplement.toScheme.smallEtaleTopology S.smallEtaleTopology
  let ei := (AlgebraicGeometry.etaleSetAdjunction j).leftAdjointUniq adj
  have hR : Nonempty (IsTerminal (R.obj H)) ↔
      Nonempty (IsTerminal ((AlgebraicGeometry.etaleSetInverseImage j).obj H)) :=
    ⟨fun ⟨h⟩ ↦ ⟨h.ofIso (ei.app H).symm⟩, fun ⟨h⟩ ↦ ⟨h.ofIso (ei.app H)⟩⟩
  apply Iff.trans _ hR
  rw [closed_iff_sections, terminal_iff_sections]
  constructor
  · intro h T
    apply h (m.obj T)
    refine ⟨(represented_open_iso k).inv.hom.app _ ?_⟩
    exact ⟨MorphismProperty.Over.homMk T.hom rfl⟩
  · intro h V ⟨x⟩
    let f : V ⟶ W := ((represented_open_iso k).hom.hom.app (Opposite.op V) x).down
    let T := (AlgebraicGeometry.Scheme.Etale.overToEtale W).obj (Over.mk f)
    let e : m.obj T ≅ V := MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ V.hom = f.left ≫ j
      have hw := (MorphismProperty.Over.w f).symm
      change V.hom = f.left ≫ j at hw
      simpa only [Category.id_comp] using hw)
    obtain ⟨hT⟩ := h T
    exact ⟨(H.obj.mapIso e.op).toEquiv.symm.uniqueCongr hT⟩

private theorem equivalence_of_essImage
    {A : Type uH} {B : Type u} [Category.{vH} A] [Category.{v} B]
    (R : A ⥤ B) [R.Full] [R.Faithful] (P : ObjectProperty B)
    (h : ∀ Y, R.essImage Y ↔ P Y) :
    ∃ e : A ≌ P.FullSubcategory, Nonempty (e.functor ⋙ P.ι ≅ R) := by
  classical
  let hR : ∀ X, P (R.obj X) := fun X ↦ (h _).mp (R.obj_mem_essImage X)
  let T := P.lift R hR
  let : T.Full := by change (P.lift R hR).Full; infer_instance
  let : T.Faithful := by change (P.lift R hR).Faithful; infer_instance
  let : T.EssSurj := ⟨fun Y ↦ by
    obtain ⟨X, ⟨e⟩⟩ := (h Y.obj).mpr Y.property
    exact ⟨X, ⟨P.isoMk e⟩⟩⟩
  let : T.IsEquivalence := {}
  exact ⟨T.asEquivalence, ⟨P.liftCompιIso R hR⟩⟩

private theorem closed_complement_data {E : Type u} [Category.{v} E]
    (hE : IsGrothendieckTopos.{w} E) (U : E) (hU : IsSubterminal U) :
    ∃ products : HasBinaryProducts E,
      Nonempty (@ClosedBaseLocalization.ComplementData.{w, u, v, uH, vH, uG, vG}
        E _ products U) := by
  classical
  obtain ⟨products, hZ, hO, j, i, ⟨ej⟩, ⟨ei⟩, _, ⟨fi⟩, hf⟩ :=
    topos_complement_factorization hE U hU
  let := products
  refine ⟨products, ⟨{
    closedTopos := hZ
    openTopos := hO
    i := i
    j := j
    inclusion := ei
    openInverse := ej
    fullyFaithful := fi
    factorization := fun H _ hH ↦ (hf H hH).1
    baseChange := ?_ }⟩⟩
  intro H _ hH a
  obtain ⟨hproducts, hZH, _, jH, k, _, ⟨ek⟩, _, ⟨fk⟩, hfH⟩ :=
    topos_complement_factorization hH (a.inverse.obj U) (inverse_subterminal a U hU)
  let := hproducts
  have hk : Nonempty (IsInitial (k.inverse.obj (a.inverse.obj U))) :=
    ((hfH _ hZH).1.1 k).mp
      ⟨{ inverse := 𝟭 _, direct := 𝟭 _, adj := Adjunction.id, leftExact := inferInstance },
        ⟨Functor.leftUnitor k.direct⟩⟩
  obtain ⟨r, ⟨er⟩⟩ :=
    (closed_factorization_criterion hE U hU i ei hZH (k.comp a)).mpr hk
  refine ⟨hproducts, hZH, k, ⟨ek⟩, ⟨fk⟩, r, ⟨er⟩, ?_⟩
  intro G _ hG
  constructor
  · intro b
    exact (closed_factorization_criterion hH (a.inverse.obj U)
      (inverse_subterminal a U hU) k ek hG b).trans
      (closed_factorization_criterion hE U hU i ei hG (b.comp a)).symm
  · intro d e
    exact (fk.whiskeringRight G).map_bijective _ _

/-- Closed complementary subtopoi, their universal inverse-image property, exact fully
faithful direct image of constant-ring modules, and the small etale scheme example.

Source: Stacks, Sites, 08LY, 08LZ, 08M0, 08M1, 00YV; Modules on Sites, 08M3;
Etale Cohomology, 04CA(1)
(blueprint: lem-trf-oriented-closed-base-localization).

Proof plan (the three steps of the DAG node):
1. Apply `lem-trf-topos-complement-factorization` to `U` to obtain the full subcategory,
   geometric embedding with inclusion direct image, open slice, and universal property
   including all direct-image 2-morphisms. Apply the same construction to `a.inverse.obj U`.
   The factorization criterion for a composite is initiality of `b.inverse.obj
   (a.inverse.obj U)`. It gives the comparison square and the inverse-image universal
   property in `ComplementData.baseChange`, including 2-morphisms by full faithfulness.
2. The normalized lifts compare the actual module adjunction units with the set-sheaf
   units through conservative forgetful functors. Thus invertibility of a module unit
   is equivalent to the underlying set sheaf lying in the closed essential image,
   equivalently vanishing under open module restriction. The direct image reflects
   isomorphisms; its counit is invertible by the triangle identity, giving full
   faithfulness and the supported essential image. It preserves limits as a right
   adjoint. Ambient finite colimits of closed-image modules are supported, since open
   restriction preserves finite colimits and kills the diagram. Full faithfulness
   creates these colimits, proving their preservation by closed direct image.
3. Apply `lem-trf-etale-closed-complement-sets` to the scheme closed immersion.
   Subcanonicity identifies the sheafified lifted representable of the open complement
   with its represented sheaf; the open immersion makes this sheaf subterminal.
   Sectionwise, `U × H → U` is invertible exactly when `H(V)` is a singleton for every
   etale `V` mapping to the open. Continuity and the composition/pullback adjunction
   identify this with terminality under the actual open inverse image. The set-image
   theorem therefore has exactly the required closed essential image. Its fully
   faithful lift to that full subcategory is essentially surjective and yields the
   equivalence with the prescribed scheme-induced direct image.
-/
theorem oriented_closed_base_localization :
    (∀ (E : Type u) [Category.{v} E], IsGrothendieckTopos.{w} E →
      ∀ U : E, IsSubterminal U → ∃ products : HasBinaryProducts E,
        Nonempty (@ClosedBaseLocalization.ComplementData.{w, u, v, uH, vH, uG, vG}
          E _ products U)) ∧
    (∀ (C D O : Type w) [SmallCategory C] [SmallCategory D] [SmallCategory O]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology O)
      (U : Sheaf J (Type w)), IsSubterminal U →
      ∀ (i : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
        (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w))),
        ClosedBaseLocalization.ModuleAssertion J K L U i j) ∧
    (∀ (F S : AlgebraicGeometry.Scheme.{t}) (k : F ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion k],
      IsSubterminal (ClosedBaseLocalization.representedOpenComplement k) ∧
      ∃ e : Sheaf F.smallEtaleTopology (Type (t + 1)) ≌
          (closedComplementObjects
            (ClosedBaseLocalization.representedOpenComplement k)).FullSubcategory,
        Nonempty (e.functor ⋙
          (closedComplementObjects (ClosedBaseLocalization.representedOpenComplement k)).ι ≅
            AlgebraicGeometry.etaleSetDirectImage k)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro E _ hE U hU
    exact closed_complement_data hE U hU
  · intro C D O _ _ _ J K L U _ i j
    exact closed_module_assertion J K L U i j
  · intro F S k _
    refine ⟨represented_open_subterminal k, ?_⟩
    obtain ⟨hfull, hfaithful, himage, _⟩ := AlgebraicGeometry.etaleClosedComplementSets k
    let := hfull
    let := hfaithful
    exact equivalence_of_essImage (AlgebraicGeometry.etaleSetDirectImage k)
      (closedComplementObjects (ClosedBaseLocalization.representedOpenComplement k))
      (fun H ↦ (himage H).trans (etale_open_support_iff k H).symm)

end CategoryTheory
