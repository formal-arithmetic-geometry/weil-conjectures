/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.Etale.SupportCohomology
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Excision in the projective-line compactification

Source: blueprint, sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; Stacks Tags 09XP and 03F3 (blueprint: lem-pur-p1-compactification-fibre).
The map is fixed by restriction on supported sections, not by an arbitrary isomorphism.
The chart used here is `[1:t]`, so its origin is the section named `infinity` by
ProjectiveLine's other chart convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Etale.P1CompactificationFibre

variable (S : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

/-- The affine chart `[1:t]`. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev j := ProjectiveLine.infinityChart S

/-- The affine origin. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev z := AffineSpace.zeroSection PUnit.{u + 1} S

/-- The closed image `[1:0]` of the origin. Source: blueprint Step 2
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev zbar := ProjectiveLine.infinity S

/-- The origin remains closed in the compactification. Source: blueprint Step 2.
Proof: it is a section of the separated projective-line structure map, hence a closed
immersion. Its factorization through `[1:t]` is the definition of `infinity`.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem zbar_isClosedImmersion : IsClosedImmersion (zbar S) := by
  apply IsClosedImmersion.of_section_of_isSeparated (ProjectiveLine S ↘ S) (zbar S)
  exact ProjectiveLine.infinity_over (S := S)

attribute [instance] zbar_isClosedImmersion

/-- The specified proper compactification of the affine line.
Source: blueprint Step 2 (blueprint: lem-pur-p1-compactification-fibre). -/
def compactification : Compactification (𝔸(PUnit.{u + 1}; S) ↘ S) where
  Z := ProjectiveLine S
  g := ProjectiveLine S ↘ S
  i := j S
  comm := (ProjectiveLine.infinityChart_over (S := S)).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The coefficient category. Source: Stacks 09XP, module-valued supported sections
(blueprint: lem-pur-p1-compactification-fibre). -/
abbrev C := ModuleCat.{u + 1} A

private lemma terminalEvaluation_eq_res {D : Type*} [Category D]
    (J : GrothendieckTopology D) (B : Type*) [Category B]
    [HasWeakSheafify J B] [HasTerminal D] {T : D} (hT : IsTerminal T)
    (F : Sheaf J B) :
    (Sheaf.ΓNatIsoSheafSections J B hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  erw [Equiv.symm_trans_apply, Equiv.symm_symm, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

private lemma restriction_sections {X Y : Scheme.{u}} (a : X ⟶ Y)
    [IsOpenImmersion a] (G : Sheaf Y.smallEtaleTopology (C A)) (V : X.Etale) :
    globalSectionsUpperStarMap (C A) a G ≫
        (Sheaf.Γ _ (C A)).map ((upperStarIsoOpenImmersionRestriction (C A) a).hom.app G) ≫
        ((openImmersionRestriction (C A) a).obj G).ΓRes (op V) =
      G.ΓRes (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale a)).obj V)) := by
  let H := (upperStar (C A) a).obj G
  let R := (openImmersionRestriction (C A) a).obj G
  let ρ := (upperStarIsoOpenImmersionRestriction (C A) a).hom.app G
  let c : V ⟶ ⊤_ X.Etale := terminal.from V
  have ht : (Sheaf.ΓNatIsoSheafSections _ (C A) terminalIsTerminal).inv.app H ≫
      H.ΓRes (op V) = H.obj.map c.op := by
    rw [← Sheaf.ΓRes_map H c.op, ← terminalEvaluation_eq_res _ _ terminalIsTerminal]
    simp only [Iso.inv_hom_id_app_assoc]
  have hu := (upperStarLowerStarAdjunction (C A) a).unit_leftAdjointUniq_hom_app
    (openImmersionRestrictionLowerStarAdjunction (C A) a) G
  have hun := congrArg (fun f ↦ f.hom.app (op (⊤_ Y.Etale))) hu
  change ((upperStarLowerStarAdjunction (C A) a).unit.app G).hom.app
      (op (⊤_ Y.Etale)) ≫ ρ.hom.app (op (a.Etale.obj (⊤_ Y.Etale))) =
    ((openImmersionRestrictionLowerStarAdjunction (C A) a).unit.app G).hom.app
      (op (⊤_ Y.Etale)) at hun
  change _ ≫ (Sheaf.Γ _ (C A)).map ρ ≫ R.ΓRes (op V) = _
  rw [Sheaf.ΓRes_naturality]
  unfold globalSectionsUpperStarMap
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  change (Sheaf.ΓNatIsoSheafSections _ (C A) terminalIsTerminal).hom.app G ≫
    ((upperStarLowerStarAdjunction (C A) a).unit.app G).hom.app (op (⊤_ Y.Etale)) ≫
    H.obj.map (PreservesTerminal.iso a.Etale).inv.op ≫
    H.obj.map c.op ≫ ρ.hom.app (op V) = _
  rw [← Functor.map_comp_assoc, ← op_comp]
  rw [ρ.hom.naturality]
  rw [← Category.assoc _ (ρ.hom.app _) _]
  erw [hun]
  rw [terminalEvaluation_eq_res]
  change G.ΓRes _ ≫ G.obj.map _ ≫ G.obj.map _ = _
  rw [Sheaf.ΓRes_map_assoc, Sheaf.ΓRes_map]
  rfl

private lemma openComplement_preimage :
    (z S).openComplement = (j S) ⁻¹ᵁ (zbar S).openComplement := by
  ext x
  change (¬ ∃ t, z S t = x) ↔ ¬ ∃ t, zbar S t = j S x
  apply not_congr
  apply exists_congr
  intro t
  change z S t = x ↔ j S (z S t) = j S x
  exact (j S).isOpenEmbedding.injective.eq_iff.symm

private abbrev chartSite :=
  MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
    (inferInstance : Etale (j S))

private def complementMap : (z S).openComplement.toScheme ⟶
    (zbar S).openComplement.toScheme :=
  (j S).resLE _ _ (openComplement_preimage S).le

private def coverSquare : Square (ProjectiveLine S).Etale where
  X₁ := (chartSite S).obj (Scheme.Etale.mk (z S).openComplement.ι)
  X₂ := (chartSite S).obj (Scheme.Etale.mk (𝟙 _))
  X₃ := Scheme.Etale.mk (zbar S).openComplement.ι
  X₄ := Scheme.Etale.mk (𝟙 _)
  f₁₂ := (chartSite S).map
    (MorphismProperty.Over.homMk (z S).openComplement.ι (Category.comp_id _))
  f₁₃ := MorphismProperty.Over.homMk (complementMap S)
    (Scheme.Hom.resLE_comp_ι _ _)
  f₂₄ := MorphismProperty.Over.homMk (j S) (Category.comp_id _)
  f₃₄ := MorphismProperty.Over.homMk (zbar S).openComplement.ι (Category.comp_id _)
  fac := (Scheme.Etale.isTerminalMkId _).hom_ext _ _

private lemma coverSquare_pullback : (coverSquare S).IsPullback := by
  apply IsPullback.of_map (Scheme.Etale.forget _ ⋙ Over.forget _)
  · exact (coverSquare S).fac
  · have h : IsPullback (complementMap S) (z S).openComplement.ι
        (zbar S).openComplement.ι (j S) := by
      apply IsOpenImmersion.isPullback
      · exact (Scheme.Hom.resLE_comp_ι _ _).symm
      · simpa only [Scheme.Opens.opensRange_ι] using (openComplement_preimage S).symm
    change IsPullback (z S).openComplement.ι (complementMap S)
      (j S) (zbar S).openComplement.ι
    exact h.flip

private lemma coverSquare_cover :
    Sieve.ofTwoArrows (coverSquare S).f₂₄ (coverSquare S).f₃₄ ∈
      (ProjectiveLine S).smallEtaleTopology (coverSquare S).X₄ := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  by_cases hx : x ∈ Set.range (j S)
  · obtain ⟨a, ha⟩ := hx
    refine ⟨WalkingPair.left, a, ?_⟩
    change j S a = x
    exact ha
  · have hw : x ∈ (zbar S).openComplement := by
      change x ∉ Set.range (zbar S)
      rintro ⟨a, rfl⟩
      exact hx ⟨z S a, rfl⟩
    refine ⟨WalkingPair.right, ⟨x, hw⟩, ?_⟩
    exact Scheme.Opens.ι_apply _ _

private lemma coverSquare_sections (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
    ((coverSquare S).op.map G.obj).IsPullback := by
  have : Mono (coverSquare S).f₂₄ :=
    (Scheme.Etale.forget _ ⋙ Over.forget _).mono_of_mono_map (by
      change Mono (j S)
      infer_instance)
  have : Mono (coverSquare S).f₃₄ :=
    (Scheme.Etale.forget _ ⋙ Over.forget _).mono_of_mono_map (by
      change Mono (zbar S).openComplement.ι
      infer_instance)
  let P := G.obj ⋙ forget (C A)
  have hP : Presheaf.IsSheaf (ProjectiveLine S).smallEtaleTopology P :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ G.property
  have hsq : ((coverSquare S).op.map P).IsPullback := by
    let sq := coverSquare S
    let hs := coverSquare_pullback S
    let hc := coverSquare_cover S
    apply Square.IsPullback.mk
    refine PullbackCone.IsLimit.mk _
      (fun t ↦ hP.amalgamateOfArrows _ hc
        (fun j ↦ WalkingPair.casesOn j t.fst t.snd)
        (fun V ↦ by
          rintro (_ | _) (_ | _) a b fac
          · obtain rfl : a = b := (cancel_mono sq.f₂₄).1 fac
            rfl
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hs.isLimit _ _ fac
            simpa using t.condition =≫ P.map φ.op
          · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hs.isLimit _ _ fac.symm
            simpa using t.condition.symm =≫ P.map φ.op
          · obtain rfl : a = b := (cancel_mono sq.f₃₄).1 fac
            rfl)) (fun _ ↦ ?_) (fun _ ↦ ?_) (fun t m hm₁ hm₂ ↦ ?_)
    · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
    · exact hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
    · apply hP.hom_ext_ofArrows _ hc
      rintro (_ | _)
      · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
        exact hm₁
      · rw [hP.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
        exact hm₂
  exact Square.IsPullback.of_map (forget (C A)) hsq

private lemma ΓRes_mkId_isIso (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (C A)) :
    IsIso (G.ΓRes (op (Scheme.Etale.mk (𝟙 X)))) :=
  (Sheaf.isLimitConeΓ G).isIso_π_app_of_isInitial _
    (MorphismProperty.Over.mkIdTerminal @Etale X).op

private lemma isIso_of_kernel_pullback {D : Type*} [Category D] [HasZeroMorphisms D]
    [HasKernels D] {K₁ K₂ X₁ X₂ Y₁ Y₂ : D}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (ι₁ : K₁ ⟶ X₁) (ι₂ : K₂ ⟶ X₂)
    (h₁ : ι₁ ≫ f₁ = 0) (h₂ : ι₂ ≫ f₂ = 0)
    (κ₁ : IsLimit (KernelFork.ofι ι₁ h₁)) (κ₂ : IsLimit (KernelFork.ofι ι₂ h₂))
    (r : K₁ ⟶ K₂) (p : X₁ ⟶ X₂) (q : Y₁ ⟶ Y₂)
    (hp : IsPullback f₁ p q f₂) (hr : r ≫ ι₂ = ι₁ ≫ p) : IsIso r := by
  let e₁ := κ₁.conePointUniqueUpToIso (kernelIsKernel f₁)
  let e₂ := κ₂.conePointUniqueUpToIso (kernelIsKernel f₂)
  have he₁ : e₁.hom ≫ kernel.ι f₁ = ι₁ :=
    κ₁.conePointUniqueUpToIso_hom_comp (kernelIsKernel f₁) WalkingParallelPair.zero
  have he₂ : e₂.inv ≫ ι₂ = kernel.ι f₂ :=
    κ₂.conePointUniqueUpToIso_inv_comp (kernelIsKernel f₂) WalkingParallelPair.zero
  have : Mono ι₂ := Fork.IsLimit.mono κ₂
  have hr' : r = e₁.hom ≫ kernel.map f₁ f₂ p q hp.w ≫ e₂.inv := by
    apply (cancel_mono ι₂).1
    rw [hr, Category.assoc, Category.assoc, he₂, kernel.lift_ι,
      ← Category.assoc, he₁]
  have := isIso_kernel_map_of_isPullback hp
  rw [hr']
  infer_instance

/-- The uniquely characterized restriction isomorphism on sections with support.
Source: Stacks 09XP and 03F3; blueprint Step 2.
Proof: the complement W of `[1:0]` and the chart X cover P, with intersection X minus
its origin. Restrict a supported section to X. Conversely glue a section on X vanishing
on X minus the origin with zero on W. The sheaf axiom gives a unique glued section.
These constructions are inverse, natural and A-linear. The kernel inclusion is monic,
so the displayed compatibility uniquely determines the natural isomorphism.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem existsUnique_supportedRestriction :
    ∃! r : globalSectionsWithSupport (C A) (zbar S) ≅
        openImmersionRestriction (C A) (j S) ⋙ globalSectionsWithSupport (C A) (z S),
      ∀ G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A),
        r.hom.app G ≫
            (Sheaf.ΓSupportι _ (C A) (op (Scheme.Etale.mk (z S).openComplement.ι))).app
              ((openImmersionRestriction (C A) (j S)).obj G) =
          (Sheaf.ΓSupportι _ (C A)
              (op (Scheme.Etale.mk (zbar S).openComplement.ι))).app G ≫
            globalSectionsUpperStarMap (C A) (j S) G ≫
            (Sheaf.Γ _ (C A)).map
              ((upperStarIsoOpenImmersionRestriction (C A) (j S)).hom.app G) := by
  let R := openImmersionRestriction (C A) (j S)
  let U := op (Scheme.Etale.mk (z S).openComplement.ι)
  let W := op (Scheme.Etale.mk (zbar S).openComplement.ι)
  let I := op (Scheme.Etale.mk (𝟙 (𝔸(PUnit.{u + 1}; S))))
  let p : Sheaf.Γ (ProjectiveLine S).smallEtaleTopology (C A) ⟶
      R ⋙ Sheaf.Γ (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A) :=
    Sheaf.natTransΓRes _ (C A) (op (coverSquare S).X₂) ≫
      inv (Functor.whiskerLeft R (Sheaf.natTransΓRes _ (C A) I))
  let q : (sheafSections _ (C A)).obj W ⟶ R ⋙ (sheafSections _ (C A)).obj U :=
    (sheafSections _ (C A)).map (coverSquare S).f₁₃.op
  have hp (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
      IsPullback (G.ΓRes W) (p.app G) (q.app G) ((R.obj G).ΓRes U) := by
    have := ΓRes_mkId_isIso A (ProjectiveLine S) G
    have := ΓRes_mkId_isIso A _ (R.obj G)
    refine (coverSquare_sections S A G).flip.of_iso'
      (asIso (G.ΓRes (op (Scheme.Etale.mk (𝟙 _))))) (Iso.refl _)
      (asIso ((R.obj G).ΓRes I)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
      exact Sheaf.ΓRes_map _ _
    · simp [p, I, R]
      rfl
    · simp [q]
    · simp only [asIso_hom, Iso.refl_hom, Category.comp_id]
      exact Sheaf.ΓRes_map (R.obj G) _
  let ι₁ := Sheaf.ΓSupportι (ProjectiveLine S).smallEtaleTopology (C A) W
  let ι₂ := Sheaf.ΓSupportι (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A) U
  have hz (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
      (ι₁.app G ≫ p.app G) ≫ (R.obj G).ΓRes U = 0 := by
    rw [Category.assoc, ← (hp G).w, ← Category.assoc]
    simp [ι₁]
  let rApp (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
      (globalSectionsWithSupport (C A) (zbar S)).obj G ⟶
        (globalSectionsWithSupport (C A) (z S)).obj (R.obj G) :=
    (isLimitΓSupportι (C A) (z S) (R.obj G)).lift
      (KernelFork.ofι (ι₁.app G ≫ p.app G) (hz G))
  have hr (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
      rApp G ≫ ι₂.app (R.obj G) = ι₁.app G ≫ p.app G :=
    (isLimitΓSupportι (C A) (z S) (R.obj G)).fac _ WalkingParallelPair.zero
  let r : globalSectionsWithSupport (C A) (zbar S) ⟶
      R ⋙ globalSectionsWithSupport (C A) (z S) :=
    { app := rApp
      naturality := by
        intro G H f
        apply (cancel_mono (ι₂.app (R.obj H))).mp
        change (globalSectionsWithSupport (C A) (zbar S)).map f ≫
            (rApp H ≫ ι₂.app (R.obj H)) =
          rApp G ≫ ((globalSectionsWithSupport (C A) (z S)).map (R.map f) ≫
            ι₂.app (R.obj H))
        have hι₂ := ι₂.naturality (R.map f)
        change (globalSectionsWithSupport (C A) (z S)).map (R.map f) ≫
            ι₂.app (R.obj H) = ι₂.app (R.obj G) ≫
            (Sheaf.Γ _ (C A)).map (R.map f) at hι₂
        rw [hr H, hι₂, reassoc_of% hr G]
        have hn := p.naturality f
        change (Sheaf.Γ _ (C A)).map f ≫ p.app H =
          p.app G ≫ (Sheaf.Γ _ (C A)).map (R.map f) at hn
        rw [← hn, ← Category.assoc]
        exact congrArg (fun t ↦ t ≫ p.app H) (ι₁.naturality f) }
  have (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) : IsIso (r.app G) := by
    exact isIso_of_kernel_pullback (G.ΓRes W) ((R.obj G).ΓRes U)
      (ι₁.app G) (ι₂.app (R.obj G))
      (Sheaf.ΓSupportι_app_comp_ΓRes _ _ _ G)
      (Sheaf.ΓSupportι_app_comp_ΓRes _ _ _ (R.obj G))
      (isLimitΓSupportι (C A) (zbar S) G)
      (isLimitΓSupportι (C A) (z S) (R.obj G))
      (r.app G) (p.app G) (q.app G) (hp G) (hr G)
  have : IsIso r := NatIso.isIso_of_isIso_app r
  have hp_actual (G : Sheaf (ProjectiveLine S).smallEtaleTopology (C A)) :
      p.app G = globalSectionsUpperStarMap (C A) (j S) G ≫
        (Sheaf.Γ _ (C A)).map
          ((upperStarIsoOpenImmersionRestriction (C A) (j S)).hom.app G) := by
    have := ΓRes_mkId_isIso A _ (R.obj G)
    apply (cancel_mono ((R.obj G).ΓRes I)).mp
    rw [Category.assoc, restriction_sections A (j S) G I.unop]
    simp [p, I, R]
    rfl
  refine ⟨asIso r, ?_, ?_⟩
  · intro G
    change rApp G ≫ ι₂.app (R.obj G) = _
    rw [hr, hp_actual]
  · intro r' h'
    apply Iso.ext
    apply NatTrans.ext
    funext G
    apply (cancel_mono (ι₂.app (R.obj G))).mp
    change r'.hom.app G ≫ ι₂.app (R.obj G) = rApp G ≫ ι₂.app (R.obj G)
    rw [h' G, hr, hp_actual]

/-- Restriction on supported sections, selected by its unique kernel-inclusion equation.
Source: Stacks 09XP and 03F3 (blueprint: lem-pur-p1-compactification-fibre). -/
def supportedRestriction := (existsUnique_supportedRestriction S A).exists.choose

/-- Derived restriction, with the open unit identifying the restriction of `j_! F` with F.
Source: Stacks 03F3, injective computation (blueprint: lem-pur-p1-compactification-fibre). -/
def derivedRestriction (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    (rightDerivedSectionsWithSupport (C A) (zbar S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek (C A) (j S)).obj F)) ⟶
      (rightDerivedSectionsWithSupport (C A) (z S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) :=
  (Functor.rightDerivedPullback (openImmersionRestriction (C A) (j S))
      (supportedRestriction S A).hom).app _ ≫
    (rightDerivedSectionsWithSupport (C A) (z S)).map
      (((openImmersionRestriction (C A) (j S)).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          (asIso ((openImmersionLowerShriekAdjunction (C A) (j S)).unit.app F)).inv)

/-- Excision: derived restriction is invertible.
Source: Stacks 03F3 and 09XP; blueprint Step 2.
Proof: resolve `j_! F` by a bounded-below injective complex I. Restriction is exact and
preserves injectives, because its left adjoint extension by zero is exact. The open unit
identifies the restriction of `j_! F` with F. The unique supported-section isomorphism
above applied termwise to I is an isomorphism of complexes. It computes the displayed
right-derived comparison. Thus the comparison is invertible, independently of the
resolution by uniqueness of right derived functors.
(blueprint: lem-pur-p1-compactification-fibre). -/
theorem derivedRestriction_isIso
    (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    IsIso (derivedRestriction S A F) := by
  have : (openImmersionRestriction (C A) (j S)).PreservesKInjectiveComplexes :=
    (openImmersionLowerShriekAdjunction (C A) (j S)).preservesKInjectiveComplexes
  have := Functor.isIso_rightDerivedPullback_app
    (openImmersionRestriction (C A) (j S)) (supportedRestriction S A).hom
    ((DerivedCategory.singleFunctor _ 0).obj
      ((openImmersionLowerShriek (C A) (j S)).obj F))
  unfold derivedRestriction
  infer_instance

/-- Canonical excision, in the direction from affine support to projective support.
Source: blueprint Step 2 (blueprint: lem-pur-p1-compactification-fibre). -/
def excision (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :=
  letI := derivedRestriction_isIso S A F
  (asIso (derivedRestriction S A F)).symm

/-- Forget support on the projective line, derived from the actual kernel inclusion.
Source: Stacks 09XP (blueprint: lem-pur-p1-compactification-fibre). -/
def forgetSupport : rightDerivedSectionsWithSupport (C A) (zbar S) ⟶
    (Sheaf.Γ (ProjectiveLine S).smallEtaleTopology (C A)).rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatTrans
    (Sheaf.ΓSupportι _ (C A) (op (Scheme.Etale.mk (zbar S).openComplement.ι)))

/-- The identification of derived global sections with the derived proper direct image,
after global sections at the base. For an algebraically closed field base, these latter
global sections are the equivalence from module sheaves on the point to modules.
Source: blueprint Step 2; Stacks 09XP
(blueprint: lem-pur-p1-compactification-fibre). -/
def properDirectImageComparison :
    (lowerStar (C A) (ProjectiveLine S ↘ S)).rightDerivedFunctor ⋙
        rightDerivedGlobalSections (C A) S ≅
      rightDerivedGlobalSections (C A) (ProjectiveLine S) :=
  rightDerivedLowerStarCompRightDerivedGlobalSectionsIso (C A) (ProjectiveLine S ↘ S)

/-- The global-sections target is the compactly supported direct image for the
specified compactification, followed by global sections on the base.
Source: blueprint Step 2, definition of compact support
(blueprint: lem-pur-p1-compactification-fibre). -/
def compactSupportComparison
    (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) :
    (rightDerivedGlobalSections (C A) (ProjectiveLine S)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((openImmersionLowerShriek (C A) (j S)).obj F)) ≅
      (rightDerivedGlobalSections (C A) S).obj
        ((rightDerivedLowerShriekOfCompactification (C A) (compactification S)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  (properDirectImageComparison S A).symm.app _ ≪≫
    (rightDerivedGlobalSections (C A) S).mapIso
      ((lowerStar (C A) (ProjectiveLine S ↘ S)).rightDerivedFunctor.mapIso
        (((openImmersionLowerShriek (C A) (j S)).mapDerivedCategorySingleFunctor 0).app F).symm)

/-- The compactification forget-supports morphism on cohomology.
Source: blueprint Step 2. It is excision followed by the kernel inclusion on P.
(blueprint: lem-pur-p1-compactification-fibre). -/
def u (F : Sheaf (𝔸(PUnit.{u + 1}; S)).smallEtaleTopology (C A)) (m : ℤ) :=
  (DerivedCategory.homologyFunctor (C A) m).map
    ((excision S A F).hom ≫ (forgetSupport S A).app _)

end AlgebraicGeometry.Etale.P1CompactificationFibre
