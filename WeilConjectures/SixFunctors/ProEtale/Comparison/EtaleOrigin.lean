/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.SiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CoverConservative

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Closure properties of the pro-étale sheaves of étale origin

A pro-étale sheaf is *of étale origin* if it lies in the essential image of the comparison
pullback `ν^*`. Since `ν^*` is exact and fully faithful, the sheaves of étale origin are closed
under kernels, cokernels and finite biproducts, and they are stable under pullback. By the
comparison `ν^* Ru_* ≅ Ru_* ν^*` for quasi-compact quasi-separated `u`
(`AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`) they
are also stable under pushforward along such `u`.

Consequently, being of étale origin is local for finite pro-étale covering families
`p s : V s ⟶ X` by quasi-compact quasi-separated morphisms
(`AlgebraicGeometry.ProEtale.essImage_comparisonUpperStar_of_cover`): a sheaf `F` is the kernel
of a morphism `∏ₛ (p s)_* (p s)^* F ⟶ ∏ₛ (p s)_* (p s)^* C` between sheaves of étale origin, where
`C` is the cokernel of the unit `F ⟶ ∏ₛ (p s)_* (p s)^* F`, whose pullbacks are of étale origin by
weakly étale base change.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Closure

variable {A} {X : Scheme.{u}}

/-- The sheaves of étale origin are closed under kernels. -/
lemma essImage_comparisonUpperStar_kernel {F₁ F₂ : Sheaf (Scheme.ProEt.topology X) A}
    (φ : F₁ ⟶ F₂) (h₁ : (comparisonUpperStar A X).essImage F₁)
    (h₂ : (comparisonUpperStar A X).essImage F₂) :
    (comparisonUpperStar A X).essImage (kernel φ) := by
  obtain ⟨G₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨G₂, ⟨e₂⟩⟩ := h₂
  let N := comparisonUpperStar A X
  let ψ : G₁ ⟶ G₂ := N.preimage (e₁.hom ≫ φ ≫ e₂.inv)
  refine ⟨kernel ψ, ⟨PreservesKernel.iso N ψ ≪≫ kernel.mapIso _ _ e₁ e₂ ?_⟩⟩
  simp [ψ]

/-- The sheaves of étale origin are closed under cokernels. -/
lemma essImage_comparisonUpperStar_cokernel {F₁ F₂ : Sheaf (Scheme.ProEt.topology X) A}
    (φ : F₁ ⟶ F₂) (h₁ : (comparisonUpperStar A X).essImage F₁)
    (h₂ : (comparisonUpperStar A X).essImage F₂) :
    (comparisonUpperStar A X).essImage (cokernel φ) := by
  obtain ⟨G₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨G₂, ⟨e₂⟩⟩ := h₂
  let N := comparisonUpperStar A X
  let ψ : G₁ ⟶ G₂ := N.preimage (e₁.hom ≫ φ ≫ e₂.inv)
  refine ⟨cokernel ψ, ⟨PreservesCokernel.iso N ψ ≪≫ cokernel.mapIso _ _ e₁ e₂ ?_⟩⟩
  simp [ψ]

/-- The sheaves of étale origin are closed under finite biproducts. -/
lemma essImage_comparisonUpperStar_biproduct {S : Type} [Finite S]
    (F : S → Sheaf (Scheme.ProEt.topology X) A)
    (h : ∀ s, (comparisonUpperStar A X).essImage (F s)) :
    (comparisonUpperStar A X).essImage (⨁ F) := by
  choose G e using h
  have := Fintype.ofFinite S
  exact ⟨⨁ G, ⟨(comparisonUpperStar A X).mapBiproduct G ≪≫ biproduct.mapIso fun s ↦ (e s).some⟩⟩

/-- The sheaves of étale origin are stable under pullback. -/
lemma essImage_comparisonUpperStar_upperStar {X' : Scheme.{u}} (q : X' ⟶ X)
    {F : Sheaf (Scheme.ProEt.topology X) A} (hF : (comparisonUpperStar A X).essImage F) :
    (comparisonUpperStar A X').essImage ((ProEtale.upperStar A q).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(Etale.upperStar A q).obj G,
    ⟨((comparisonUpperStarCompUpperStarIso A q).app G).symm ≪≫ (ProEtale.upperStar A q).mapIso e⟩⟩

lemma essImage_comparisonUpperStar_of_iso {F F' : Sheaf (Scheme.ProEt.topology X) A}
    (e : F ≅ F') (hF : (comparisonUpperStar A X).essImage F) :
    (comparisonUpperStar A X).essImage F' :=
  (comparisonUpperStar A X).essImage.prop_of_iso e hF

end Closure

section LowerStar

variable {A} [Etale.HasCohomologyContinuity A] {U V : Scheme.{u}} (u : U ⟶ V) [QuasiCompact u]
  [QuasiSeparated u]

/-- The comparison `ν^* u_* ≅ u_* ν^*` for a quasi-compact quasi-separated `u`, on sheaves: the
degree `0` part of `ν^* Ru_* ≅ Ru_* ν^*`. -/
lemma nonempty_comparisonUpperStar_obj_lowerStar_obj_iso
    (G : Sheaf U.smallEtaleTopology A) :
    Nonempty ((comparisonUpperStar A V).obj ((Etale.lowerStar A u).obj G) ≅
      (ProEtale.lowerStar A u).obj ((comparisonUpperStar A U).obj G)) := by
  obtain ⟨e⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar A u
  let S₀ := (DerivedCategory.Plus.singleFunctor (Sheaf U.smallEtaleTopology A) 0).obj G
  exact ⟨(comparisonUpperStar A V).mapIso
      ((Etale.lowerStar A u).rightDerivedZeroIsoSelf.symm.app G ≪≫
        ((Etale.lowerStar A u).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
          0).symm.app G) ≪≫
    ((comparisonUpperStar A V).mapDerivedCategoryPlusHomologyFunctorIso 0).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso (e.app S₀) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((ProEtale.lowerStar A u).rightDerivedFunctorPlus.mapIso
        (((comparisonUpperStar A U).mapDerivedCategoryPlusSingleFunctor 0).app G)) ≪≫
    ((ProEtale.lowerStar A u).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      0).app _ ≪≫
    (ProEtale.lowerStar A u).rightDerivedZeroIsoSelf.app _⟩

/-- The sheaves of étale origin are stable under pushforward along a quasi-compact
quasi-separated morphism. -/
lemma essImage_comparisonUpperStar_lowerStar {F : Sheaf (Scheme.ProEt.topology U) A}
    (hF : (comparisonUpperStar A U).essImage F) :
    (comparisonUpperStar A V).essImage ((ProEtale.lowerStar A u).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  obtain ⟨e'⟩ := nonempty_comparisonUpperStar_obj_lowerStar_obj_iso u G
  exact ⟨(Etale.lowerStar A u).obj G, ⟨e' ≪≫ (ProEtale.lowerStar A u).mapIso e⟩⟩

end LowerStar

section Cover

variable {A} [Etale.HasCohomologyContinuity A] {X : Scheme.{u}} {S : Type} [Finite S]
  {V : S → Scheme.{u}} (p : ∀ s, V s ⟶ X) [∀ s, QuasiCompact (p s)] [∀ s, QuasiSeparated (p s)]

/-- The product `∏ₛ (p s)_* (p s)^* F` of the pushforwards of the pullbacks along a finite
family. -/
noncomputable abbrev coverProduct (F : Sheaf (Scheme.ProEt.topology X) A) :
    Sheaf (Scheme.ProEt.topology X) A :=
  ⨁ fun s ↦ (ProEtale.lowerStar A (p s)).obj ((ProEtale.upperStar A (p s)).obj F)

/-- The unit `F ⟶ ∏ₛ (p s)_* (p s)^* F`. -/
noncomputable def coverUnit (F : Sheaf (Scheme.ProEt.topology X) A) :
    F ⟶ coverProduct p F :=
  biproduct.lift fun s ↦ (ProEtale.upperStarLowerStarAdjunction A (p s)).unit.app F

omit [Etale.HasCohomologyContinuity A] [∀ s, QuasiCompact (p s)]
  [∀ s, QuasiSeparated (p s)] in
@[reassoc (attr := simp)]
lemma coverUnit_π (F : Sheaf (Scheme.ProEt.topology X) A) (s : S) :
    coverUnit p F ≫ biproduct.π _ s =
      (ProEtale.upperStarLowerStarAdjunction A (p s)).unit.app F :=
  biproduct.lift_π _ _

omit [Etale.HasCohomologyContinuity A] [∀ s, QuasiCompact (p s)]
  [∀ s, QuasiSeparated (p s)] in
/-- The unit along a family whose pullbacks jointly detect zero objects is a monomorphism. -/
lemma mono_coverUnit
    (hdet : ∀ H : Sheaf (Scheme.ProEt.topology X) A,
      (∀ s, IsZero ((ProEtale.upperStar A (p s)).obj H)) → IsZero H)
    (F : Sheaf (Scheme.ProEt.topology X) A) : Mono (coverUnit p F) := by
  refine Preadditive.mono_of_isZero_kernel' _ (kernelIsKernel _) (hdet _ fun s ↦ ?_)
  let P := ProEtale.upperStar A (p s)
  -- `P` of the unit is a split monomorphism, so `P` of its kernel vanishes
  have hsplit : P.map (coverUnit p F ≫ biproduct.π _ s) ≫
      (ProEtale.upperStarLowerStarAdjunction A (p s)).counit.app (P.obj F) = 𝟙 _ := by
    rw [coverUnit_π]
    exact (ProEtale.upperStarLowerStarAdjunction A (p s)).left_triangle_components F
  have : Mono (P.map (coverUnit p F)) := by
    have : Mono (P.map (coverUnit p F ≫ biproduct.π _ s)) := mono_of_mono_fac hsplit
    rw [P.map_comp] at this
    exact mono_of_mono _ (P.map (biproduct.π _ s))
  exact IsZero.of_iso (isZero_kernel_of_mono _) (PreservesKernel.iso P _)

/-- **Being of étale origin can be checked on a finite family of quasi-compact
quasi-separated morphisms whose pullbacks jointly detect zero objects.** The sheaf `F` is the
kernel of `∏ (p s)_* (p s)^* F ⟶ C ⟶ ∏ (p s)_* (p s)^* C`, `C` the cokernel of the unit, and the
pullbacks of these products are of étale origin, the pushforwards and pullbacks preserving the
sheaves of étale origin. -/
theorem essImage_comparisonUpperStar_of_detect
    (hdet : ∀ H : Sheaf (Scheme.ProEt.topology X) A,
      (∀ s, IsZero ((ProEtale.upperStar A (p s)).obj H)) → IsZero H)
    (F : Sheaf (Scheme.ProEt.topology X) A)
    (hF : ∀ s, (comparisonUpperStar A (V s)).essImage ((ProEtale.upperStar A (p s)).obj F)) :
    (comparisonUpperStar A X).essImage F := by
  have hT (H : Sheaf (Scheme.ProEt.topology X) A)
      (hH : ∀ s, (comparisonUpperStar A (V s)).essImage ((ProEtale.upperStar A (p s)).obj H)) :
      (comparisonUpperStar A X).essImage (coverProduct p H) :=
    essImage_comparisonUpperStar_biproduct _ fun s ↦
      essImage_comparisonUpperStar_lowerStar _ (hH s)
  -- the pullbacks of the cokernel of the unit are of étale origin
  have hC (s : S) : (comparisonUpperStar A (V s)).essImage
      ((ProEtale.upperStar A (p s)).obj (cokernel (coverUnit p F))) :=
    essImage_comparisonUpperStar_of_iso
      (PreservesCokernel.iso (ProEtale.upperStar A (p s)) (coverUnit p F)).symm
      (essImage_comparisonUpperStar_cokernel _ (hF s)
        (essImage_comparisonUpperStar_upperStar _ (hT F hF)))
  have := mono_coverUnit p hdet F
  have := mono_coverUnit p hdet (cokernel (coverUnit p F))
  -- `F` is the kernel of `∏ (p s)_* (p s)^* F ⟶ C ⟶ ∏ (p s)_* (p s)^* C`, `C` the cokernel
  have hker := isKernelCompMono
    (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit (parallelPair (coverUnit p F) 0)))
    (coverUnit p (cokernel (coverUnit p F))) rfl
  exact essImage_comparisonUpperStar_of_iso
    ((limit.isLimit _).conePointUniqueUpToIso hker)
    (essImage_comparisonUpperStar_kernel _ (hT F hF) (hT _ hC))

/-- **Being of étale origin is local for finite pro-étale covering families** by
quasi-compact quasi-separated morphisms. -/
theorem essImage_comparisonUpperStar_of_cover [∀ s, WeaklyEtale (p s)]
    (hp : Presieve.ofArrows V p ∈ Scheme.proetalePrecoverage X)
    (F : Sheaf (Scheme.ProEt.topology X) A)
    (hF : ∀ s, (comparisonUpperStar A (V s)).essImage ((ProEtale.upperStar A (p s)).obj F)) :
    (comparisonUpperStar A X).essImage F :=
  essImage_comparisonUpperStar_of_detect p
    (fun H hH ↦ (isZero_iff_forall_isZero_upperStar_obj A p hp H).2 hH) F hF

end Cover

end AlgebraicGeometry.ProEtale
