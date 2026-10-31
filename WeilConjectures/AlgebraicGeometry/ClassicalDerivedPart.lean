/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedDefinitions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.EssImageKernels
import WeilConjectures.AlgebraicGeometry.ClassicalDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalDerivedWeakSerre
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheaves
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.BoundedBelowProEtaleComparison

/-!
# The derived classical part

Source: the Weil conjectures blueprint,
`sec-proetale-coefficients/sk-cor-pe-classical-derived/_section.md`,
node `sk-cor-pe-classical-derived` (blueprint: sk-cor-pe-classical-derived).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Classical module sheaves are weak Serre, and bounded-below classical pro-étale
complexes are equivalent to bounded-below étale complexes through the comparison maps.

Source: the blueprint node `sk-cor-pe-classical-derived`, order 1053
(blueprint: sk-cor-pe-classical-derived).

Proof: exactness and full faithfulness of the comparison inverse image give closure under
kernels and cokernels. The extension statement is the counit argument for a short exact
sequence with classical endpoints. The bounded-below comparison unit gives the classical
image and the inverse-image/direct-image counit on every classical object. Restricting the
comparison adjunction to the full classical subcategory and using the triangle identities
produces the displayed equivalence, with inverse functors the derived comparison inverse
image and right derived direct image.
-/
theorem classicalDerivedPart (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    ObjectProperty.IsClosedUnderKernels (IsClassicalModuleFor X Λ) ∧
      ObjectProperty.IsClosedUnderCokernels (IsClassicalModuleFor X Λ) ∧
      ObjectProperty.IsClosedUnderExtensions (IsClassicalModuleFor X Λ) ∧
    ∃ e : (ClassicalPlus X Λ).FullSubcategory ≌
          DerivedCategory.Plus
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        Nonempty (e.inverse ⋙ (ClassicalPlus X Λ).ι ≅
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus) ∧
        Nonempty (e.functor ≅ (ClassicalPlus X Λ).ι ⋙
            (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctorPlus) := by
  classical
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let P : ObjectProperty (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) := IsClassicalModuleFor X Λ
  obtain ⟨F, hFL, hFeq, _, _⟩ := (proEtaleClassicalSheaves X).2.2 Λ
  obtain ⟨adj, hlim, hcolim, hbij, _, _⟩ :=
    proEtaleClassicalSheavesModules X Λ
  have hIso {G H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
      (e : G ≅ H) (hG : P G) : P H := by
    intro I _ _ A
    have hmap := continuityMap_natural A e.hom.hom
    have : IsIso (continuityMap A G.obj) := hG A
    have : IsIso (Functor.whiskerLeft A.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft A.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    apply (isIso_comp_left_iff
      (colimMap (Functor.whiskerLeft A.diagram.op e.hom.hom)) _).mp
    rw [hmap]
    infer_instance
  have hclass (G : Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} Λ)) : P G ↔ L.essImage G := by
    constructor
    · intro hG
      obtain ⟨A, ⟨e⟩⟩ := hFeq.essSurj.mem_essImage ⟨G, hG⟩
      refine ⟨A, ?_⟩
      exact ⟨(eqToIso (congrArg (fun H ↦ H.obj A) hFL)).symm ≪≫ P.ι.mapIso e⟩
    · rintro ⟨A, ⟨e⟩⟩
      exact hIso (eqToIso (congrArg (fun H ↦ H.obj A) hFL) ≪≫ e)
        (F.obj A).property
  let hff : Nonempty L.FullyFaithful :=
    (Functor.FullyFaithful.nonempty_iff_map_bijective L).2 hbij
  let ff := Classical.choice hff
  letI : L.Full := ff.full
  letI : L.Faithful := ff.faithful
  letI : PreservesFiniteLimits L := hlim
  letI : PreservesFiniteColimits L := hcolim
  letI : L.Additive := inferInstance
  letI hk : L.essImage.IsClosedUnderKernels := inferInstance
  letI hc : L.essImage.IsClosedUnderCokernels := inferInstance
  have hker : P.IsClosedUnderKernels := by
    refine ⟨?_⟩
    intro G hG
    exact (hclass _).2 (hk.kernels_le _ (by
      rcases hG with ⟨f, k, hk', h₁, h₂⟩
      exact .of_isLimit f k hk' ⟨(hclass _).1 h₁, (hclass _).1 h₂⟩))
  have hcoker : P.IsClosedUnderCokernels := by
    refine ⟨?_⟩
    intro G hG
    exact (hclass _).2 (hc.cokernels_le _ (by
      rcases hG with ⟨f, k, hk', h₁, h₂⟩
      exact .of_isColimit f k hk' ⟨(hclass _).1 h₁, (hclass _).1 h₂⟩))
  have hext : P.IsClosedUnderExtensions := by
    refine ⟨?_⟩
    intro S hS h₁ h₃
    obtain ⟨F₁, ⟨e₁⟩⟩ := (hclass _).mp h₁
    obtain ⟨F₂, ⟨e₂⟩⟩ := (hclass _).mp h₃
    let i := e₁.hom ≫ S.f
    let p := S.g ≫ e₂.inv
    have hip : i ≫ p = 0 := by simp [i, p]
    let S' := ShortComplex.mk i p hip
    have hIso : S ≅ S' :=
      ShortComplex.isoMk (S₁ := S) (S₂ := S') e₁.symm (Iso.refl _) e₂.symm
        (by simp [S', i]) (by simp [S', p])
    have hS' : S'.ShortExact := ShortComplex.shortExact_of_iso hIso hS
    change IsClassicalModuleFor X Λ S.X₂
    exact (classicalExtension X Λ F₁ F₂ S.X₂ i p hip hS').2
  refine ⟨hker, hcoker, hext, ?_⟩
  have hunit := (boundedBelowComparison X Λ).1
  rw [NatTrans.isIso_iff_isIso_app] at hunit
  obtain ⟨himg, hcounit, ⟨e, hfun, hinv⟩⟩ :=
    classicalDerivedEquivalence X Λ (by
      intro L'
      exact hunit L')
  refine ⟨e.symm, ?_, ?_⟩
  · exact hfun
  · exact hinv

end AlgebraicGeometry.ProEtale

end
