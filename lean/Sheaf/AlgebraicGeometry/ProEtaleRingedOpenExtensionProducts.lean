/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation

/-!
# Products of ringed pro-etale open extensions

Source: Stacks Project, Pro-etale Cohomology, Tag 09BP (lemma-j-shriek-limits),
with arbitrary ring-sheaf coefficients via ringed recollement
(blueprint: lem-cbc-ringed-open-extension-products).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Exact functors that jointly detect zero objects jointly detect isomorphisms. -/
private theorem jointly_detect_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (J : C ⥤ D) (I : C ⥤ E)
    [J.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (hd : ∀ M, IsZero (J.obj M) → IsZero (I.obj M) → IsZero M)
    {M N : C} (c : M ⟶ N) [IsIso (J.map c)] [IsIso (I.map c)] : IsIso c := by
  have hk : IsZero (kernel c) := hd _
    ((isZero_kernel_of_mono (J.map c)).of_iso (PreservesKernel.iso J c))
    ((isZero_kernel_of_mono (I.map c)).of_iso (PreservesKernel.iso I c))
  have hc : IsZero (cokernel c) := hd _
    ((isZero_cokernel_of_epi (J.map c)).of_iso (PreservesCokernel.iso J c))
    ((isZero_cokernel_of_epi (I.map c)).of_iso (PreservesCokernel.iso I c))
  have : Mono c := Preadditive.mono_of_isZero_kernel c hk
  have : Epi c := Preadditive.epi_of_isZero_cokernel c hc
  exact isIso_of_mono_of_epi c

/-- For a quasi-compact open immersion, the canonical product comparison for extension
by zero of module sheaves is invertible and natural in maps of families.

The open site is presented as the slice at `U`, as in `ProEt.weaklyEtale_localization`.
The coefficient sheaf is `(proEtaleModuleCoefficients R).over U`; the functor
`proEtaleRingedExtensionByZero U R` is the recorded extension presheaf followed by
module sheafification. `piComparison` has components the images of the projections.
Products are Mathlib's sectionwise module-sheaf limits. The index type may be empty.
No quasi-compactness or quasi-separatedness condition is imposed on `X`.

Source: Stacks Project, Tag 09BP, using Tags 09AA, 09AG, 09AH and 09BN
(blueprint: lem-cbc-ringed-open-extension-products).

Proof plan:
1. Use `reduced_induced_closed_subscheme` for the closed complement of `U.hom`.
   Apply `proEtale_ringed_open_closed` to obtain the open restriction isomorphism,
   closed restriction vanishing, exactness and the localization short exact sequence.
2. Form the specified comparison `c` using the sectionwise products of
   `SheafOfModules.hasLimitsOfSize`. Open inverse image preserves products by
   `proEtale_immersion_inverseImage_preservesLimits`. Naturality of the open restriction
   isomorphism identifies the open restriction of `c` with an isomorphism: after
   projecting to each factor its composite is the restriction isomorphism on the product.
3. Closed inverse image also preserves products by the same immersion theorem. Both
   restrictions of the source and target to the closed complement are zero, since
   closed restriction annihilates extension by zero. Thus the closed restriction of
   `c` is invertible. This includes the empty product, which is the zero module sheaf.
4. Both inverse images are exact. The kernel and cokernel of `c` therefore have zero
   open and closed restrictions. The localization sequence makes each zero, using
   exactness of extension by zero and closed direct image. Hence `c` is invertible.
5. For a family map `a`, project the naturality square to factor `s`. Both paths are
   extension by zero applied to the projection followed by `a s`, by functoriality.
   Product uniqueness gives the displayed equality. For an empty family both products
   are terminal zero objects and extension by zero preserves zero by exactness.
   The same formulas cover an empty open or scheme, the identity open, and zero rings. -/
theorem proEtaleRingedExtensionByZero_products {X : Scheme.{u}} (U : X.ProEt)
    [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (S : Type (u + 1))
    (F : S → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U)) :
    IsIso (piComparison (proEtaleRingedExtensionByZero U R) F) ∧
      ∀ (G : S → ringedSiteModules.{u + 1} ((proEtaleModuleCoefficients R).over U))
        (a : ∀ s : S, F s ⟶ G s),
        (proEtaleRingedExtensionByZero U R).map (Limits.Pi.map a) ≫
            piComparison (proEtaleRingedExtensionByZero U R) G =
          piComparison (proEtaleRingedExtensionByZero U R) F ≫
            Limits.Pi.map (fun s ↦ (proEtaleRingedExtensionByZero U R).map (a s)) := by
  classical
  let T : TopologicalSpace.Closeds X :=
    ⟨(Set.range U.hom)ᶜ, (IsOpenImmersion.isOpen_range U.hom).isClosed_compl⟩
  let i := (IdealSheafData.vanishingIdeal T).subschemeι
  have hi : Set.range i = (T : Set X) :=
    (IdealSheafData.reduced_induced_closed_subscheme X T).2.2.2.2.2.1
  have hU : Set.range U.hom = (Set.range i)ᶜ := by
    rw [hi]
    exact (compl_compl _).symm
  obtain ⟨q, ⟨e⟩, ai, aj, _, hu, _, hz, hLlim, _, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let L := proEtaleRingedExtensionByZero U R
  let J := SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) U
  let I := proEtaleModuleInverseImage i R
  have : PreservesFiniteLimits L := hLlim
  have : L.IsLeftAdjoint := aj.isLeftAdjoint
  have : (proEtaleRingedDirectImage i R).IsRightAdjoint := ai.isRightAdjoint
  obtain ⟨hIadd, hIlim, hIcolim, hIall, _⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits i).2.2 R
  have : I.Additive := hIadd
  have : PreservesFiniteLimits I := hIlim
  have : PreservesFiniteColimits I := hIcolim
  have : PreservesLimitsOfSize.{u + 1, u + 1} I := hIall
  obtain ⟨_, _, hJcolim, _⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits U.hom).2.2 R
  have : PreservesFiniteColimits (proEtaleModuleInverseImage U.hom R) := hJcolim
  have : J.IsRightAdjoint := aj.isRightAdjoint
  have : PreservesFiniteColimits J := preservesFiniteColimits_of_natIso e
  have : PreservesLimitsOfSize.{u + 1, u + 1} J := aj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits J := by infer_instance
  have hunit (G) : IsIso (aj.unit.app G) := hu G
  let c := piComparison L F
  have hJc : IsIso (J.map c) := by
    have he : aj.unit.app (∏ᶜ F) ≫ J.map c ≫
        piComparison J (fun s ↦ L.obj (F s)) =
        Limits.Pi.map (fun s ↦ aj.unit.app (F s)) := by
      apply Limits.Pi.hom_ext
      intro s
      simp only [Category.assoc, piComparison_comp_π, ← J.map_comp]
      dsimp [c]
      rw [piComparison_comp_π, Limits.Pi.map_π]
      exact (aj.unit.naturality (Limits.Pi.π F s)).symm
    have hc : J.map c = inv (aj.unit.app (∏ᶜ F)) ≫
        Limits.Pi.map (fun s ↦ aj.unit.app (F s)) ≫
          inv (piComparison J (fun s ↦ L.obj (F s))) := by
      rw [← he]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [hc]
    infer_instance
  have hIc : IsIso (I.map c) := by
    have hsrc : IsZero (I.obj (L.obj (∏ᶜ F))) := hz _
    have hprod : IsZero (∏ᶜ fun s ↦ I.obj (L.obj (F s))) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply Limits.Pi.hom_ext
      intro s
      exact (hz (F s)).eq_of_tgt _ _
    have htgt : IsZero (I.obj (∏ᶜ fun s ↦ L.obj (F s))) :=
      hprod.of_iso (PreservesProduct.iso I (fun s ↦ L.obj (F s)))
    exact isIso_of_source_target_iso_zero (I.map c) hsrc.isoZero htgt.isoZero
  have hd : ∀ M, IsZero (J.obj M) → IsZero (I.obj M) → IsZero M := by
    intro M hj hi
    let S := ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)
    have hS : S.Exact := (hs M).2.2
    have he := (S.exact₂_iff hS.toIsComplex).1 hS
    exact he.isZero_of_both_isZero (L.map_isZero hj)
      ((proEtaleRingedDirectImage i R).map_isZero hi)
  have : IsIso c := jointly_detect_iso J I hd c
  refine ⟨this, ?_⟩
  intro G a
  apply Limits.Pi.hom_ext
  intro s
  simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
    ← Functor.map_comp]
  rw [← Category.assoc, piComparison_comp_π, Functor.map_comp]

end AlgebraicGeometry.Scheme
