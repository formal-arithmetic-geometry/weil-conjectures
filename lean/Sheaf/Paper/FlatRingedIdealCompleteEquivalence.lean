/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Paper.SiteRestrictionExact
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.Paper.FlatExtendedCechComparison

/-!
# Flat ringed-site equivalence on locally derived complete objects

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of scalars is exact on module sheaves.
Source: Stacks Project, Algebraization, Tag 099C
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the underlying additive sheaf is unchanged. Kernels are sectionwise kernels with
restricted action; cokernels are sheafifications of the same additive presheaf cokernels.
The same description applies to finite products and coproducts. -/
theorem siteRestrictScalars_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  sorry

/-- Derived restriction of scalars, using Mathlib's restriction of scalars and its exact
functor localization, rather than an unspecified functor between derived categories.
Source: Stacks Project, Algebraization, Tags 099C and 099I
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence). -/
noncomputable def siteDerivedRestrictScalars {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    DerivedCategory (SheafOfModules.{u} (siteModuleRings B)) ⥤
      DerivedCategory (SheafOfModules.{u} (siteModuleRings R)) :=
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory


/-- Restriction of scalars along a flat ring-sheaf map which is an isomorphism modulo a
locally finitely generated ideal induces an equivalence of the locally derived complete
full subcategories. The natural isomorphism in the conclusion identifies the equivalence
with the specified derived restriction functor on the ambient categories.

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).

Proof:
1. Restriction of scalars is exact and conservative, since its underlying additive sheaf
is unchanged. It therefore induces the stated derived functor. By
`lem-weil-pbc-restriction-local-completeness`, it preserves and reflects local completeness.
2. Choose the augmented extended Cech model `K → R[0]` from
`lem-weil-pbc-extended-cech-completion-model`. Flatness makes termwise tensoring with `B`
exact, giving `K_B → B[0]` and `u : K → r K_B`. On every generating slice, localization
commutes with tensor: `(a/f^n) ⊗ b ↦ φ(a)b/φ(f)^n` with inverse
`b/φ(f)^n ↦ (1/f^n) ⊗ b`. Finite products in this model are finite direct sums.
Slice restriction is exact (`lem-weil-pbc-site-restriction-exact`) and preserves quotients;
flatness restricts (`lem-weil-pbc-slice-restriction-flat`). Apply
`lem-weil-pbc-flat-extended-cech-comparison` locally to deduce that `u` is a quasi-isomorphism.
3. Define `F(E)` by the Hom complex from `r K_B` into the functorial K-injective replacement
of a representative of `E`, with action `(b h)(k) = h(bk)`. This action commutes with the
Hom differential and with restrictions. Naturality and two-out-of-three show replacement
maps preserve quasi-isomorphisms; `lem-pur-rhom-well-defined` then makes the Hom maps
quasi-isomorphisms. Thus the construction descends to a functor `D(R) → D(B)`.
4. Precomposition with `u` identifies `r F(E)` with `RHom_R(K,E)`. For complete `E`, the
completion unit identifies this with `E`, naturally. Completeness is reflected by `r`,
so `F` also restricts to the complete subcategories.
5. For complete `M` over `B`, send a homogeneous `m` to the cochain
`k ↦ q(ε_B(k)m)`, zero off degree zero of `k`. This is a chain map because `ε_B d_K = 0`
and `q` is a chain map. It is `B`-linear under the action in step 3, and natural. After
precomposition with `u`, it is exactly the completion unit of `r M`. Hence its restriction
is an isomorphism by step 4; conservativity of restriction makes it an isomorphism over
`B`. These two natural isomorphisms exhibit the equivalence asserted here. -/
theorem flat_ringed_ideal_complete_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  sorry

end CategoryTheory
