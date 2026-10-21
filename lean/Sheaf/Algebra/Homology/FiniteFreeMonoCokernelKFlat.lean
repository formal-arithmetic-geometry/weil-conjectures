/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-!+# Normalized finite-free cokernel resolutions on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 06YQ; Homology, Tag 0115;
Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat).

The cone of the degree-zero map represents the two-term complex with differential `+u`.
Its augmentation uses the specified cokernel projection, without choosing another map.
-/

@[expose] public section

set_option autoImplicit false

universe a b u v r

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

section Construction

variable {A : Type a} [Category.{b} A] [Abelian A]

/-- The two-term complex of a morphism, represented by the canonical cone on its
degree-zero single complex. Under the canonical identifications its terms are `P` in
degree `-1`, `Q` in degree `0`, and zero elsewhere; its differential is `+u`.
Source: Stacks Project, Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelComplex {P Q : A} (u : P ⟶ Q) : CochainComplex A ℤ :=
  mappingCone ((singleFunctor A 0).map u)

/-- The specified quotient augmentation: zero on the shifted source summand and the
given projection on the unshifted target summand. `S.zero` is exactly the condition
that the projection kills the differential; no exactness is needed to construct it.
Source: Stacks Project, Derived Categories, discussion before Tag 0152
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelAugmentation (S : ShortComplex A) :
    monoCokernelComplex S.f ⟶ (singleFunctor A 0).obj S.X₃ :=
  mappingCone.descShortComplex (S.map (singleFunctor A 0))

end Construction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- A monomorphism between specified finite direct sums of the regular module sheaf
has the normalized K-flat cokernel resolution, for arbitrary coefficients on a small site.
`S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g` are respectively `P`, `Q`, `T`, `u`, `q`.
The cokernel universal property retains the supplied projection, not just its object.
The last equation records the positive differential using the canonical cone inclusions.
Source: Stacks Project, Cohomology on Sites, Tag 06YQ; Homology, Tag 0115;
Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat).

Proof:
1. In the abelian category of module sheaves, monicity of `S.f` and the cokernel
   universal property give the short exact sequence `0 → P → Q → T → 0`
   (def-weil-sheaf-of-modules-category). The single functor puts it in degree zero
   (def-pc-cochain-complex-modules). The relation `S.zero` constructs the augmentation.
2. The cone differential is `(d_Q,u;0,-d_P)` (def-weil-abstract-derived-category).
   Single complexes have zero differentials, so only `+u` in degrees `-1,0` remains.
   The unshifted-summand inclusion has degree-zero component the identity of `Q`.
3. Apply lem-pc-cone-short-exact-quasi-iso to that short exact sequence of complexes.
   Its canonical cone map is exactly monoCokernelAugmentation; it is a quasi-isomorphism
   (def-pc-quasi-iso-modules). Its composite with the inclusion is the given `q[0]`.
4. The tensor unit isomorphism (lem-pc-sheaf-modules-tensor-closed) makes the regular
   module flat (def-pc-flat-sheaf-modules).
5. By lem-pc-sites-modules-coproduct-flat, both finite sums are flat, including rank zero.
   Transport along the specified isomorphisms gives flatness of `P,Q`. The empty sum
   also gives flatness of zero. Thus every term of all three displayed complexes is flat.
6. They all vanish above degree zero. Apply lem-pc-bounded-above-flat-kflat-site
   separately to each. By def-pc-kflat-complex the specified quasi-isomorphism is a
   K-flat resolution. No flatness of the cokernel, scalar origin of `u`, or constant
   origin of `R` is used. -/
theorem finite_free_mono_cokernel_kflat
    (S : ShortComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    [Mono S.f] (hq : IsColimit (CokernelCofork.ofπ S.g S.zero)) (m n : ℕ)
    (eP : S.X₁ ≅ ∐ (fun (_ : Fin m) ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (eQ : S.X₂ ≅ ∐ (fun (_ : Fin n) ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) :
    QuasiIso (monoCokernelAugmentation S) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        ((monoCokernelComplex S.f).X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        (((singleFunctor _ 0).obj S.X₁).X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        (((singleFunctor _ 0).obj S.X₂).X i)) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) (monoCokernelComplex S.f) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) ((singleFunctor _ 0).obj S.X₁) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) ((singleFunctor _ 0).obj S.X₂) ∧
      IsKFlatResolutionIndependentCoefficients (J := J) (R := R)
        (monoCokernelAugmentation S) ∧
      mappingCone.inr ((singleFunctor _ 0).map S.f) ≫ monoCokernelAugmentation S =
        (singleFunctor _ 0).map S.g ∧
      (mappingCone.inl ((singleFunctor _ 0).map S.f)).v 0 (-1) rfl ≫
          (monoCokernelComplex S.f).d (-1) 0 =
        ((singleFunctor _ 0).map S.f).f 0 ≫
          (mappingCone.inr ((singleFunctor _ 0).map S.f)).f 0 := by
  sorry

end CochainComplex
