/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjectionSupplement
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExactSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Exact tensor pullback for a flat morphism of ringed topoi

Source: Stacks Project, Modules on Sites, Tag 04JC, second assertion, and Tag 03ER(3).
(blueprint: lem-sfb-flat-ringed-topos-pullback-exact).

The functor is specified on both objects and morphisms by the existing sheafified
sectionwise tensor construction. No presenting-site functor is required. The algebraic
inverse-image presentation merely identifies the transported ring and module operations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory

namespace SheafOfModules

/-- Tensor pullback along a flat morphism of ringed topoi is additive and exact,
including preservation of kernels, cokernels and short exact sequences.

Source: Stacks Project, Tag 04JC, second assertion; flatness is Tag 03ER(3).
(blueprint: lem-sfb-flat-ringed-topos-pullback-exact).

Proof, following the four steps of the DAG:
1. Put R = RI = f⁻¹B. Apply lem-trf-geometric-inverse-image-exact with the sites
   interchanged. The transported module functor I.modules is exact. Its addition
   is transported through the finite-product comparison, so it is additive.
2. Flatness of A as an R-module is exactly exactness of N ↦ N tensor_R A.
   The balancing relations give inverse flips a tensor n ↔ n tensor a, natural
   in N. Thus the underlying R-module of extension of scalars is this exact
   tensor functor. On pure tensors extension of scalars preserves sums and zero.
3. By lem-weil-pbc-module-sheaves-colimits-forgetful, forgetting scalars preserves
   kernels and cokernels. The comparisons for extension become isomorphisms on
   underlying abelian sheaves. The inverse of an invertible A-linear map is
   A-linear, since u(ax) = a u(x); hence these comparisons are isomorphisms of
   A-module sheaves as well.
4. Compose inverse image and extension of scalars. The kernel and cokernel
   comparisons compose, and both factors are additive. In the abelian module
   categories a short exact row is a kernel followed by its cokernel, so its
   image is again short exact. The prescribed object and map equations below
   specify exactly this composite tensor pullback, with no arbitrary lift.
-/
theorem flat_ringedTopos_pullback_exact
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{w}) (B : Sheaf K CommRingCat.{w})
    (f : RingedToposMorphismOfUniverses
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj B))
    (RI : Sheaf J CommRingCat.{w}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : I.ringUnderlying.hom ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map c = f.ringMap)
    (hflat : IsFlatOnSite.{uC, vC, w, w} (J := J) (R := RI) ((restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map c)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A)))) :
    ∃ (F : ringedSiteModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj B) ⥤
      ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj A))
      (hobj : ∀ M : ringedSiteModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj B),
        F.obj M = changeOfRingsOfUniverses c (I.modules.obj M))
      (_ : ∀ {M N : ringedSiteModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj B)} (a : M ⟶ N),
        F.map a = eqToHom (hobj M) ≫
          changeOfRingsHomOfUniverses c (I.modules.obj M) (I.modules.map a) ≫
            eqToHom (hobj N).symm)
      (hadd : F.Additive),
      exactFunctor _ _ F ∧
      ∀ S : ShortComplex (ringedSiteModules.{w}
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj B)),
        S.ShortExact →
          (@ShortComplex.map _ _ _ _ _ _ S F
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ F hadd)).ShortExact := by
  sorry

end SheafOfModules
