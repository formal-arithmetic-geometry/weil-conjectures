/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Exact.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.Algebra.Homology.FlatResolutionTorComparison
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.SpectralSequence.Basic
import WeilConjectures.CategoryTheory.Abelian.Filtration
import Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence

/-!
# The integral bounded Kunneth short exact sequence

Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact).

`ModuleCat (ULift ℤ)` represents abelian groups in any universe: the scalar action is the
unique integral action, transported along the ring isomorphism `ULift ℤ ≃+* ℤ`.
The lift allows the coefficient ring and module carriers to have the same universe,
as required by the existing module tensor. Coproducts here are direct sums.
The tensor on the derived category is the existing K-flat derived monoidal tensor,
whose restriction to a fixed second complex computes the functor of Tag 06Y6.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

/-- Abelian groups of size `u`, encoded as modules over the canonically lifted integers.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
abbrev IntegralModuleCat : Type (u + 1) := ModuleCat.{u} (ULift.{u} ℤ)

variable [HasDerivedCategory.{w} IntegralModuleCat.{u}]

/-- The tensor direct sum in degree `r` of the integral Kunneth sequence.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTensorTerm (r : ℤ)
    (C D : Bounded IntegralModuleCat.{u}) : IntegralModuleCat.{u} :=
  ∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = r} ↦
    (homologyFunctor IntegralModuleCat.{u} p.val.1).obj C.obj ⊗
      (homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj

/-- The Tor-one direct sum, indexed by total cohomological degree `r + 1`.
Source: Stacks Project, Tag 0H80 (blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTorTerm (r : ℤ)
    (C D : Bounded IntegralModuleCat.{u}) : IntegralModuleCat.{u} :=
  ∐ fun p : {p : ℤ × ℤ // p.1 + p.2 = r + 1} ↦
    ((Tor' IntegralModuleCat.{u} 1).obj
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).obj C.obj)).obj
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj)

/-- The direct sum of the ordinary tensor maps induced by two derived morphisms.
Source: Stacks Project, Tags 0H7Z/0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTensorMap (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    integralKunnethTensorTerm r C D ⟶ integralKunnethTensorTerm r C' D' :=
  Limits.Sigma.map fun p ↦
    (homologyFunctor IntegralModuleCat.{u} p.val.1).map f.hom ⊗ₘ
      (homologyFunctor IntegralModuleCat.{u} p.val.2).map g.hom

/-- The direct sum of the first-variable-derived Tor maps induced by two morphisms.
Source: Stacks Project, Tags 00LY and 0H7Z/0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact). -/
noncomputable def integralKunnethTorMap (r : ℤ)
    {C C' D D' : Bounded IntegralModuleCat.{u}} (f : C ⟶ C') (g : D ⟶ D') :
    integralKunnethTorTerm r C D ⟶ integralKunnethTorTerm r C' D' :=
  Limits.Sigma.map fun p ↦
    ((Tor' IntegralModuleCat.{u} 1).map
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).map f.hom)).app
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).obj D.obj) ≫
    ((Tor' IntegralModuleCat.{u} 1).obj
      ((homologyFunctor IntegralModuleCat.{u} p.val.1).obj C'.obj)).map
        ((homologyFunctor IntegralModuleCat.{u} p.val.2).map g.hom)

/-- For bounded derived abelian groups the integral Kunneth sequence is short exact,
with both arrows natural in both derived arguments. No finite generation is assumed.
Source: Stacks Project, More on Algebra, Tags 0H7Z and 0H80
(blueprint: lem-kun-integral-bounded-kunneth-exact).

Proof (the five DAG steps):
1. Apply `lem-kun-bounded-tensor-tor-spectral-sequence` over the integers. Its second page
   is the direct sum of Tor in bidegree `(p,q)`, with Tor degree `-p` and `i+j=q`.
   It converges with a finite natural decreasing filtration to derived-tensor cohomology.
2. Resolve any abelian group M by the free group on its elements mapping onto M and
   its kernel. Both groups are torsion free, hence flat over the PID Z by
   `lem-weil-pbc-pid-torsion-free-module-flat`. This is a two-term flat resolution;
   `lem-pc-flat-resolution-tor-comparison` proves Tor vanishes in degrees at least two.
   Neither group needs to be finitely generated.
3. Only columns -1 and 0 of the spectral sequence remain. All differentials from page
   two onward have zero source or target, so the successor-page homology rule of
   `def-sp-spectral-sequence` gives canonical stationary-page identifications. Tor-zero
   is the ordinary tensor of `def-weil-pbc-tor-modules`.
4. In the finite decreasing filtration of `def-sp-filtration`, vanishing of the other
   graded pieces implies F^1=0 and F^{-1}=H^r. Inclusion of F^0 and the quotient by F^0
   give the sequence. The two graded identifications give precisely the tensor sum
   in degree r and the Tor-one sum in degree r+1.
5. Functoriality of the spectral sequence preserves F^0 and commutes with its graded
   identifications. The inclusion and quotient squares commute, and their outside
   maps are exactly the direct sums of cohomological tensor and Tor maps below.
   No choice of a splitting is made. -/
theorem integral_bounded_kunneth_exact (r : ℤ) :
    ∃ ι : ∀ C D : Bounded IntegralModuleCat.{u},
        integralKunnethTensorTerm r C D ⟶
          (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj),
    ∃ π : ∀ C D : Bounded IntegralModuleCat.{u},
        (homologyFunctor IntegralModuleCat.{u} r).obj (C.obj ⊗ D.obj) ⟶
          integralKunnethTorTerm r C D,
      (∀ C D : Bounded IntegralModuleCat.{u},
        Function.Injective (ι C D) ∧ Function.Exact (ι C D) (π C D) ∧
          Function.Surjective (π C D)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        integralKunnethTensorMap r f g ≫ ι C' D' =
          ι C D ≫ (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom)) ∧
      (∀ (C C' D D' : Bounded IntegralModuleCat.{u}) (f : C ⟶ C') (g : D ⟶ D'),
        (homologyFunctor IntegralModuleCat.{u} r).map (f.hom ⊗ₘ g.hom) ≫ π C' D' =
          π C D ≫ integralKunnethTorMap r f g) := by
  sorry

end DerivedCategory
