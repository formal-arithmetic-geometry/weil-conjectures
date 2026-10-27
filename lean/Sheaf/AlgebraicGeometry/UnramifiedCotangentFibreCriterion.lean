module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialsAffineSections
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Unramified neighbourhoods and the relative cotangent fibre

Source: Stacks Project, Morphisms, Tag 02GF, Lemma `lemma-unramified-at-point`,
equivalence of (1) and (5) (blueprint: lem-sfb-unramified-cotangent-fibre-criterion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A locally finite type scheme morphism is unramified on an open neighbourhood of a
point exactly when its relative differential stalk tensored with the residue field is zero.
The point is arbitrary; no Noetherian, flatness, or residue-field perfection is required.

Source: Stacks Project, Morphisms, Tag 02GF, equivalence of (1) and (5).
(blueprint: lem-sfb-unramified-cotangent-fibre-criterion).

Proof:
1. By `lem-trf-relative-differential-sheaf-base-change`, the differential sheaf is
   quasi-coherent and of finite type. Choose affine neighbourhoods Spec A of x and Spec R
   of f(x). By `lem-sc-relative-differentials-affine-sections` and
   `lem-weil-pbc-finite-type-module-support-closed`, its sections are the finite A-module
   M = Omega(A/R), and its stalk is M localized at the prime of x. Localizing generators
   shows that this stalk is finite over the local ring at x.
2. An unramified neighbourhood has affine charts of finite type with zero relative
   differentials, by `def-weil-unramified-morphism`. By
   `def-sc-relative-differential-sheaf`, the differential sheaf, its stalk, and hence
   its tensor with the residue field vanish there.
3. Conversely, identify the tensor with residue-field extension of scalars by symmetry. Apply
   `lem-weil-pbc-nakayama-local-generators` to the empty family of the finite stalk
   module: its residue vector space is zero, so the stalk itself is zero.
4. The annihilator criterion of `lem-weil-pbc-finite-type-module-support-closed`
   supplies g in Ann(M) outside the prime of x. Thus M localized at g is zero:
   m/g^r = (gm)/g^(r+1) = 0. By
   `lem-weil-pbc-kahler-differentials-localization`, Omega(A_g/R) is zero.
5. By `lem-weil-pbc-affine-open-section-vanishing-prime`, D(g) is an affine open
   containing x with coordinate ring A_g. Adjoining 1/g to generators of A over R
   proves that A_g is finite type over R. Its zero differentials make the restriction
   to D(g) unramified by `def-weil-unramified-morphism`, giving the neighbourhood. -/
theorem unramified_neighbourhood_iff_cotangent_fibre_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (x : X) :
    (∃ W : X.Opens, x ∈ W ∧ IsUnramified (W.ι ≫ f)) ↔
      Subsingleton ((ModuleCat.extendScalars (X.residue x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj f.relativeDifferentials)) := by
  sorry

end AlgebraicGeometry
