module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Field.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.CategoryTheory.RingedSiteModules

/-! # Ampleness on a finite coproduct with integral point summands

Source: Stacks Project, Properties, Tag 01PS, `definition-ample`, and Varieties,
Tag 0B5Y, `lemma-ampleness-in-terms-of-degrees-components`
(blueprint: lem-trf-finite-coproduct-ample-with-points).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Integral zero-dimensional summands are spectra of fields, and every invertible module
on them is ample. On a finite disjoint union with such summands, absolute ampleness is
therefore equivalent to ampleness on the other summands. The inclusions of those other
summands are `Sigma.ι Y i ≫ coprod.inl`.

Source: Stacks Project, Properties, Tag 01PS, `definition-ample`, applied to a finite
clopen cover; Varieties, Tag 0B5Y, `lemma-ampleness-in-terms-of-degrees-components`
(blueprint: lem-trf-finite-coproduct-ample-with-points).

Proof:
1. An integral scheme is nonempty and irreducible. By scheme sobriety it has a unique
   generic point. Dimension zero forces the closure of every point to be the whole
   scheme, since a proper irreducible closed subset would give a chain of length one.
   Thus each P j has just one point (lem-sc-scheme-sober and
   def-kun-topological-krull-dimension).
2. An affine neighbourhood of that point is the whole scheme. Its local ring is a field
   by lem-sc-integral-function-field-affine-fraction. The germ map from global sections
   is an isomorphism, since there is only one open neighbourhood, identifying P j with
   the spectrum of that field (def-weil-pbc-module-stalk and def-weil-affine-spectrum).
3. A local frame of an invertible module on P j is global. Its nonvanishing open is the
   entire affine singleton; exponent one verifies 01PS. Pullbacks of L to these summands
   are invertible by lem-weil-pbc-invertible-pullback-invertible.
4. Each coprojection has clopen image and is affine by lem-trf-closed-embedding-affine.
   Hence ampleness of L implies ampleness on Y i by
   lem-weil-pbc-pullback-ample-invertible.
5. Conversely, ample Y i and singleton P j are quasi-compact. Finiteness of both index
   sets makes their disjoint union quasi-compact, by taking finite subcovers on each
   summand (lem-weil-pbc-scheme-coproduct-family).
6. At each point choose an ample positive-power section on its summand. Restriction is
   pullback (def-pc-module-pullback), and tensor powers commute with it by
   lem-weil-pbc-invertible-pullback-tensor. Glue that section to zero on the complementary
   clopen subscheme by the sheaf axiom (def-weil-sheaf-of-modules-category). Its
   nonvanishing open is the same affine open as on the summand. This proves 01PS for L.
   When both index sets are empty, the pointwise condition is vacuous; empty Y i do
   not affect either finite subcovers or the section argument. -/
theorem finite_coproduct_isAmple_iff_with_points
    {I : Type v} {J : Type w} [Finite I] [Finite J]
    (Y : I → Scheme.{u}) (P : J → Scheme.{u}) [∀ j : J, IsIntegral (P j)]
    (hP : ∀ j : J, topologicalKrullDim (P j) = 0)
    (L : ((∐ Y) ⨿ (∐ P)).Modules) [L.IsInvertible] :
    (∀ j : J,
      (∃ (K : Type u) (_ : Field K), Nonempty (P j ≅ Spec (CommRingCat.of K))) ∧
      ∀ (N : (P j).Modules) (hN : N.IsInvertible), @IsAmple (P j) N hN) ∧
    (IsAmple ((∐ Y) ⨿ (∐ P)) L ↔
      ∀ i : I, ∃ h : ((tensorPullback (Sigma.ι Y i ≫ coprod.inl)).obj L).IsInvertible,
        @IsAmple (Y i) ((tensorPullback (Sigma.ι Y i ≫ coprod.inl)).obj L) h) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
