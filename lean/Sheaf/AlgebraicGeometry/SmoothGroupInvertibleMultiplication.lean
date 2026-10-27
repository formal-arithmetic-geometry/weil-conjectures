/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SpaceLfpFormallyEtaleCriterion
import Sheaf.AlgebraicGeometry.SpaceEtaleSourceAtlasDetection
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # Invertible multiplication on a smooth commutative group algebraic space

Source: Stacks Project, Groupoids, Tags 0BF5 and 0BFH; More on Morphisms of Spaces,
Tags 04AM and 0616; Spaces, Tag 02X2
(blueprint: lem-sfb-smooth-group-invertible-multiplication).

The group law uses multiplicative notation, so the source's `[n]` is `x ↦ x ^ n`.
The kernel is the actual sheaf fibre product. Its base-change assertion is its
pullback universal property after restriction from S-schemes to S'-schemes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction on points as a homomorphism of the given commutative groups.
Source: the natural group law in Stacks, Groupoids, Tag 0BF5
(blueprint: lem-sfb-smooth-group-invertible-multiplication). -/
def CommutativeSpaceGroup.restrictionHom {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : CommutativeSpaceGroup G) {T U : (Over S)ᵒᵖ} (f : T ⟶ U) :
    @MonoidHom (G.obj.obj.obj T) (G.obj.obj.obj U)
      (H.group T).toMulOne (H.group U).toMulOne :=
  letI := H.group T
  letI := H.group U
  { toFun := G.obj.obj.map f
    map_one' := H.map_one f
    map_mul' := H.map_mul f }

/-- Multiplication by n, written as n-th power for the existing multiplicative group law.
This is defined pointwise, with naturality supplied by the restriction homomorphisms.
Source: Stacks, Groupoids, Tag 0BFH, multiplication morphism
(blueprint: lem-sfb-smooth-group-invertible-multiplication). -/
def CommutativeSpaceGroup.npow {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : CommutativeSpaceGroup G) (n : ℕ) : G ⟶ G :=
  ObjectProperty.homMk ⟨{
    app := fun T ↦ ↾fun x ↦ @NPow.npow _ (H.group T).toNPow n x
    naturality := by
      intro T U f
      ext x
      let := H.group T
      let := H.group U
      exact ((H.restrictionHom f).map_pow x n).symm }⟩

/-- The n-torsion kernel, as the sheaf fibre product of multiplication by n and identity.
Its data come from the existing fibre-product construction, with no choice of a space.
Source: Stacks, Spaces, Tag 02X2; Groupoids, Tag 0BFH, kernel of multiplication
(blueprint: lem-sfb-smooth-group-invertible-multiplication). -/
def CommutativeSpaceGroup.torsionSpace {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : CommutativeSpaceGroup G) (n : ℕ) : AlgebraicSpace S :=
  enlargedFibreProduct (H.npow n) H.identity

/-- The canonical inclusion of the n-torsion kernel into the given group space.
Source: Stacks, Spaces, Tag 02X2; Groupoids, Tag 0BFH
(blueprint: lem-sfb-smooth-group-invertible-multiplication). -/
def CommutativeSpaceGroup.torsionInclusion {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : CommutativeSpaceGroup G) (n : ℕ) : H.torsionSpace n ⟶ G :=
  enlargedFibreProductFst (H.npow n) H.identity

/-- If n is positive and invertible in every local ring of the base, multiplication
by n on a smooth commutative group algebraic space is etale. Its kernel is an etale
commutative group algebraic space, with group law induced from G, and the kernel square
remains a pullback after every base change S' → S. No properness or finiteness is assumed.

Source: Stacks, Groupoids, Tags 0BF5 and 0BFH, generalized by the affine infinitesimal
criterion, More on Morphisms of Spaces, Tags 04AM and 0616; Spaces, Tag 02X2
(blueprint: lem-sfb-smooth-group-invertible-multiplication).

Proof: (1) Smoothness gives local finite presentation on charts. The chart criterion
[lem-sfb-space-local-properties-chart-test] and relative permanence
[lem-sfb-space-relative-lfp-permanence], with X = Y = G and Z = S, give local finite
presentation of [n].
(2) For an affine square-zero test with ideal I, the kernel of G(T) → G(T₀) is an
A/I-module, and [n] on this kernel is scalar multiplication by n
[lem-sfb-group-space-square-zero-kernel-module]. Stalkwise inverses of n glue uniquely
on S, hence pull back to an inverse scalar on T₀. Thus [n] on this module is bijective.
(3) Lift x₀ smoothly across the thickening
[lem-sfb-smooth-space-affine-infinitesimal-lift]. Correct any lift x by the unique
kernel element k with n k = y - n x. Then x + k is the desired lift; the difference
of two such lifts lies in the module kernel and is killed by n, so is zero.
(4) Apply [lem-sfb-space-lfp-formally-etale-criterion] to obtain etaleness of [n].
(5) Convert to chartwise etaleness using compatible etale charts
[lem-sfb-unramified-etale-compatible-charts], scheme etale base change
[lem-weil-pbc-etale-scheme-base-change], and atlas detection
[lem-trf-space-etale-source-atlas-detection]. Form the kernel using
[lem-trf-space-fibre-products-etale-covers]; its projection to S is etale by
[lem-trf-space-chartwise-etale-permanence]. On every test scheme its points are precisely
those x with n x = 0. Multiplication, identity and inverse restrict to these subsets,
naturally in the test scheme, giving the asserted group law and inclusion homomorphisms.
For any S' → S, restriction evaluates these same kernels on S'-schemes. Matching pairs
still have a unique lift, so the restricted square is a pullback. This identifies
G[n] ×_S S' canonically with G_{S'}[n], compatibly with its inclusion and group law. -/
theorem smoothGroup_invertible_multiplication {S : Scheme.{u}} (G : AlgebraicSpace S)
    (H : CommutativeSpaceGroup G)
    (hsmooth : MapIsLocally (@Smooth) (groupSpaceProjection G))
    (n : ℕ) (hn : 1 ≤ n) (hunit : ∀ s : S, IsUnit (n : S.presheaf.stalk s)) :
    MapIsLocally (@Etale) (H.npow n) ∧
    MapIsLocally (@Etale) (groupSpaceProjection (H.torsionSpace n)) ∧
    (∃ K : CommutativeSpaceGroup (H.torsionSpace n),
      (∀ T : (Over S)ᵒᵖ,
        (H.torsionInclusion n).hom.hom.app T (@One.one _ (K.group T).toOne) =
          @One.one _ (H.group T).toOne) ∧
      ∀ (T : (Over S)ᵒᵖ) (x y : (H.torsionSpace n).obj.obj.obj T),
        (H.torsionInclusion n).hom.hom.app T (@Mul.mul _ (K.group T).toMul x y) =
          @Mul.mul _ (H.group T).toMul
            ((H.torsionInclusion n).hom.hom.app T x)
            ((H.torsionInclusion n).hom.hom.app T y)) ∧
    ∀ B : Over S,
      IsPullback
        (Functor.whiskerLeft (Over.map B.hom).op (H.torsionInclusion n).hom.hom)
        (Functor.whiskerLeft (Over.map B.hom).op
          (Limits.pullback.snd (H.npow n).hom H.identity.hom).hom)
        (Functor.whiskerLeft (Over.map B.hom).op (H.npow n).hom.hom)
        (Functor.whiskerLeft (Over.map B.hom).op H.identity.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
