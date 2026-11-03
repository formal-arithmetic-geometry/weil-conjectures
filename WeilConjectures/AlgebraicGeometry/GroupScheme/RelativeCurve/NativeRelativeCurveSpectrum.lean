/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
import WeilConjectures.DeligneLaumon.Reduction.TraceReality

/-! # The native fibre cohomology range and top factor

Source: latest blueprint, lem-zl-relative-envelope-factor-reality.
(blueprint: lem-zl-native-relative-curve-spectrum)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeCurve

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [hYsep : IsSeparated Y₀.hom]
  (h₀ : U₀ ⟶ Y₀) [hSmooth : SmoothOfRelativeDimension 1 h₀.left]
  [hSep : IsSeparated h₀.left] [hQC : QuasiCompact h₀.left]
  (hAffine : ∀ y : Y₀.left, IsAffine (h₀.left.fiber y))
  (c₀ : Compactification h₀.left) (E : NativeL2.WeilModule D l U₀)
  (hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) E.carrier)
  (iota : PadicAlgCl l →+* ℂ)

include hl hYsep hSmooth hSep hQC hAffine hLisse

/-- The affine curve has only degrees one and two, with finite fibres and pure top factor.
Source: latest blueprint, lem-zl-relative-envelope-factor-reality.proof.md, first paragraph;
lem-a1-affine-hc0, lem-zl-affine-curve-range and lem-zl-affine-curve-hc2-purity.
(blueprint: lem-zl-native-relative-curve-spectrum)

Proof: use condensed compact-support base change at the geometric closed point,
including its degree-d Frobenius equivariance. The geometric affine fibre is a
smooth curve, possibly empty or disconnected. Degree-zero compact cohomology of
a lisse sheaf vanishes on each nonproper curve component, and compact cohomology
vanishes above dimension two. The finite clopen component decomposition gives these
vanishings for the whole fibre, and constructibility gives finite-dimensionality.
For degree two pass to a finite residue extension defining each component, apply
top-factor purity on the smooth connected affine curve, then descend the weight
by the power-eigenvalue formula. Transport back along the equivariant base-change
map, including the empty fibre, where every vector space is zero.
-/
theorem native_relative_curve_spectrum
    (hPure : NativeL2.Pure D l U₀ E iota 0)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (∀ i : ℕ, FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (NativeCondensedModule.fibre l D (higherShriek D l h₀ c₀ E i).carrier
        (NativeCondensedModule.localClosedPoint D Y₀ y ι hι))) ∧
    (∀ i : ℕ, i ≠ 1 → i ≠ 2 → Subsingleton
      (NativeCondensedModule.fibre l D (higherShriek D l h₀ c₀ E i).carrier
        (NativeCondensedModule.localClosedPoint D Y₀ y ι hι))) ∧
    ∀ α : ULift.{u + 1} (PadicAlgCl l),
      Module.End.HasEigenvalue
        (NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 2) y ι hι).hom α →
      ‖iota α.down‖ = (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (1 : ℝ) := by
  sorry

end WeilConjectures.RelativeCurve
