/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.FrobeniusFixedPoints
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace

/-! # Scheme Frobenius fixes the canonical extension-valued geometric point

Source: latest blueprint, thm-trf-frobenius-fixed-points, rational-point summands
(blueprint: thm-trf-frobenius-fixed-points).

The full fixed-scheme theorem remains public. This exposes its fixed-point equation
for the already constructed fibre-product lift, so consumers need no extra equality
hypothesis and make no choice of a geometric lift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The geometric point obtained using the fixed inclusion F_(q^m) into k is fixed
by Phi^m. This is the rational-point summand clause of the fixed-scheme theorem,
expressed for the canonical fibre-product lift rather than an existential summand.
Source: latest blueprint, thm-trf-frobenius-fixed-points, rational-point decomposition
(blueprint: thm-trf-frobenius-fixed-points).

Proof: the summand indexed by x in the fixed-point decomposition has second
projection id_s and first projection Spec(F_(q^m) -> k) followed by x. The universal
property of the geometric fibre identifies this summand map with localExtensionPoint.
The defining pullback of the graph against the diagonal makes that summand map an
equalizer of Phi^m and the identity. Substitution gives the displayed equality.
Equivalently, on each affine chart its coordinates belong to F_(q^m), so their q^m
powers equal themselves; the chart equalities glue. No smoothness is required.
-/
theorem rationalPoint_schemeFrobenius_fixed (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (x : D.extensionPoints X₀ m hm) :
    localExtensionPoint D X₀ m hm x ≫ D.schemeFrobeniusIterate X₀ m =
      localExtensionPoint D X₀ m hm x := by
  have H := frobenius_fixed_points D X₀ m hm
  dsimp only at H
  obtain ⟨e, _, hy, _⟩ := H
  have hyx := hy x
  let g : Spec (.of D.k) ⟶ _ :=
    Sigma.ι (fun _ : D.extensionPoints X₀ m hm => Spec (.of D.k)) x ≫ e.inv
  have hg : g ≫ trfEndomorphismFixedInclusion _ _ =
      localExtensionPoint D X₀ m hm x := by
    apply pullback.hom_ext
    · dsimp [g, localExtensionPoint]
      rw [Category.assoc, pullback.lift_fst]
      simpa [Category.assoc, trfEndomorphismFixedInclusion] using hyx.2
    · dsimp [g, localExtensionPoint]
      rw [Category.assoc, pullback.lift_snd]
      simpa [Category.assoc, trfEndomorphismFixedInclusion,
        FiniteFieldDatum.geometricFiber] using hyx.1
  have hfix := (trfEndomorphismFixedScheme_equalizer _ _
      (Spec (.of D.k)) (localExtensionPoint D X₀ m hm x)).1 g
  rw [hg] at hfix
  exact hfix


end WeilConjectures
