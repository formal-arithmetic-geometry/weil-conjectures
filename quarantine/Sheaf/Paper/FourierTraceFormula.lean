/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.CommonStageFourierTransform
public import Sheaf.Paper.FourierTraceFunctions
import Sheaf.Paper.DerivedPullbackTensorIso
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.FourierTransform.Properties.Stalk
import Sheaf.Paper.FourierSetting
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.Paper.SfWeilSheafComplex
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius

/-! # The Fourier trace formula

Source: blueprint main-20261015, sec-fourier-transform/sk-thm-fourier-trace-formula;
Laumon, Transformation de Fourier, Theorem 1.2.1.2, p. 141
(blueprint: sk-thm-fourier-trace-formula).

Both sides use the recorded fixed-pair Weil category and its alternating local
Frobenius trace. The right side is the recorded classical finite-field transform.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The base-field character psi=Psi composed with Tr_(k0/Fp), using the recorded
trace-composition construction and the actual characteristic of the fixed base field.
Source: sk-def-char, used in the Fourier trace formula
(blueprint: sk-thm-fourier-trace-formula). -/
def fourierTraceBaseCharacter (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    AddChar F.field.k₀ F.coefficients.Qbar :=
  letI := fourierBaseCharacteristic F
  letI := (ZMod.castHom (dvd_refl F.field.p) F.field.k₀).toAlgebra
  Ψ.compTrace F.field.k₀

/-- An element x of the specified subfield F_(q^n) gives the rational point of A1
whose coordinate is x. This uses the specified base-field inclusion, so it retains
all extension-field points, including zero.
Source: the point convention in sk-def-trace and sk-thm-fourier-trace-formula
(blueprint: sk-thm-fourier-trace-formula). -/
def fourierAffineExtensionPoint (F : FourierSetting.{u}) (n : ℕ) (hn : 1 ≤ n)
    (x : F.field.extensionSubfield n hn) :
    F.field.extensionPoints (fourierAffineModel F PUnit.{u + 1}) n hn :=
  Over.homMk
    (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (F.field.extensionEmbedding n hn)))
      (fun _ ↦ (Scheme.ΓSpecIso (.of (F.field.extensionSubfield n hn))).inv.hom x))
    (AffineSpace.homOfVector_over _ _)

/-- P8, the Fourier trace formula, for the actual adic fixed-pair Weil complexes.
Source: blueprint main-20261015, sk-thm-fourier-trace-formula/_section.md;
Laumon Theorem 1.2.1.2, p. 141 (blueprint: sk-thm-fourier-trace-formula).

Proof plan:
1. Use sk-def-fourier-set and def-fd-transform at rank one. Descend the Weil
complex and character to one finite coefficient field containing their values.
The six-functor package prop-functor-package and lem-fix-weil-operations supply
bounded constructibility and the natural Weil structures on the integrand and image.
2. At y in F_(q^n), lem-fd-stalk-formula identifies the transform stalk with
compact-support cohomology of the y-fibre, shifted by [1]. Iterate the Weil map n
times. The square is defined over F_(q^n), so exchange is equivariant for the
actual returned geometric point, including the point transports of
 def-weil-local-frobenius-trace, rather than fixing that point pointwise.
3. Apply thm-weil-grothendieck-lefschetz-trace over F_(q^n) to the Weil integrand
on A1 and exponent one. The alternating compact-support trace is its finite sum
of local traces. This uses the general Weil-complex formula, with no weight assumption.
4. The general-function closed-point clause of sk-lem-as-properties identifies
the kernel scalar at x with Psi(Tr_(F_(q^n)/Fp)(xy)), equivalently
psi(Tr_(F_(q^n)/k0)(xy)) by sk-def-char. This includes y=0 and scalar one.
5. By lem-pur-derived-pullback-tensor-iso and lem-fix-weil-operations the stalk is
the tensor of K's stalk with that degree-zero line, with tensor Frobenius. A basis
of the line multiplies the matrix of each cohomological Frobenius by its scalar.
The alternating trace of sk-def-trace is therefore t_K(x) times that scalar.
6. Reindex the finite cohomological sum by i=j+1. The shift [1] contributes minus
one, giving the negative classical transform. Coefficient comparisons in
prop-functor-package put the coefficient-independent equality in Qbar. -/
theorem fourierTraceFormula (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (c : Compactification (fourierModelSnd F PUnit.{u + 1}).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F PUnit.{u + 1}) F.coefficients.Qbar)
    (n : ℕ) (hn : 1 ≤ n) (y : F.field.extensionSubfield n hn) :
    weilTraceFunction F.field F.coefficients.l F.coefficients.different F.coefficients.Qbar
      (fourierAffineModel F PUnit.{u + 1})
      (affineCommonStageFourierTransform F PUnit.{u + 1} Ψ c K) n hn
      (fourierAffineExtensionPoint F n hn y) =
    -classicalFiniteFieldFourierTransform F (fourierTraceBaseCharacter F Ψ) n hn
      (fun x ↦ weilTraceFunction F.field F.coefficients.l F.coefficients.different
        F.coefficients.Qbar (fourierAffineModel F PUnit.{u + 1}) K n hn
        (fourierAffineExtensionPoint F n hn x)) y := by
  sorry

end WeilConjectures
