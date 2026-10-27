/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FourierAdicArtinSchreier
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.FourierTransform.AffineSpace
import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition
import Sheaf.Paper.QbarCompactSupportBaseChange
import WeilConjectures.FourierTransform.Properties.Stalk
import WeilConjectures.FourierTransform.ArtinSchreierCohomology
import Sheaf.Paper.SfRationalLocalGlobalPowerTorsion
import Sheaf.Paper.SfRationalBoundedConeTorsion
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Sheaf.Paper.CommonStageFourierTransform
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.FourierTransform.ArtinSchreier
import WeilConjectures.FourierTransform.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect

/-!
# The convolution of the Fourier kernels

Source: blueprint main-20261015, sec-fourier-transform/sk-prop-convolution-kernel,
lem-fd-convolution-kernel and its proof (blueprint: lem-fd-convolution-kernel).
All objects use the intrinsic adic common-stage coefficient category. The finite index
set labels the standard coordinates, and its cardinality is the rank r, including zero.
The standard basis identifies the dual affine space with the same coordinate scheme.

## Main definitions and statements

- `fourierConvolutionIntegrand`: the two completed pullbacks and their derived tensor.
- `fourierGeometricConvolution`: its unshifted adic compact-support image.
- `fourierDeltaKernel`: the twisted diagonal image, with optional second reflection.
- `fourierKernelConvolutionIso`: the two kernel identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.AffineSpace
namespace WeilConjectures

/-- The geometric base Spec k of the fixed Fourier setting.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricBase (F : FourierSetting.{u}) := Spec (.of F.field.k)

/-- Standard affine space V, identified with its dual by its standard coordinates.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricSpace (F : FourierSetting.{u}) (n : Type u) :=
  𝔸(n; fourierGeometricBase F)

/-- The structure map of the standard affine space.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricProjection (F : FourierSetting.{u}) (n : Type u) :=
  fourierGeometricSpace F n ↘ fourierGeometricBase F

/-- The product V times V over the geometric base.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricSquare (F : FourierSetting.{u}) (n : Type u) :=
  pullback (fourierGeometricProjection F n) (fourierGeometricProjection F n)

/-- The standard triple product, in the existing kernel-composition convention.
Source: kernel-composition and convolution-kernel proof Step 1
(blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricTriple (F : FourierSetting.{u}) (n : Type u) :=
  pullback
    (pullback.snd (fourierGeometricProjection F n) (fourierGeometricProjection F n))
    (pullback.fst (fourierGeometricProjection F n) (fourierGeometricProjection F n))

/-- The existing projection r13, with no change to the unshifted convolution convention.
Source: kernel-composition (blueprint: lem-fd-convolution-kernel). -/
abbrev fourierGeometricR13 (F : FourierSetting.{u}) (n : Type u) :=
  pullback.tripleProj₁₃ (fourierGeometricProjection F n)
    (fourierGeometricProjection F n) (fourierGeometricProjection F n)

/-- The product's structural morphism to the geometric base.
Source: convolution-kernel standard product (blueprint: lem-fd-convolution-kernel). -/
instance fourierSquareOver (F : FourierSetting.{u}) (n : Type u) :
    (fourierGeometricSquare F n).Over (fourierGeometricBase F) where
  hom := pullback.fst _ _ ≫ fourierGeometricProjection F n

/-- The triple product's structural morphism to the geometric base.
Source: convolution-kernel standard product (blueprint: lem-fd-convolution-kernel). -/
instance fourierTripleOver (F : FourierSetting.{u}) (n : Type u) :
    (fourierGeometricTriple F n).Over (fourierGeometricBase F) where
  hom := fourierGeometricR13 F n ≫ fourierGeometricSquare F n ↘ fourierGeometricBase F

/-- Standard finite-dimensional affine products are Noetherian.
Source: convolution-kernel finite rank hypothesis (blueprint: lem-fd-convolution-kernel).
Proof: a finite-dimensional affine space is finite type over a field, and so is its
square. A finite type scheme over a Noetherian field is Noetherian. -/
theorem fourierSquareNoetherian (F : FourierSetting.{u}) (n : Type u) [Finite n] :
    IsNoetherian (fourierGeometricSquare F n) := by
  sorry

/-- The structural properties needed by the already defined compact-support functor.
Source: convolution-kernel affine projections (blueprint: lem-fd-convolution-kernel).
Proof: the square and triple are affine spaces of ranks 2r and 3r. Their structural
maps are quasi-compact and finite type. The projection r13 is an affine-space
projection, hence separated, quasi-compact and finite type. Its structural triangle
commutes by the definition of fourierTripleOver. -/
theorem fourierConvolutionGeometry (F : FourierSetting.{u}) (n : Type u) [Finite n] :
    LocallyOfFiniteType (fourierGeometricTriple F n ↘ fourierGeometricBase F) ∧
    QuasiCompact (fourierGeometricTriple F n ↘ fourierGeometricBase F) ∧
    LocallyOfFiniteType (fourierGeometricSquare F n ↘ fourierGeometricBase F) ∧
    QuasiCompact (fourierGeometricSquare F n ↘ fourierGeometricBase F) ∧
    (fourierGeometricR13 F n).IsOver (fourierGeometricBase F) ∧
    IsSeparated (fourierGeometricR13 F n) ∧
    LocallyOfFiniteType (fourierGeometricR13 F n) ∧
    QuasiCompact (fourierGeometricR13 F n) := by
  sorry

/-- The finite-field convention implies characteristic p on the pairing scheme.
Source: def-fourier-set and convolution-kernel statement
(blueprint: lem-fd-convolution-kernel).
Proof: a finite field of cardinality p^a has characteristic p, since a is positive.
The chosen algebraic closure has the same characteristic. Every k-algebra, hence
all global functions on V times V, has characteristic p. -/
theorem fourierPairingCharacteristic (F : FourierSetting.{u}) (n : Type u) :
    CharP Γ(fourierGeometricSquare F n, ⊤) F.field.p := by
  sorry

/-- The coefficient prime is invertible in the geometric base field.
Source: def-fourier-set (blueprint: lem-fd-convolution-kernel).
Proof: the finite-field cardinality determines characteristic p. The distinct prime l
is nonzero in k, hence is a unit in this field. -/
theorem fourierGeometricCoefficient_isUnit (F : FourierSetting.{u}) :
    IsUnit (F.coefficients.l : F.field.k) := by
  sorry

/-- The same scalar is a unit in every residue field of a k-scheme.
Source: def-fourier-set (blueprint: lem-fd-convolution-kernel).
Proof: apply the structure homomorphism from k to each residue field to the unit
fourierGeometricCoefficient_isUnit. This includes non-closed geometric points. -/
theorem fourierResidueCoefficient_isUnit (F : FourierSetting.{u}) (X : Scheme.{u})
    [X.Over (fourierGeometricBase F)] (x : X) :
    IsUnit (F.coefficients.l : X.residueField x) := by
  sorry

/-- The Fourier kernel of the standard evaluation pairing, at the actual adic stage.
Source: def-fd-kernel and convolution-kernel statement
(blueprint: lem-fd-convolution-kernel). -/
def fourierGeometricKernel (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (fourierGeometricSquare F n) :=
  letI := fourierPairingCharacteristic F n
  letI := fourierSquareNoetherian F n
  fourierAdicKernel F (fourierGeometricProjection F n) (fourierGeometricProjection F n)
    Ψ (stdPairing n (fourierGeometricBase F))

/-- The actual two-factor convolution integrand at the fixed integral stage.
The factors are the already defined kernels; no identification of their tensor product
with a character of x-y or x+y is built into this definition.
Source: kernel-composition and convolution-kernel proof Step 1
(blueprint: lem-fd-convolution-kernel). -/
def fourierConvolutionIntegrand (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (Ψ Ψ' : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    DerivedCategory (scalarReductionSource F.coefficients.l (fourierCoefficient F)
      (fourierGeometricTriple F n)) :=
  letI := fourierPairingCharacteristic F n
  (integralCompletedTensor F.coefficients.l (fourierCoefficient F)
    (fourierGeometricTriple F n)).obj
      (((integralDerivedPullback F.coefficients.l (fourierCoefficient F)
        (pullback.fst
          (pullback.snd (fourierGeometricProjection F n) (fourierGeometricProjection F n))
          (pullback.fst (fourierGeometricProjection F n) (fourierGeometricProjection F n)))).obj
            (fourierAdicArtinSchreier F (fourierGeometricSquare F n) Ψ
              (stdPairing n (fourierGeometricBase F)))),
       ((integralDerivedPullback F.coefficients.l (fourierCoefficient F)
        (pullback.snd
          (pullback.snd (fourierGeometricProjection F n) (fourierGeometricProjection F n))
          (pullback.fst (fourierGeometricProjection F n) (fourierGeometricProjection F n)))).obj
            (fourierAdicArtinSchreier F (fourierGeometricSquare F n) Ψ'
              (stdPairing n (fourierGeometricBase F)))))

/-- The convolution integrand belongs to the intrinsic integral category.
Source: convolution-kernel proof Step 1, rank-one finite-Tor kernel clause
(blueprint: lem-fd-convolution-kernel).
Proof: the integral kernels are completed rank-one lisse sheaves. Their pullbacks
are again such sheaves. Completed derived tensor is their rank-one tensor product,
whose reductions are locally free in degree zero and are compatible with reduction.
Thus they are derived complete, with constructible reductions uniformly in [0,0]. -/
theorem fourierConvolutionIntegrand_mem (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (Ψ Ψ' : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    sfIntegralConstructible F.coefficients.l (fourierCoefficient F)
      (fourierGeometricTriple F n) (fourierConvolutionIntegrand F n Ψ Ψ') := by
  sorry

/-- Unshifted convolution of the actual evaluation kernels: the published adic Rr13!
of the published completed tensor of the two pulled-back kernels, rationalized at E.
The compactification is arbitrary, with the same choice at every finite coefficient level.
Source: kernel-composition and convolution-kernel proof Step 1
(blueprint: lem-fd-convolution-kernel). -/
def fourierGeometricConvolution (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (Ψ Ψ' : AddChar (ZMod F.field.p) F.coefficients.Qbar)
    (c : Compactification (fourierGeometricR13 F n)) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (fourierGeometricSquare F n) :=
  letI := (fourierConvolutionGeometry F n).1
  letI := (fourierConvolutionGeometry F n).2.1
  letI := (fourierConvolutionGeometry F n).2.2.1
  letI := (fourierConvolutionGeometry F n).2.2.2.1
  letI := (fourierConvolutionGeometry F n).2.2.2.2.1
  letI := (fourierConvolutionGeometry F n).2.2.2.2.2.1
  letI := (fourierConvolutionGeometry F n).2.2.2.2.2.2.1
  letI := (fourierConvolutionGeometry F n).2.2.2.2.2.2.2
  sfQbarCompactSupportValue F.coefficients.l F.field.k
    (fourierGeometricCoefficient_isUnit F) F.coefficients.Qbar c (fourierCoefficientStage F)
    ⟨fourierConvolutionIntegrand F n Ψ Ψ', fourierConvolutionIntegrand_mem F n Ψ Ψ'⟩

/-- The automorphism id times iota', acting on the second coordinate.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
def fourierSecondReflection (F : FourierSetting.{u}) (n : Type u) :
    fourierGeometricSquare F n ⟶ fourierGeometricSquare F n :=
  pullback.map _ _ _ _ (𝟙 _) (neg n (fourierGeometricBase F)) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (neg_over n (fourierGeometricBase F)).symm)

/-- The integral diagonal delta object with twist -r. For sign=true, apply the ordinary
image of id times iota' as well. Both images are proper ordinary derived images.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
def fourierIntegralDelta (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (sign : Bool) : DerivedCategory (scalarReductionSource F.coefficients.l
      (fourierCoefficient F) (fourierGeometricSquare F n)) :=
  letI : ∀ x : fourierGeometricSpace F n,
      Invertible (F.coefficients.l : (fourierGeometricSpace F n).residueField x) :=
    fun x ↦ (fourierResidueCoefficient_isUnit F (fourierGeometricSpace F n) x).invertible
  if sign then
    (sfCompletedDerivedDirectImage F.coefficients.l (fourierCoefficient F)
      (fourierSecondReflection F n)).obj
      ((sfCompletedDerivedDirectImage F.coefficients.l (fourierCoefficient F)
        (pullback.diagonal (fourierGeometricProjection F n))).obj
        (integralCoefficientTwist F.field F.coefficients.l F.coefficients.different
          (fourierCoefficient F) (fourierGeometricSpace F n) (-(Fintype.card n : ℤ))))
  else
    (sfCompletedDerivedDirectImage F.coefficients.l (fourierCoefficient F)
      (pullback.diagonal (fourierGeometricProjection F n))).obj
      (integralCoefficientTwist F.field F.coefficients.l F.coefficients.different
        (fourierCoefficient F) (fourierGeometricSpace F n) (-(Fintype.card n : ℤ)))

/-- The proper images of the completed Tate line are constructible and complete.
Source: convolution-kernel proof Steps 7--8 (blueprint: lem-fd-convolution-kernel).
Proof: the diagonal is closed since V is separated. Second reflection is an
isomorphism, hence proper. Proper direct image preserves completeness and bounded
constructibility. The input is the recorded integral Tate line, with all reductions
in degree zero; these observations apply to either value of sign, also in rank zero. -/
theorem fourierIntegralDelta_mem (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (sign : Bool) : sfIntegralConstructible F.coefficients.l (fourierCoefficient F)
      (fourierGeometricSquare F n) (fourierIntegralDelta F n sign) := by
  sorry

/-- The actual diagonal or reflected diagonal image in the common-stage category.
Source: convolution-kernel statement (blueprint: lem-fd-convolution-kernel). -/
def fourierDeltaKernel (F : FourierSetting.{u}) (n : Type u) [Fintype n] (sign : Bool) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (fourierGeometricSquare F n) :=
  ⟨fourierCoefficientStage F,
    (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
      (fourierGeometricSquare F n)).obj
      ⟨fourierIntegralDelta F n sign, fourierIntegralDelta_mem F n sign⟩⟩

/-- The inverse-character convolution is the diagonal delta kernel, and the same-character
convolution is its image by reflection in the second coordinate. Both carry the actual
coefficient twist -r and the unshifted-convolution shift -2r, for r=card n.

Source: main-20261015 sk-prop-convolution-kernel/lem-fd-convolution-kernel,
including its completed eight-step proof (blueprint: lem-fd-convolution-kernel).

Proof (deferred):
1. Kernel composition and the pullback kernel description identify the integrands.
Multiplicativity and inverse Artin--Schreier identities give the characters of
<xi,x-y> and <xi,x+y>. Lisse finite-Tor stability puts them in the stated category.
2. Compact-support base change along each rational y-slice identifies the result
with the Fourier transform of its actual linear-character input, shifted by -r.
The Fourier stalk formula computes its geometric stalks over arbitrary residue fields.
3. On A1, rank-one duality and degreewise perfectness identify compact cohomology's
dual with ordinary cohomology of the inverse character and twist. The affine-line
character vanishing and finite dimensionality show that compact cohomology is zero.
4. For c=x-y or x+y, cover the complement of c=0 by D(c_i). The regular coordinates
t=sum c_j xi_j and u_j=xi_j for j different from i have the explicit inverse
xi_i=c_i^-1(t-sum_{j different from i}c_j u_j). Rank zero has empty complement.
5. Compact-support base change, composition and projection formula on each chart
reduce the convolution to the zero compact cohomology of Step 3, using the
coefficient-transported affine-space Thom formula in rank r-1.
6. Move the finitely many chart identities to one coefficient stage. Rational
local-global power torsion and bounded-cone torsion show vanishing on the entire
open complement, including the empty complement.
7. On c=0 the two kernel factors are tensor inverses as sheaves over the whole
relative scheme. Closed base change and transported Thom give the constant line
with twist -r and shift -2r on that closed support.
8. The actual open-closed unit is an isomorphism because its open term vanishes.
The closed supports identify with V by x mapped to (x,x) and (x,-x). Proper image
composition gives the displayed two identities. In characteristic two the supports
coincide; in rank zero both are the coefficient unit on a point. -/
theorem fourierKernelConvolutionIso (F : FourierSetting.{u}) (n : Type u) [Fintype n]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (c : Compactification (fourierGeometricR13 F n)) :
    Nonempty (fourierGeometricConvolution F n Ψ Ψ⁻¹ c ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj (fourierDeltaKernel F n false)) ∧
    Nonempty (fourierGeometricConvolution F n Ψ Ψ c ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj (fourierDeltaKernel F n true)) := by
  sorry

end WeilConjectures
