/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.FourierAdicArtinSchreier
public import Sheaf.Paper.CommonStageWeilShriek
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import WeilConjectures.WeilSheaf.Fourier

/-!
# The Fourier construction on common-stage Weil pairs

Source: blueprint main-20261015, sec-fourier-transform/sk-def-ft/_section.md,
with the adic convention of sk-def-fourier-set (blueprint: sk-def-ft).

The general ordinary-etale transform is the imported `Etale.fourierTransform`.
The helpers give its adic Weil-complex application using the recorded completed
Artin--Schreier kernel, pullback, tensor, and compact-support functors. Frobenius
on an arithmetic kernel is induced by its descent from the finite field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The coefficient prime is invertible on the arithmetic model as well as its fibre.
Source: sk-def-fourier-set, l different from p (blueprint: sk-def-ft).
Proof: the positive cardinality p^a determines characteristic p of k₀. The distinct
prime l is a nonzero element of k₀, hence a unit. Its image under the structure
homomorphism into every residue field is a unit. -/
theorem sfFourierArithmeticPrime_isUnit (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (x : X₀.left) :
    IsUnit (l : X₀.left.residueField x) := by
  sorry

/-- The existing first projection from the specified geometric fibre.
Source: sk-def-ft, base change of the arithmetic kernel (blueprint: sk-def-ft). -/
def sfFourierModelProjection : (D.geometricFiber X₀).left ⟶ X₀.left :=
  pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Pull back an arithmetic coefficient object, with its canonical descent Weil structure.
The structure is the inverse pullback-composition comparison followed by the equality
Fr composed with the model projection equals that projection. No Weil map is chosen.
Source: sk-def-ft and sk-def-fourier-set (blueprint: sk-def-ft). -/
def sfFourierArithmeticWeilObject
    (A : generalAlgebraicallyClosedConstructibleCategory l Ω X₀.left) :
    sfCommonStageWeilComplex D l hl X₀ Ω :=
  letI := fun x ↦ (sfFourierArithmeticPrime_isUnit D l hl X₀ x).invertible
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := Fintype.ofFinite D.k₀
  IsoAlgebra.mk
    ((commonStageDerivedPullback l Ω (sfFourierModelProjection D X₀)).obj A)
    (((zlPullComp l Ω (D.geometricFrobenius X₀).hom
      (sfFourierModelProjection D X₀)).symm).app A ≪≫
      eqToIso (congrArg
        (fun f ↦ (commonStageDerivedPullback l Ω f).obj A)
        (D.galoisMap_projections X₀.hom
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).1))

/-- Tensor the two actual common-stage carriers, with the tensor of their Weil maps.
The comparison is the normalized completed pullback/tensor comparison.
Source: sk-def-ft, the tensor factor (blueprint: sk-def-ft). -/
def sfFourierWeilTensor (K L : sfCommonStageWeilComplex D l hl X₀ Ω) :
    sfCommonStageWeilComplex D l hl X₀ Ω :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  IsoAlgebra.mk ((commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).obj
      (K.carrier, L.carrier))
    (canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X₀).hom
      K.carrier L.carrier ≪≫
      (commonStageDerivedTensor l Ω (D.geometricFiber X₀).left).mapIso
        (Iso.prod K.str L.str))

/-- The affine line as the existing finite-field scheme, bundled over k₀.
Source: sk-def-ft, rank one application (blueprint: sk-def-ft). -/
abbrev sfFourierLine (F : FourierSetting.{u}) : Over (Spec (.of F.field.k₀)) :=
  Over.mk (affineLine F.field.k₀ ↘ Spec (.of F.field.k₀))

/-- The existing arithmetic plane, with its inherited finite-field model.
Source: sk-def-ft, product of the two lines (blueprint: sk-def-ft). -/
abbrev sfFourierPlane (F : FourierSetting.{u}) : Over (Spec (.of F.field.k₀)) :=
  Over.mk (affinePlane F.field.k₀ ↘ Spec (.of F.field.k₀))

/-- The line is finite type over the fixed finite field.
Source: sk-def-ft, affine-line application (blueprint: sk-def-ft). -/
instance sfFourierLine_finiteType (F : FourierSetting.{u}) :
    LocallyOfFiniteType (sfFourierLine F).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineLine F.field.k₀ ↘ Spec (.of F.field.k₀)))

/-- The line is quasi-compact over the fixed finite field.
Source: sk-def-ft, affine-line application (blueprint: sk-def-ft). -/
instance sfFourierLine_quasiCompact (F : FourierSetting.{u}) :
    QuasiCompact (sfFourierLine F).hom :=
  inferInstanceAs (QuasiCompact (affineLine F.field.k₀ ↘ Spec (.of F.field.k₀)))

/-- The line is separated over the fixed finite field.
Source: sk-def-ft, affine-line application (blueprint: sk-def-ft). -/
instance sfFourierLine_separated (F : FourierSetting.{u}) :
    IsSeparated (sfFourierLine F).hom :=
  inferInstanceAs (IsSeparated (affineLine F.field.k₀ ↘ Spec (.of F.field.k₀)))

/-- The plane is finite type over the fixed finite field.
Source: sk-def-ft, product of the lines (blueprint: sk-def-ft). -/
instance sfFourierPlane_finiteType (F : FourierSetting.{u}) :
    LocallyOfFiniteType (sfFourierPlane F).hom :=
  inferInstanceAs (LocallyOfFiniteType (affinePlane F.field.k₀ ↘ Spec (.of F.field.k₀)))

/-- The actual first projection, as an arrow of finite-field models.
Source: sk-def-ft, p₁ (blueprint: sk-def-ft). -/
def sfFourierFst (F : FourierSetting.{u}) : sfFourierPlane F ⟶ sfFourierLine F :=
  Over.homMk (affinePlane.fst F.field.k₀) (comp_over _ _)

/-- The actual second projection, as an arrow of finite-field models.
Source: sk-def-ft, p₂ (blueprint: sk-def-ft). -/
def sfFourierSnd (F : FourierSetting.{u}) : sfFourierPlane F ⟶ sfFourierLine F :=
  Over.homMk (affinePlane.snd F.field.k₀) (comp_over _ _)

/-- The arithmetic product is finite type and Noetherian, with global characteristic p.
Source: sk-def-ft and sk-def-fourier-set (blueprint: sk-def-ft).
Proof: each projection is an affine-line projection. Thus the plane is finite type
over the finite field, hence Noetherian. Characteristic p of k₀ follows from its
cardinality p^a with a positive, and passes to its algebra of global functions. -/
theorem sfFourierPlane_geometry (F : FourierSetting.{u}) :
    QuasiCompact (sfFourierPlane F).hom ∧ IsNoetherian (sfFourierPlane F).left ∧
      CharP Γ((sfFourierPlane F).left, ⊤) F.field.p := by
  sorry

/-- The arithmetic evaluation kernel in the common-stage category, shifted by one.
It is the existing completed Artin--Schreier construction for b(x,y)=xy, rationalized
and included at the fixed coefficient field. Moving [1] into this kernel is the
canonical tensor/compact-support shift convention of the defining Fourier formula.
Source: sk-def-ft, affine-line formula (blueprint: sk-def-ft). -/
def sfFourierShiftedKernel (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (sfFourierPlane F).left :=
  letI := (sfFourierPlane_geometry F).2.1
  letI := (sfFourierPlane_geometry F).2.2
  let b := (affinePlane.fst F.field.k₀).appTop (AffineSpace.coord _ PUnit.unit) *
    (affinePlane.snd F.field.k₀).appTop (AffineSpace.coord _ PUnit.unit)
  GeneralAlgebraicallyClosedCoefficients.shiftPair 1
    ⟨fourierCoefficientStage F,
      (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
        (sfFourierPlane F).left).obj
        ⟨fourierAdicArtinSchreier F (sfFourierPlane F).left Ψ b,
          fourierAdicArtinSchreier_mem F (sfFourierPlane F).left Ψ b⟩⟩

/-- The Fourier transform on every common-stage Weil complex on the affine line.
This is precisely p₂!(p₁*K tensor Kψ)[1], with the shift moved into the kernel.
The kernel's Weil map is arithmetic descent, tensor uses the canonical monoidal
pullback comparison, and compact support uses the recorded open/proper Frobenius mates.
The prime-field character Ψ induces ψ=Ψ composed with Tr_(k₀/F_p), as in sk-def-char.
Source: sk-def-ft, rank one formula (blueprint: sk-def-ft). -/
def sfWeilFourierTransformObj (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar)
    (c : Compactification (sfFourierSnd F).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (sfFourierLine F) F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (sfFourierLine F) F.coefficients.Qbar :=
  letI := (sfFourierPlane_geometry F).1
  (zlComplexShriek F.field F.coefficients.l F.coefficients.different F.coefficients.Qbar
    (sfFourierSnd F) c).obj
    (sfFourierWeilTensor F.field F.coefficients.l F.coefficients.different
      F.coefficients.Qbar (sfFourierPlane F)
      ((IsoAlgebra.mapOfNatIso (zlFrobeniusSquare F.field F.coefficients.l
        F.coefficients.different F.coefficients.Qbar (sfFourierFst F))).obj K)
      (sfFourierArithmeticWeilObject F.field F.coefficients.l F.coefficients.different
        F.coefficients.Qbar (sfFourierPlane F) (sfFourierShiftedKernel F Ψ)))

end WeilConjectures
