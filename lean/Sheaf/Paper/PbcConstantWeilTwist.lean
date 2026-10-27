/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.PbcWeilCoefficientComparison
public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.WeilTensorProduct
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation

/-! # Constant Weil lines in the actual PBC coefficient model

Source: blueprint, sec-purity-real-sheaves/sk-r-real-linear,
`def-wf-constant-weil-twist.md` (blueprint: def-wf-constant-weil-twist).

The integral representative is the completed coefficient ring in degree zero.
Scalar multiplication takes place only after rationalization. Thus nonintegral
units are allowed, and disconnected and empty schemes require no base point.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v z r
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor
namespace WeilConjectures

/-- Scalar multiplication by a unit, using the existing endomorphism algebra.
Source: blueprint constant-line Frobenius formula
(blueprint: def-wf-constant-weil-twist). -/
def constantTwistScalarIso {R : Type r} [CommRing R] {C : Type z} [Category.{v} C]
    [Preadditive C] [Linear R C] (b : Rˣ) (M : C) : M ≅ M :=
  Aut.unitsEndEquivAut M (Units.map (algebraMap R (End M)).toMonoidHom b)

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]

/-- Rescale theta at a finite stage, keeping precisely its original carrier.
The inverse uses b inverse; b need not preserve any integral lattice.
Source: blueprint constant-line Frobenius formula
(blueprint: def-wf-constant-weil-twist). -/
def sfFiniteConstantTwist (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (b : E.valˣ)
    (K : sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E)) :
    sfWeilComplex D c.l c.different X₀ (pbcFiniteField.{u} c.l c.Qbar E) :=
  IsoAlgebra.mk K.carrier (K.str ≪≫ constantTwistScalarIso
    (Units.map ((sfRationalCoefficientEquiv c.l (pbcFiniteField.{u} c.l c.Qbar E)).symm
      |>.toRingHom.toMonoidHom)
      (Units.map (Shrink.algEquiv ℚ_[c.l] E.val).symm.toRingHom.toMonoidHom b)) K.carrier)

variable [IsNoetherian (D.geometricFiber X₀).left]
  (S : FdCoefficientComparisonSystem.{u} c.l c.Qbar)

/-- The finite constant PBC Weil line is J(E_X,b theta_E), with J's specified
pullback comparison and the completed integral coefficient representative.
Source: blueprint constant-line construction
(blueprint: def-wf-constant-weil-twist). -/
def pbcFiniteConstantWeilLine (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ) :
    WeilD D c X₀ E :=
  (constantTwistFiniteComparison D c X₀ S E).obj
    (sfFiniteConstantTwist D c X₀ E b
      (constantWeilRationalComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
        D c.different X₀))

/-- Include the explicit line at its chosen coefficient stage in the PBC Weil colimit.
Source: blueprint constant-line construction
(blueprint: def-wf-constant-weil-twist). -/
def pbcConstantWeilLine (E : Padic.FiniteCoefficientFields c.l c.Qbar) (b : E.valˣ) :
    WeilDQbar D c X₀ :=
  ((weilScalarSystem D c X₀).ι E).obj (pbcFiniteConstantWeilLine D c X₀ S E b)

/-- Scalar multiplication at common stages is the uniquely lifted coefficient scalar
under J's fully faithful underlying equivalence. It therefore keeps the same carrier,
and uses exactly the common-stage scalar action of the PBC model.
Source: blueprint scalar Frobenius rescaling
(blueprint: def-wf-constant-weil-twist). -/
def sfCommonConstantTwist (b : c.Qbarˣ)
    (K : sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar) :
    sfCommonStageWeilComplex D c.l c.different X₀ c.Qbar :=
  IsoAlgebra.mk K.carrier (K.str ≪≫
    (S.coefficients (D.geometricFiber X₀).left).equivalence.functor.preimageIso
      (constantTwistScalarIso b
        ((S.coefficients (D.geometricFiber X₀).left).equivalence.functor.obj K.carrier)))

/-- Completed tensor with the explicit finite constant line, including the tensor
Frobenius. It is formed in the recorded ambient category; constructible-heart
membership is the conclusion of the comparison theorem, not an input assumption.
Source: blueprint constant Weil twist, final sentence
(blueprint: def-wf-constant-weil-twist). -/
def pbcFiniteConstantWeilTensor (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (b : E.valˣ) (K : WeilD D c X₀ E) :
    IsoAlgebra (wfAmbientFrobenius D c X₀ E) :=
  IsoAlgebra.mk
    ((wfTensor D c X₀ E).obj
      (wfWeilCarrier D c X₀ E K,
        wfWeilCarrier D c X₀ E (pbcFiniteConstantWeilLine D c X₀ S E b)))
    (wfTensorFrobenius D c X₀ E K (pbcFiniteConstantWeilLine D c X₀ S E b))

/-- The constant etale-adic presentation of the line uses the constant unit and
is uniquely normalized by multiplication by b on constant fibres. Quantifying over
all finite-fibre paths keeps the normalization independent of a lift or base point.
Source: current blueprint constant-module Frobenius formula
(blueprint: def-wf-constant-weil-twist).
Proof: the reindexing equivalence carries the constant finite quotient module sheaves
to themselves by their constant sections. These maps commute with reduction. Pass
to the inverse limit, extend scalars to the finite field and then to Q, and multiply
by b. A path fixes constants by its naturality for maps from the terminal cover;
hence every displayed fibre operator is b. Conversely stalk faithfulness determines
the sheaf arrow, and the fully faithful lisse localization determines theta. -/
theorem constantTwistEtaleTheta_existsUnique
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y) (b : Qˣ) :
    ∃! theta : (lisseAlgebraicAutomorphismPullback h l Q).obj
          (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ Y)
        (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom)),
        (etaleWeilFrobenius l Q h t path
          (IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
          (b : Q) • LinearMap.id := by
  sorry

/-- The constant etale-adic Weil presentation of the same constant coefficient line.
Its carrier is the actual constant system, and its structure map has a unique
constant-section normalization. Source: current blueprint constant-module formula
(blueprint: def-wf-constant-weil-twist). -/
def constantTwistEtaleLine
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y) (b : Qˣ) : EtaleLisseWeilSheaf l Q h :=
  IsoAlgebra.mk (lisseAlgebraicUnit l Y Q)
    (constantTwistEtaleTheta_existsUnique l Y Q h b).exists.choose

end WeilConjectures
