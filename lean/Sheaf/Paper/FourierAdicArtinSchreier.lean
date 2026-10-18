/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FourierSetting
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import WeilConjectures.FourierTransform.ArtinSchreier
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.FourierTransform.Defs

/-!
# Integral adic realization of the Artin--Schreier sheaf

Source: blueprint main-20261015, sec-fourier-transform/sk-def-as,
with the adic conventions of def-fourier-set (blueprint: def-fd-adic-fourier-realization).
The existing idempotent-image construction is retained. Only its coefficient realization
is extended: the finite-monodromy integral sheaf is tensored with completed coefficients.

## Main definitions

- `fourierCompletedRealization`: canonical completed scalar extension after site pullback.
- `fourierIntegralCharacter`: the uniquely determined integral character at the fixed stage.
- `fourierAdicArtinSchreier`: the completed prime-field Artin--Schreier sheaf in degree zero.
- `fourierAdicKernel`, `fourierAdicIntegrand`: its common-stage kernel and Fourier integrand.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Pull the existing etale sheaf to the pro-etale site, regard it as a module over
constant integral scalars, and tensor with the actual completed coefficient ring.
Source: blueprint main-20261015, sk-def-as, together with def-fourier-set's adic convention
(blueprint: def-fd-adic-fourier-realization). -/
def fourierCompletedRealization
    (H : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))) :
    scalarReductionSource l E X :=
  SheafOfModules.changeOfRingsOfUniverses
    (R₁ := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
    (R₂ := completedIntegralCommRingSheafUnrestricted l E X)
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
        (integralConstantToCompletionOfUniverses l E X))
    ((SheafOfModules.restrictScalars
      (constantModuleHomRingIso (ProEt.topology X)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).inv).obj
      ((PresheafOfModules.sheafification
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))).obj
        ((ProEtale.finiteCoefficientModulePresheaf X.ProEt
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj
          ((ProEtale.comparisonUpperStar _ X).obj H).obj)))


/-- The coefficient field fixed by the Fourier setting, as an actual common-stage index.
Source: def-fourier-set, coefficient convention (blueprint: def-fd-adic-fourier-realization). -/
def fourierCoefficientStage (F : FourierSetting.{u}) :
    Padic.FiniteCoefficientFields F.coefficients.l F.coefficients.Qbar :=
  ⟨F.extension, F.finiteExtension⟩

/-- The already recorded small model of that coefficient field.
Source: common-stage coefficient convention (blueprint: def-fd-adic-fourier-realization). -/
abbrev fourierCoefficient (F : FourierSetting.{u}) : Type u :=
  AlgebraicallyClosedCoefficients.Coefficient F.coefficients.l F.coefficients.Qbar
    (fourierCoefficientStage F)

/-- The inclusion into the fixed algebraic closure, retaining the small-model transport.
Source: def-fourier-set, coefficient convention (blueprint: def-fd-adic-fourier-realization). -/
def fourierCoefficientEmbedding (F : FourierSetting.{u}) :
    fourierCoefficient F →+* F.coefficients.Qbar :=
  F.extension.subtype.comp
    (Shrink.algEquiv (Padic F.coefficients.l) F.extension).toRingHom

/-- The finite-field datum supplies its prime instance, without an additional hypothesis.
Source: def-fourier-set (blueprint: def-fd-adic-fourier-realization). -/
instance fourierCharacteristicPrime (F : FourierSetting.{u}) : Fact F.field.p.Prime :=
  ⟨F.field.prime⟩

/-- Character values have a unique integral lift at the fixed coefficient stage.
Source: main-20261015 sk-def-as; def-fourier-set, mu_p contained in E
(blueprint: def-fd-adic-fourier-realization).
Proof: every value has pth power one since the additive group has exponent p.
The roots-of-unity assumption puts it in E. Its absolute value is one, so it lies
in O_E; transport through Shrink and ULift. Injectivity of the inclusion proves
the character identities and uniqueness, including for the trivial character. -/
theorem fourierIntegralCharacter_existsUnique (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :
    ∃! χ : AddChar (ZMod F.field.p)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers F.coefficients.l
          (fourierCoefficient F))),
      ∀ a, fourierCoefficientEmbedding F (χ a).down.val = Ψ a := by
  sorry

/-- The uniquely specified lift; no character is chosen from mere existence.
Source: main-20261015 sk-def-as (blueprint: def-fd-adic-fourier-realization). -/
def fourierIntegralCharacter (F : FourierSetting.{u})
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) :=
  (fourierIntegralCharacter_existsUnique F Ψ).exists.choose

/-- The prime p is invertible in the integral coefficient ring since p differs from l.
Source: sk-def-as, idempotent coefficient 1/p (blueprint: def-fd-adic-fourier-realization).
Proof: the integers of a finite l-adic extension have residue characteristic l.
The image of p in its residue field is nonzero, so p is outside the maximal ideal
and is a unit. The ring isomorphism ULift preserves units. -/
theorem fourierIntegerPrime_isUnit (F : FourierSetting.{u}) :
    IsUnit (F.field.p : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))) := by
  sorry

/-- The canonical inverse of p, supplied by its unit property.
Source: sk-def-as (blueprint: def-fd-adic-fourier-realization). -/
@[instance_reducible]
def fourierIntegerPrimeInvertible (F : FourierSetting.{u}) :
    Invertible (F.field.p : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers F.coefficients.l (fourierCoefficient F))) :=
  (fourierIntegerPrime_isUnit F).invertible

/-- The integral adic Artin--Schreier sheaf in degree zero, for the prime-field character.
Its defining data are the existing idempotent-image sheaf and completed scalar extension.
Source: main-20261015 sk-def-as (blueprint: def-fd-adic-fourier-realization). -/
def fourierAdicArtinSchreier (F : FourierSetting.{u}) (X : Scheme.{u})
    [CharP Γ(X, ⊤) F.field.p] (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar)
    (b : Γ(X, ⊤)) : DerivedCategory (scalarReductionSource F.coefficients.l
      (fourierCoefficient F) X) :=
  letI := fourierIntegerPrimeInvertible F
  (DerivedCategory.singleFunctor _ 0).obj
    (fourierCompletedRealization F.coefficients.l (fourierCoefficient F) X
      (Etale.artinSchreierSheafZMod X (fourierIntegralCharacter F Ψ) b))

/-- Membership of this actual construction in the intrinsic integral category.
Source: main-20261015 sk-def-as and def-fourier-set's adic convention
(blueprint: def-fd-adic-fourier-realization).
Proof: the finite etale Artin--Schreier torsor trivializes the character summand.
There it is the completed free rank-one module. Each derived reduction is the
same finite-level character summand in degree zero, so it is constructible with
uniform support [0,0]. The completed free module is derived complete, and these
properties descend along the finite etale cover. -/
theorem fourierAdicArtinSchreier_mem (F : FourierSetting.{u}) (X : Scheme.{u})
    [IsNoetherian X] [CharP Γ(X, ⊤) F.field.p]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (b : Γ(X, ⊤)) :
    sfIntegralConstructible F.coefficients.l (fourierCoefficient F) X
      (fourierAdicArtinSchreier F X Ψ b) := by
  sorry

/-- The actual Fourier kernel in the adic common-stage category. V and V' may be
any S-schemes with a characteristic-p pairing; evaluation is the application.
Source: main-20261015 sk-def-kernel (blueprint: def-fd-adic-fourier-realization). -/
def fourierAdicKernel (F : FourierSetting.{u}) {S V V' : Scheme.{u}}
    (π : V ⟶ S) (π' : V' ⟶ S) [IsNoetherian (pullback π π')]
    [CharP Γ(pullback π π', ⊤) F.field.p]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (b : Γ(pullback π π', ⊤)) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (pullback π π') :=
  letI := fourierIntegerPrimeInvertible F
  ⟨fourierCoefficientStage F,
    (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
      (pullback π π')).obj
        ⟨(DerivedCategory.singleFunctor _ 0).obj
          (fourierCompletedRealization F.coefficients.l (fourierCoefficient F)
            (pullback π π')
            (Etale.fourierKernel _ π π' (fourierIntegralCharacter F Ψ) b)),
          fourierAdicArtinSchreier_mem F (pullback π π') Ψ b⟩⟩

/-- The Fourier integrand is the recorded adic pullback tensored with the kernel.
Source: sk-def-kernel, Fourier integrand paragraph (blueprint: def-fd-adic-fourier-realization). -/
def fourierAdicIntegrand (F : FourierSetting.{u}) {S V V' : Scheme.{u}}
    (π : V ⟶ S) (π' : V' ⟶ S) [IsNoetherian (pullback π π')]
    [CharP Γ(pullback π π', ⊤) F.field.p]
    [∀ x : V, Invertible (F.coefficients.l : V.residueField x)]
    [∀ x : ↥(pullback π π'),
      Invertible (F.coefficients.l : (pullback π π').residueField x)]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (b : Γ(pullback π π', ⊤))
    (K : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar V) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (pullback π π') :=
  (commonStageDerivedTensor F.coefficients.l F.coefficients.Qbar (pullback π π')).obj
    (((commonStageDerivedPullback F.coefficients.l F.coefficients.Qbar
      (pullback.fst π π')).obj K), fourierAdicKernel F π π' Ψ b)

end WeilConjectures
