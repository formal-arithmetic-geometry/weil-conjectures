/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeComplexUpperWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Data.Fin.Rev
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.RepresentationTheory.CompositionSeries
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.Monoidal.EndTensorUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
public import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree

/-! # Elementary operations on condensed Weil weights

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/_section.md
and sk-r-real-linear.proof.md; Wei Yang, Zulip #1441, items 34--35.
(blueprint: sk-r-real-linear).

Duals here are coefficient internal duals. The mixed-dual theorem makes no
assumption on a chosen filtration; the annihilator theorem requires lisse gradeds.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.RealLinearWeights
open NativeL2

section Geometric

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [hsep : IsSeparated X₀.hom]

include hsep

/-- Subobjects and quotients retain the specified pure weight.
Proof: exact Frobenius fibres turn the arrow into an invariant subspace or quotient.
The block triangular characteristic polynomial factors, so all surviving eigenvalues
have the original modulus; a zero fibre has no eigenvalues.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_mono (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : N ⟶ M) [Mono f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Pure D l X₀ M iota w) : Pure D l X₀ N iota w := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro x i hi α hα
  let V := nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)
  have hinj : Function.Injective (V.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (V.map f))
  apply h x i hi α
  apply eigenvalue_mem_of_injective (closedOperator D l X₀ N x i hi).hom
    (closedOperator D l X₀ M x i hi).hom (V.map f).hom hinj _ hα
  intro v
  exact (congrArg (fun g ↦ g.hom v)
    (closedOperator_naturality D l X₀ x i hi f)).symm

/-- Subobjects and quotients retain every mixed upper bound.
Proof: intersect a mixed filtration with the subobject or take its images in the
quotient. Exact fibres identify the gradeds as subquotients of the old pure gradeds.
The previous pure clauses preserve their weights and the inequalities to the bound.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_mono (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : N ⟶ M) [Mono f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Mixed D l X₀ M iota w) : Mixed D l X₀ N iota w := by
  sorry

/-- Subobjects and quotients retain the specified pure weight.
Proof: exact Frobenius fibres turn the arrow into an invariant subspace or quotient.
The block triangular characteristic polynomial factors, so all surviving eigenvalues
have the original modulus; a zero fibre has no eigenvalues.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_epi (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Epi f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Pure D l X₀ M iota w) : Pure D l X₀ N iota w := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro x i hi α hα
  let V := nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)
  let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D M.carrier (localClosedPoint D X₀ x i hi)) :=
    NativeCondensedModule.constructible_fibre_finiteDimensional D l M.carrier _hM
      (localClosedPoint D X₀ x i hi)
  let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D N.carrier (localClosedPoint D X₀ x i hi)) :=
    NativeCondensedModule.constructible_fibre_finiteDimensional D l N.carrier _hN
      (localClosedPoint D X₀ x i hi)
  have hsurj : Function.Surjective (V.map f).hom :=
    (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (V.map f))
  apply h x i hi α
  apply eigenvalue_mem_of_surjective (closedOperator D l X₀ M x i hi).hom
    (closedOperator D l X₀ N x i hi).hom (V.map f).hom hsurj _ hα
  intro v
  exact (congrArg (fun g ↦ g.hom v)
    (closedOperator_naturality D l X₀ x i hi f)).symm

/-- Subobjects and quotients retain every mixed upper bound.
Proof: intersect a mixed filtration with the subobject or take its images in the
quotient. Exact fibres identify the gradeds as subquotients of the old pure gradeds.
The previous pure clauses preserve their weights and the inequalities to the bound.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_epi (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Epi f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Mixed D l X₀ M iota w) : Mixed D l X₀ N iota w := by
  sorry

/-- Extensions retain any common mixed upper bound.
Proof: append the inverse images of a quotient filtration to the filtration of the
subobject. Exactness identifies all successive quotients with the old pure quotients;
constructibility is closed under extensions. Every old weight keeps its common bound.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_extension (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (S : ShortComplex (WeilModule D l X₀)) (hS : S.ShortExact)
    (_h₁ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₁.carrier)
    (_h₂ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₂.carrier)
    (_h₃ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₃.carrier) (w : ℝ)
    (h₁ : Mixed D l X₀ S.X₁ iota w) (h₃ : Mixed D l X₀ S.X₃ iota w) :
    Mixed D l X₀ S.X₂ iota w := by
  sorry

/-- An extension of mixed sheaves is mixed, without a common bound supplied.
Proof: take the maximum of the finitely many weights of both filtrations and apply
the preceding extension construction. The maximum also handles distinct old bounds.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_extension_unbounded (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (S : ShortComplex (WeilModule D l X₀)) (hS : S.ShortExact)
    (_h₁ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₁.carrier)
    (_h₂ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₂.carrier)
    (_h₃ : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left S.X₃.carrier)
    (h₁ : ∃ a : ℝ, Mixed D l X₀ S.X₁ iota a)
    (h₃ : ∃ b : ℝ, Mixed D l X₀ S.X₃ iota b) :
    ∃ w : ℝ, Mixed D l X₀ S.X₂ iota w := by
  have mono : ∀ {M : WeilModule D l X₀} {a b : ℝ},
      Mixed D l X₀ M iota a → a ≤ b → Mixed D l X₀ M iota b := by
    rintro M a b ⟨n, G, φ, hC, h0, hn, hm, hwt⟩ hab
    refine ⟨n, G, φ, hC, h0, hn, hm, fun i ↦ ?_⟩
    obtain ⟨v, hv, hp⟩ := hwt i
    exact ⟨v, hv.trans hab, hp⟩
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  exact ⟨max a b, mixed_extension D l X₀ _hl iota S hS _h₁ _h₂ _h₃
    (max a b) (mono ha (le_max_left _ _)) (mono hb (le_max_right _ _))⟩

/-- Tensor products add pure weights for arbitrary constructible factors.
Proof: restrict to a closed point, where both modules are finite locally free.
The monoidal pullback comparison identifies Frobenius with F_x tensor G_x.
Its eigenvalues are products alpha*beta and their complex moduli multiply.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_tensor (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M N : WeilModule D l X₀)
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (a b : ℝ)
    (hM : Pure D l X₀ M iota a) (hN : Pure D l X₀ N iota b) :
    Pure D l X₀ (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius X₀) M N)
      iota (a + b) := by
  sorry

/-- Tensor products add mixed upper bounds.
Proof: tensor is exact on each stratum of a common lisse stratification, hence
exact globally by open-closed induction. Refine the tensor filtration by its two
indices; its gradeds are tensor products of the old pure gradeds. Their weights
are sums and satisfy a_i+b_j ≤ a+b.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_tensor (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M N : WeilModule D l X₀)
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (a b : ℝ)
    (hM : Mixed D l X₀ M iota a) (hN : Mixed D l X₀ N iota b) :
    Mixed D l X₀ (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius X₀) M N)
      iota (a + b) := by
  sorry

/-- Coefficient duals of pure lisse sheaves negate the pure weight.
Proof: finite-free evaluation identifies the dual fibre with the linear dual,
and its local Frobenius with the transpose inverse. Its eigenvalues are alpha inverse,
so their moduli have exponent -a/2.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_dual (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : WeilModule D l X₀) (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) (a : ℝ)
    (hM : Pure D l X₀ M iota a) :
    Pure D l X₀ (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) M) iota (-a) := by
  sorry

/-- The coefficient dual of any mixed lisse sheaf is mixed. No lissity of
the gradeds of a chosen mixed filtration is assumed.
Proof (Wei Yang #1441 item 34): induct on reduced closed subsets, with empty case zero.
Choose the Weil-stable dense open where all constructible gradeds are lisse. There
finite-free duality gives the reversed annihilator filtration with negative weights.
On the closed complement, restriction commutes with the dual because M is lisse;
restriction preserves mixedness, so induction applies. Glue along the short exact
open-closed sequence of the dual. Extension by zero and closed pushforward preserve
purity from their supported and zero fibres, and extensions glue mixed filtrations.
No later quasi-finite weight theorem or Verdier duality is used.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem mixed_dual (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : WeilModule D l X₀) (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier)
    (hM : ∃ w : ℝ, Mixed D l X₀ M iota w) :
    ∃ v : ℝ, Mixed D l X₀
      (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) M) iota v := by
  sorry

/-- A specified lisse mixed filtration dualizes to its reversed annihilator
filtration, with reversed dual gradeds and negated weights.
Proof (Wei Yang #1441 item 34): each short exact lisse-graded sequence splits locally.
Finite-free coefficient duality is therefore exact. Restriction of functionals to
a filtration term has kernel the annihilator, which is the dual of the quotient.
Reverse the indices. Exact duality identifies each new cokernel with the dual of
the corresponding old cokernel; the pure-dual computation negates its weight.
The kernels give zero and whole-dual endpoints, including a length-zero filtration.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem lisse_annihilator_filtration (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : WeilModule D l X₀) (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) M.carrier) (n : ℕ)
    (S : Fin (n + 1) → Subobject M) (hS : Monotone S)
    (h₀ : S 0 = ⊥) (hₙ : S (Fin.last n) = ⊤)
    (a : ∀ i : Fin n, (S i.castSucc : WeilModule D l X₀) ⟶ S i.succ)
    (ha : ∀ i, a i ≫ (S i.succ).arrow = (S i.castSucc).arrow)
    (haMono : ∀ i, Mono (a i)) (v : Fin n → ℝ)
    (_hTerms : ∀ i, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      (S i : WeilModule D l X₀).carrier)
    (_hGr : ∀ i, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (cokernel (a i)).carrier)
    (hPure : ∀ i, Pure D l X₀ (cokernel (a i)) iota (v i)) :
    ∃ (H : Fin (n + 1) → Subobject
        (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) M))
      (b : ∀ i : Fin n,
        (H i.castSucc : WeilModule D l X₀) ⟶ H i.succ),
      Monotone H ∧ H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
      (∀ i, b i ≫ (H i.succ).arrow = (H i.castSucc).arrow) ∧
      (∀ i, Mono (b i)) ∧
      (∀ i : Fin (n + 1), ∃ r :
          (CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀) M) ⟶
          CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀)
            (S i.rev : WeilModule D l X₀),
        r.hom.f = (MonoidalClosed.pre (S i.rev).arrow.hom.f).app (𝟙_ _) ∧
        H i = kernelSubobject r) ∧
      ∀ i : Fin n,
        Nonempty ((cokernel (b i)) ≅
          CondensedFibreLinearCurrent.dualWeil l (D.geometricFrobenius X₀)
            (cokernel (a i.rev))) ∧
        Pure D l X₀ (cokernel (b i)) iota (-(v i.rev)) := by
  sorry

/-- The actual base change of the arithmetic morphism to the fixed algebraic closure.
Source: latest blueprint, inverse-image sentence (blueprint: sk-r-real-linear). -/
abbrev geometricMap
    (Y₀ : Over (Spec (.of D.k₀))) (f₀ : Y₀ ⟶ X₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Inverse image preserves purity, mixedness and every mixed upper bound.
The Frobenius square is a conclusion; no compatibility is assumed.
Proof: both composites in the square have the same two pullback projections.
At a closed source point the return is the e-th power of the image return and
q_y=q_x^e. Thus taking e-th powers preserves the same modulus exponent. Exact
module pullback carries finite mixed filtrations and cokernels to their pullbacks.
The unbounded assertion follows by retaining a finite upper bound.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pullback_weights (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : Y₀ ⟶ X₀) :
    ∃ sq : CommSq (D.geometricFrobenius Y₀).hom (geometricMap D X₀ Y₀ f₀)
        (geometricMap D X₀ Y₀ f₀) (D.geometricFrobenius X₀).hom,
      let F := IsoAlgebra.mapOfNatIso
        (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l) sq).symm
      ∀ (M : WeilModule D l X₀),
        IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier →
        (∀ w : ℝ, Pure D l X₀ M iota w → Pure D l Y₀ (F.obj M) iota w) ∧
        (∀ w : ℝ, Mixed D l X₀ M iota w → Mixed D l Y₀ (F.obj M) iota w) ∧
        ((∃ w : ℝ, Mixed D l X₀ M iota w) →
          ∃ w : ℝ, Mixed D l Y₀ (F.obj M) iota w) := by
  sorry

/-- Shift the carrier and transport Frobenius by its canonical shift comparison.
Source: latest blueprint, K[r] sentence (blueprint: sk-r-real-linear). -/
def shiftComplex
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀))) (r : ℤ) :=
  IsoAlgebra.mk (K.carrier⟦r⟧)
    (((CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀)).commShiftIso r).app K.carrier ≪≫
      (shiftFunctor _ r).mapIso K.str)

/-- A cohomological shift by r raises an upper complex weight by r.
Proof: the canonical comparison identifies H^i(K[r]) with H^(i+r)(K), including
its induced Weil datum. The old bound w+(i+r) equals (w+r)+i for every integer i.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem shift_weights (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀))) (w : ℝ) (r : ℤ)
    (_hKbc : constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left K.carrier)
    (hK : complexMixedOfWeightsAtMost D l X₀ K iota w) :
    complexMixedOfWeightsAtMost D l X₀
      (shiftComplex D l X₀ K r) iota (w + (r : ℝ)) := by
  intro n
  have h := mixed_of_iso D l X₀ (shiftWeilCohomologyIso D l X₀ K r n).symm
    iota (w + ((r + n : ℤ) : ℝ)) (hK (r + n))
  simpa only [Int.cast_add, add_assoc] using h

/-- Constant Weil twisting shifts every pure weight.
Proof: the degree-d local eigenvalue of the constant line is b^d. Tensor
eigenvalues are multiplied by it. Its weight is 2*log(norm(iota b))/log(q),
since both logarithms at degree d are multiplied by d. Tensoring is exact
with inverse twist b inverse, so the same computation applies to every graded piece.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem constant_twist_pure (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) (w : ℝ)
    (hM : Pure D l X₀ M.obj iota w) :
    Pure D l X₀ (CondensedRing.ConstantWeil.twist l D X₀ hl b M).obj iota
      (w + AlgebraicGeometry.WeilGroup.frobeniusWeight iota D.q (b : PadicAlgCl l)) := by
  apply Pure.constantTwist D l hl X₀ M iota w _ hM b
  simp only [AlgebraicGeometry.WeilGroup.frobeniusWeight, Real.logb, D.card_base]
  ring

/-- Constant Weil twisting shifts every mixed upper bound.
Proof: the degree-d local eigenvalue of the constant line is b^d. Tensor
eigenvalues are multiplied by it. Its weight is 2*log(norm(iota b))/log(q),
since both logarithms at degree d are multiplied by d. Tensoring is exact
with inverse twist b inverse, so the same computation applies to every graded piece.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem constant_twist_mixed (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) (w : ℝ)
    (hM : Mixed D l X₀ M.obj iota w) :
    Mixed D l X₀ (CondensedRing.ConstantWeil.twist l D X₀ hl b M).obj iota
      (w + AlgebraicGeometry.WeilGroup.frobeniusWeight iota D.q (b : PadicAlgCl l)) := by
  sorry

set_option linter.unusedSectionVars false in
/-- The coefficient prime is invertible on the geometric fibre.
Source: latest blueprint, standing ell distinct from p and Tate sheaf paragraph
(blueprint: sk-r-real-linear).
Proof: every residue field of the geometric fibre receives the algebraic closure
of the finite base field, of characteristic p. Since l and p are distinct primes,
l is nonzero in every such field and therefore is invertible. -/
theorem coefficientPrimeIsUnit (_hl : l ≠ D.p) :
    ∀ x : (D.geometricFiber X₀).left,
      IsUnit (l : (D.geometricFiber X₀).left.residueField x) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (f := D.a)
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (l : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
  let g := (D.geometricFiber X₀).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  intro x
  simpa only [map_natCast] using hunit.map
    ((Scheme.ΓSpecIso (CommRingCat.of D.k₀)).inv ≫ g.appTop ≫
      (D.geometricFiber X₀).left.Γevaluation x).hom

/-- The roots-of-unity Tate line is the constant line of scalar q^(-r).
Proof: arithmetic Frobenius raises roots to q, so geometric Frobenius acts by its
inverse. This passes through the integral inverse limit, scalar extension, positive
tensor powers and negative coefficient duals. The resulting frame identifies the
canonical Weil datum with the constant-line datum, including r=0.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem tate_is_constant (hl : l ≠ D.p)
    (r : ℤ) :
    ∃ b : (PadicAlgCl l)ˣ,
      (b : PadicAlgCl l) = (D.q : PadicAlgCl l) ^ (-r) ∧
      Nonempty (tateModule D l X₀ hl r ≅
        CondensedRing.ConstantWeil.lineModule l D X₀ hl b) := by
  sorry

/-- Tate twisting by r subtracts 2r from a pure weight.
Proof: the preceding cyclotomic identification gives local scalar q_x^(-r).
Multiplying each eigenvalue by it subtracts 2r from its logarithmic weight.
Exact tensor with this lisse line applies the same rule to every mixed graded piece.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem tate_twist_pure (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : WeilModule D l X₀) (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (w : ℝ) (r : ℤ) (hM : Pure D l X₀ M iota w) :
    Pure D l X₀ (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius X₀)
      M (tateModule D l X₀ hl r)) iota (w - 2 * (r : ℝ)) := by
  sorry

/-- Tate twisting by r subtracts 2r from each mixed upper bound.
Proof: the preceding cyclotomic identification gives local scalar q_x^(-r).
Multiplying each eigenvalue by it subtracts 2r from its logarithmic weight.
Exact tensor with this lisse line applies the same rule to every mixed graded piece.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem tate_twist_mixed (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : WeilModule D l X₀) (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (w : ℝ) (r : ℤ) (hM : Mixed D l X₀ M iota w) :
    Mixed D l X₀ (CondensedFibreLinearCurrent.tensorWeil l (D.geometricFrobenius X₀)
      M (tateModule D l X₀ hl r)) iota (w - 2 * (r : ℝ)) := by
  sorry

end Geometric

section Complement

variable {E : Type u} {V : Type v} {W : Type z} [Field E] [Group W] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

/-- Semisimplification preserves the characteristic factor and the full eigenvalue multiset.
In particular it preserves each punctual pure weight and punctual upper bound when
applied to the local Frobenius element of a Weil representation.
Source: latest blueprint, sk-r-real-linear, Complement
(blueprint: sk-r-real-linear).
Proof: in a basis adapted to the composition series, every action matrix is block
upper triangular. Its characteristic polynomial is the product of those on the
composition factors. The direct sum defining semisimplification has that same
product. Reverse the equality for the local factor and take roots for the spectrum;
applying any fixed weight function gives identical purity and upper bounds.
This includes the zero representation and its empty composition series. -/
theorem semisimplification_spectrum (rho : Representation E W V)
    (c : rho.CompositionSeries) (g : W) :
    (c.semisimplification g).charpolyRev = (rho g).charpolyRev ∧
    (c.semisimplification g).charpoly.roots = (rho g).charpoly.roots ∧
    ∀ (iota : E →+* ℂ) (q : ℕ) (w : ℝ),
      ((∀ a ∈ (c.semisimplification g).charpoly.roots,
          AlgebraicGeometry.WeilGroup.frobeniusWeight iota q a = w) ↔
        ∀ a ∈ (rho g).charpoly.roots,
          AlgebraicGeometry.WeilGroup.frobeniusWeight iota q a = w) ∧
      ((∀ a ∈ (c.semisimplification g).charpoly.roots,
          AlgebraicGeometry.WeilGroup.frobeniusWeight iota q a ≤ w) ↔
        ∀ a ∈ (rho g).charpoly.roots,
          AlgebraicGeometry.WeilGroup.frobeniusWeight iota q a ≤ w) := by
  classical
  let F : ℕ → Subrepresentation rho := fun j ↦
    c.series ⟨min j c.length, Nat.lt_succ_of_le (Nat.min_le_right j c.length)⟩
  have h0 : (F 0).toSubmodule = ⊥ := by
    simpa [F, RelSeries.head] using congrArg Subrepresentation.toSubmodule c.head_eq
  have hn : (F c.length).toSubmodule = ⊤ := by
    simpa [F, RelSeries.last, Fin.last] using
      congrArg Subrepresentation.toSubmodule c.last_eq
  have hle : ∀ i < c.length, (F i).toSubmodule ≤ (F (i + 1)).toSubmodule := by
    intro i hi
    simpa [F, Nat.min_eq_left (Nat.le_of_lt hi),
      Nat.min_eq_left (Nat.succ_le_of_lt hi)] using
      (show (c.series (⟨i, hi⟩ : Fin c.length).castSucc).toSubmodule ≤
        (c.series (⟨i, hi⟩ : Fin c.length).succ).toSubmodule from (c.covBy ⟨i, hi⟩).le)
  have hc := LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le (rho g)
    (fun i ↦ (F i).toSubmodule) c.length h0 hn hle
    (fun i ↦ (F i).apply_mem_toSubmodule g)
  rw [← Fin.prod_univ_eq_prod_range] at hc
  have hcp : (c.semisimplification g).charpoly = (rho g).charpoly := by
    change (Representation.directSum (fun i ↦ c.factor i) g).charpoly = _
    rw [Representation.charpoly_directSum, hc]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hi0 : F i = c.series i.castSucc :=
      congrArg c.series (Fin.ext (Nat.min_eq_left (Nat.le_of_lt i.isLt)))
    have hi1 : F (i + 1) = c.series i.succ :=
      congrArg c.series (Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)))
    change ((c.series i.succ).subquotient (c.series i.castSucc) g).charpoly =
      ((F (i + 1)).subquotient (F i) g).charpoly
    rw [hi0, hi1]
  refine ⟨?_, congrArg Polynomial.roots hcp, ?_⟩
  · simpa only [LinearMap.charpolyRev_def] using congrArg Polynomial.reverse hcp
  · intro iota q w
    rw [hcp]
    exact ⟨Iff.rfl, Iff.rfl⟩

end Complement

end WeilConjectures.RealLinearWeights
