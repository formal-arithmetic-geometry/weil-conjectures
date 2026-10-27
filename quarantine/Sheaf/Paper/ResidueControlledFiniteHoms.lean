/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.RingedProEtaleTorAmplitudeOfUniverses
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.CharP.CharAndCard

/-!
# Residue-controlled uniform bounds for finite internal Homs

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-integral-internal-hom.proof.md, sentences 2–3 and the final sentence
(blueprint: lem-coef-residue-controlled-finite-homs).

The index `n : ℕ` denotes exponent `n+1`; index zero is the residue reduction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

private theorem support_of_torAmplitude (X : Scheme.{u}) (A : Type u) [CommRing A]
    (K : proEtaleDerivedCategory X A) (a b : ℤ)
    (h : HasProEtaleTorAmplitude X A K a b) :
    proEtaleCohomologicalSupport K ⊆ Set.Icc a b := by
  classical
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := SheafOfModules.monoidalCategory R
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  have := SheafOfModules.tensorPreadditive R
  have : (DerivedCategory.Q (C := C)).EssSurj :=
    Localization.essSurj _ (HomologicalComplex.quasiIso C (.up ℤ))
  let L := (DerivedCategory.Q (C := C)).objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K :=
    (DerivedCategory.Q (C := C)).objObjPreimageIso K
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral (R := R) L
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
  let et : derivedTensor X A L
      ((HomologicalComplex.single C (.up ℤ) 0).obj (MonoidalCategory.tensorUnit C))
      P f hf hP ≅ K :=
    DerivedCategory.Q.mapIso (HomologicalComplex.rightUnitor P) ≪≫
      asIso (DerivedCategory.Q.map f) ≪≫ e
  intro i hi
  by_contra hout
  have hoff : i < a ∨ b < i := by
    change ¬ (a ≤ i ∧ i ≤ b) at hout
    omega
  have hz := h.2 L P ⟨e⟩ f hf hP (MonoidalCategory.tensorUnit C) i hoff
  exact hi (hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso et.symm))

/-- The finite internal Hom of the two canonical reductions, at exponent `n+1`.
It uses modules over the constant finite coefficient sheaf on the original small site.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentence 3
(blueprint: lem-coef-residue-controlled-finite-homs). -/
noncomputable def integralFiniteInternalHom
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
    proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) :=
  (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))).obj
      (op ((scalarReductionDerivedExtension.{u, u} l E X n).obj K),
        (scalarReductionDerivedExtension.{u, u} l E X n).obj L)

/-- Residue cohomological bounds give one uniform interval for bounded constructibility,
Tor amplitude and cohomological support of all finite internal Homs.
Source: main-20261015, cor-coef-integral-internal-hom.proof.md, sentences 2–3
and the final sentence (blueprint: lem-coef-residue-controlled-finite-homs).

Proof:
1. Integral constructibility gives bounded constructibility of every reduction.
Since l differs from the characteristic of the base field, l is invertible on X.
Apply lem-coef-integral-residue-tor to K and L with the supplied residue intervals,
obtaining Tor intervals [a,b] and [c,e] at every positive level. Together with
constructibility these are the conditions of def-weil-finite-tor-amplitude.
2. Apply the pro-etale clause of cor-weil-finite-constructible-hom at exponent n+1.
It gives bounded constructibility and Tor interval [c-b-2d,e-a+2d]. The endpoints
involve only the residue bounds and d, so they are independent of n.
3. Test Tor amplitude against the coefficient sheaf in degree zero. On a K-flat
representative P, the maps P tensor B_n → P, x tensor r ↦ r x, and
P → P tensor B_n, x ↦ x tensor 1, are inverse chain maps by tensor balancing
and linearity of the differential. Hence the tensor test is the same derived
object, giving the stated cohomological support inclusion. -/
theorem residue_controlled_finite_homs
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (K L : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K) (_hL : sfIntegralConstructible l E X L)
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (_hK₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj K) ⊆ Set.Icc a b)
    (_hL₁ : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E X 0).obj L) ⊆ Set.Icc c e) :
    ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X (integralFiniteInternalHom l E X K L n) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        (integralFiniteInternalHom l E X K L n)
        (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) ∧
      proEtaleCohomologicalSupport (integralFiniteInternalHom l E X K L n) ⊆
        Set.Icc (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  classical
  have hunit : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  have hKt := (integral_residue_tor D l _hl E X).1 K _hK a b _hab
    (fun i hi ↦ _hK₁ hi)
  have hLt := (integral_residue_tor D l _hl E X).1 L _hL c e _hce
    (fun i hi ↦ _hL₁ hi)
  obtain ⟨_, r, s, hrs, hKs⟩ := _hK
  obtain ⟨_, t, v, htv, hLs⟩ := _hL
  intro n
  have hKn : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) :=
    ⟨(hKs n).1, a, b, hKt n⟩
  have hLn : finiteTorConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X
      ((scalarReductionDerivedExtension.{u, u} l E X n).obj L) :=
    ⟨(hLs n).1, c, e, hLt n⟩
  have hhom := finite_constructible_derivedHom_proEtale D l _hl E (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) X d _hd a b c e _hab _hce
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj L) hKn hLn (hKt n) (hLt n)
  exact ⟨hhom.1.1, hhom.2,
    support_of_torAmplitude X _ _ _ _ hhom.2⟩

end WeilConjectures
