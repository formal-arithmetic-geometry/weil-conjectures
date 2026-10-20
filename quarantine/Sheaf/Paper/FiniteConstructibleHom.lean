/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.FiniteStageVerdierBiduality
import Sheaf.Paper.WeilVerdierPreservationStrata
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-!
# Internal Hom of finite-stage constructible complexes

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
cor-weil-finite-constructible-hom, order 2138
(blueprint: cor-weil-finite-constructible-hom).

## Main statements

* `WeilConjectures.finite_constructible_derivedHom_etale`
* `WeilConjectures.finite_constructible_derivedHom_proEtale`

The two statements give the etale and pro-etale assertions separately. On the etale
site the scalar ring is its canonical universe lift; on the pro-etale site the recorded
constant-ring module category already uses that lift. No perfectness is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Etale internal Hom is bounded constructible, with the asserted Tor interval.
The input intervals already imply finite Tor amplitude. Finiteness of the lifted
coefficient ring is supplied by the recorded positive-level finiteness theorem.
Source: blueprint order 2138 (blueprint: cor-weil-finite-constructible-hom).

Proof:
1. General biduality (thm-fix-general-biduality) identifies L with D_X D_X L.
Apply internal Hom(K,-), then the natural currying isomorphism of
lem-weil-pbc-ringed-internal-hom-exact-restriction, to identify the result with
D_X(K tensor^L D_X L), without a perfectness hypothesis.
2. By lem-weil-verdier-preservation-strata, D_X L is constructible with interval
[-e-2d,-c]. By lem-sf-tensor-ctf the tensor with K is constructible with interval
[a-e-2d,b-c]. Dualizing again gives bounded constructibility and the interval
[c-b-2d,e-a+2d]. Transport these properties across the displayed isomorphism. -/
theorem finite_constructible_derivedHom_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (K L : Etale.DerivedCategoryModule (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X K)
    (_hL : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X L)
    (_hKt : Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X a b K)
    (_hLt : Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X c e L) :
    @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) _
      (@Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E n hn)
        Equiv.ulift.symm) X
      (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj L) ∧
    Etale.DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj L) := by
  sorry

/-- Pro-etale internal Hom preserves finite-Tor bounded constructibility and has the
same interval bound. The internal Hom is the recorded Hom-complex localization on the
original small site, whose object and morphism universes remain distinct.
Source: blueprint order 2138 (blueprint: cor-weil-finite-constructible-hom).

Proof:
1. By lem-sf-proetale-constructible-origin choose bounded constructible etale
origins K', L'. By clause (ii) of lem-sf-comparison-tor-amplitude they retain the
original intervals [a,b] and [c,e].
2. Apply the etale argument: biduality thm-fix-general-biduality and currying
lem-weil-pbc-ringed-internal-hom-exact-restriction give Hom(K',L') as
D_X(K' tensor^L D_X L'). The two duality bounds of
lem-weil-verdier-preservation-strata and tensor bound lem-sf-tensor-ctf give
bounded constructibility and interval [c-b-2d,e-a+2d].
3. By lem-weil-finite-duality-site-comparison, inverse image of this internal Hom
is the internal Hom of the inverse images. That comparison applies since K' is
finite-Tor constructible and L' is bounded constructible. Clause (i) of
lem-sf-comparison-tor-amplitude preserves bounded constructibility and the exact
interval. Transport through the chosen identifications with K,L. -/
theorem finite_constructible_derivedHom_proEtale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b c e : ℤ) (_hab : a ≤ b) (_hce : c ≤ e)
    (K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hK : finiteTorConstructible l E n hn X K)
    (_hL : finiteTorConstructible l E n hn X L)
    (_hKt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) K a b)
    (_hLt : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n) L c e) :
    finiteTorConstructible l E n hn X
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, L)) ∧
    HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
      ((derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))).obj (op K, L))
      (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ)) := by
  sorry

end WeilConjectures
