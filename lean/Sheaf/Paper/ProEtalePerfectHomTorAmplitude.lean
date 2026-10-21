/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ConstructibleHomComparison
import Sheaf.Paper.EtaleHomFiniteTorAmplitude

/-!
# Pro-etale internal Hom with a site-perfect first argument

Source: Weil blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
cor-sf-hom-ctf-proetale-unconditional, order 2200
(blueprint: cor-sf-hom-ctf-proetale-unconditional).

The comparison is the recorded exact inverse image, expressed by the canonical
constant-ring realization. Internal Hom is the recorded K-injective construction.
The local finite-projective hypothesis uses the existing coefficient-site perfectness
predicate, whose data are a covering and bounded finite-projective local models.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The internal Hom of the two comparison inverse images, with its actual canonical
construction. The finiteness proof is explicit so positive coefficient levels do not
require an extra finiteness hypothesis or a file-local instance.
Source: Weil blueprint, cor-sf-hom-ctf-proetale-unconditional, order 2200;
Stacks, Tag 08J7 (blueprint: cor-sf-hom-ctf-proetale-unconditional). -/
noncomputable def finiteCoefficientComparisonRHom (X : Scheme.{u})
    (A : Type u) [CommRing A] (hA : Finite A)
    (K M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X) :
    proEtaleDerivedCategory X A :=
  letI := hA
  (derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
    (ProEt.topology X) (proEtaleConstantRing X A)).obj
      (op ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj K),
        (ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj M)

/-- The pro-etale internal Hom of etale-origin bounded constructible complexes is
bounded constructible with the sharp Tor interval when the first complex is site-perfect.
Source: Weil blueprint, cor-sf-hom-ctf-proetale-unconditional, order 2200
(blueprint: cor-sf-hom-ctf-proetale-unconditional).

Proof:
1. Apply lem-fin-finite-type-fibre-dimension-bound to the structure morphism to
Spec k. Its base has one point, so its fibre is X and gives a finite dimension bound.
2. Apply thm-sf-hom-ctf on the etale site. The first argument is site-perfect by
the covering and finite-free retractions in IsSitePerfect, so the sharper clause puts
H' = RHom(K,M) in bounded constructible complexes with Tor interval [c-b,d-a].
3. Apply thm-sf-hom-comparison-constructible to identify the inverse image of H'
with finiteCoefficientComparisonRHom X A K M. This is the canonical comparison,
using the same finite coefficients on both sites.
4. The prime l is invertible on X, since l differs from the characteristic p of k.
Clause (i) of lem-sf-comparison-tor-amplitude preserves bounded constructibility
and the interval [c-b,d-a]. Transport these properties through the comparison
isomorphism. Tensoring that isomorphism with every degree-zero pro-etale module
sheaf proves the Tor bound against all such sheaves, not only etale-origin ones.
-/
theorem finiteCoefficientComparisonRHom_boundedConstructible_torAmplitude
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) X K)
    (_hM : @Etale.DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X c d M)
    (_hPerfect : Etale.DerivedCategory.IsSitePerfect K) :
    intrinsicFiniteTorsionConstructible l E n hn X
        (finiteCoefficientComparisonRHom X (Padic.coefficientExtensionRing l E n)
          (Padic.finite_coefficientExtensionRing l E n hn) K M) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
        (finiteCoefficientComparisonRHom X (Padic.coefficientExtensionRing l E n)
          (Padic.finite_coefficientExtensionRing l E n hn) K M) (c - b) (d - a) := by
  sorry

end AlgebraicGeometry.Scheme
