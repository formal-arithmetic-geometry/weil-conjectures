/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.SiteRestrictionExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.CategoryTheory.RingedToposKFlatPullback
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Paper.EtaleSitePerfectConstructibleHom
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.SitePerfectTorWindow
import Sheaf.AlgebraicGeometry.EtaleSheafZeroOnCover
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Derived internal Hom at finite coefficients on the etale site

Source: Weil conjectures blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
node thm-sf-hom-ctf, order 2199 (blueprint: thm-sf-hom-ctf).
The current main-20261015 snapshot has the same theorem at order 2543.

The finite-Tor constructible predicate is the recorded etale presentation. The coefficient
ring has its canonical universe lift. Internal Hom and site-perfectness use the existing
etale module-sheaf interfaces: local models are bounded complexes of retracts of finite
free constant module sheaves. No separatedness of the structure morphism is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Internal Hom preserves finite-Tor bounded constructibility, with a dimension-dependent
Tor interval and the sharper interval when the first argument is site-perfect.
Source: Weil blueprint, thm-sf-hom-ctf, order 2199 (blueprint: thm-sf-hom-ctf).

Proof:
1. Slice restriction is exact by lem-weil-pbc-site-restriction-exact. Using K-flat models
from lem-weil-pbc-site-derived-tensor-descent, their preservation under localized pullback
(lem-weil-pbc-supplied-ringed-topos-kflat-pullback), and the degreewise tensor comparison
(lem-weil-pbc-ringed-topoi-module-pullback-tensor), restriction commutes with derived tensor.
The Hom restriction comparison is lem-weil-pbc-ringed-internal-hom-exact-restriction.
2. Finite type over the affine field base gives a finite affine open cover of X. Each member
is separated over k by lem-weil-pbc-affine-source-morphism-separated and has dimension at
most m by lem-weil-pbc-open-subspace-dimension-monotone. The scheme is Noetherian, hence
qcqs, by lem-weil-pbc-finite-type-over-noetherian. The empty scheme permits an empty cover.
3. Restrict the bounded flat models in [a,b] and [c,d] from lem-sf-flat-model. Flatness
is preserved by lem-weil-pbc-slice-restriction-flat, and Step 1 preserves their derived
identifications. Constructibility restricts by lem-weil-pbc-constructible-qcqs-affine-local.
4. Apply cor-weil-finite-constructible-hom on every affine member with the same parameter m.
Its Verdier-biduality and tensor argument gives bounded constructibility and the common
interval [c-b-2m,d-a+2m]. Step 1 identifies these with restrictions of the global Hom.
5. Test tensor against any module sheaf in degree zero. Cohomology vanishes outside that
interval after restriction to the cover, hence globally by the sheaf axiom. Testing the
coefficient sheaf gives boundedness. For each cohomology sheaf G, its restrictions to the
cover and overlaps are constructible. The overlaps are finite type by
lem-weil-pbc-qc-open-immersion-finite-type. Apply thm-fin-open-immersion to the cover members
and overlaps; their degree-zero direct images are constructible, with the section formula
of def-weil-pbc-direct-image. Sheaf gluing expresses G as the kernel of the difference map
between the two finite sums of these direct images. The finite-sum and kernel clauses of
thm-constructible-serre give constructibility, including the empty-cover case.
6. If K is site-perfect, lem-sf-site-perfect-tor-window gives local finite-projective models
P in the prescribed interval [a,b]. Independently choose a bounded flat model F of M in
[c,d] by lem-sf-flat-model; its restrictions remain flat by
lem-weil-pbc-slice-restriction-flat.
7. The Hom complex of def-pur-hom-complex computes derived Hom from bounded P to F.
For a single finite-free retract P^i, sheaf Hom is a retract of a finite power, hence exact,
and finite-projective evaluation identifies it with (P^i)-dual tensor. Induct on the number
of terms of P, using the long exact sequence of
lem-weil-pbc-complex-ses-homology-long-exact, to show Hom(P,-) preserves quasi-isomorphisms.
Apply this to a K-injective replacement of F and use def-pur-derived-internal-hom.
8. Degree r of Hom(P,F) is the finite sum of Hom(P^i,F^(i+r)). These are flat finite-free
retracts of powers of F^(i+r), and vanish unless c-b <= r <= d-a. Induction on the endpoint
filtration proves that this bounded flat complex is K-flat (def-pc-kflat-complex), so tensor
against any degree-zero module is still supported in [c-b,d-a].
9. Step 1 and the sheaf axiom descend the sharper tensor vanishing globally. Testing the
coefficient sheaf gives boundedness; lem-sf-ext-sheaf-constructible supplies constructibility
in this case independently of the general Verdier-duality argument. -/
theorem finiteCoefficient_derivedHom_ctf_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℕ) (_hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : finiteTorConstructibleEtale l E n hn X K)
    (_hM : finiteTorConstructibleEtale l E n hn X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X c d M) :
    finiteTorConstructibleEtale l E n hn X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X (c - b) (d - a)
        (((Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M)) := by
  sorry

end WeilConjectures
