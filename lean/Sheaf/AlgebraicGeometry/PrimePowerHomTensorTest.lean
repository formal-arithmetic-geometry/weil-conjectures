/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic

import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology
import Sheaf.Paper.EtaleFlatKFlatResolution
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Sheaf.Algebra.Homology.RingedSiteTorFlatModel
import Mathlib.Algebra.Homology.HomologySequence
import Sheaf.Paper.RestrictedCoefficientHom
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-! # The prime-power Hom and tensor boundedness test

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
Lemma 6.2.2.4, pp. 294--295 (blueprint: lem-per-prime-power-hom-tensor-test).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The coefficient quotient `Z/ell^(r+1) → Z/ell`, with harmless universe lifts.
Source: ILO XVII, Lemma 6.2.2.4 (blueprint: lem-per-prime-power-hom-tensor-test).
Writing the positive exponent as `r+1` includes every exponent at least one. -/
def primePowerResidueMap (l r : ℕ) :
    ULift.{u + 1} (ZMod (l ^ (r + 1))) →+* ULift.{u + 1} (ZMod l) :=
  (ZMod.castHom (dvd_pow_self l (Nat.succ_ne_zero r)) (ZMod l)).ulift

/-- Extension to the residue coefficient sheaves, the left adjoint of exact restriction.
The adjunction determines this functor up to its unique adjunction-compatible isomorphism.
Source: ILO XVII, Lemma 6.2.2.4 (blueprint: lem-per-prime-power-hom-tensor-test). -/
abbrev primePowerResidueExtension (l r : ℕ) (X : Scheme.{u}) :=
  (Sheaf.restrictScalars X.smallEtaleTopology (primePowerResidueMap.{u} l r)).leftAdjoint

/-- The constant residue sheaf, restricted to the prime-power coefficient ring and put
in degree zero. Source: ILO XVII, Lemma 6.2.2.4
(blueprint: lem-per-prime-power-hom-tensor-test). -/
abbrev primePowerResidueComplex (l r : ℕ) (X : Scheme.{u}) :
    DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ (r + 1)))) X :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1)))))).obj
        ((ModuleCat.restrictScalars (primePowerResidueMap.{u} l r)).obj
          (ModuleCat.of (ULift.{u + 1} (ZMod l)) (ULift.{u + 1} (ZMod l)))))

/-- Prime-power coefficient Hom and tensor boundedness criterion, with its normalized
residue-linear comparison.
Source: ILO, Travaux de Gabber, XVII, Lemma 6.2.2.4, pp. 294--295
(blueprint: lem-per-prime-power-hom-tensor-test).

`coextendScalars` is the residue-linear sheaf Hom from the residue coefficient sheaf.
Its right derived functor is therefore RHom with its residue action, not only the
underlying prime-power-coefficient object. Extension is the left adjoint to restriction,
so its value on a flat model computes the residue-linear derived tensor.
The equation involving the two adjunctions specifies the ordinary map
M/ell M → M[ell] by multiplication by ell^r. On every bounded flat representative
its termwise map, followed by the derived unit, is the stated isomorphism in D(k).
Both complexes there are bounded. Its inverse has the orientation RHom → tensor
used in the source. Naturality of δ and the derived unit makes this independent
of the chosen flat model.

Proof:
1. By lem-sfb-bounded-representative choose a bounded representative L in [a,b].
   On the small etale site (def-weil-size-convention), the alternating resolution
   of k has terms R in nonpositive degrees, with maps ell and ell^r. Its exactness
   is ker(ell)=(ell^r), ker(ell^r)=(ell), including r=0 (maps 0 and 1).
   Exact sheafification (lem-weil-pbc-site-module-presheaf-sheafification-exact)
   preserves this resolution; lem-pc-bounded-above-flat-kflat-site makes it K-flat.
2. Its tensor total with L represents the reduction (def-kun-derived-tensor).
   Its Hom complex into L computes RHom: resolve L by bounded-below K-injectives
   (lem-sc-bounded-below-injective-resolution), then use
   lem-sc-bounded-above-finite-free-hom-acyclic and lem-pur-rhom-well-defined.
   Rephase column p, row q by (-1)^(pq+p(p+1)/2). Tensor is bounded above,
   Hom below (def-pur-derived-internal-hom).
3. Extend the alternating columns in both directions. The total C has finite
   diagonals and C ≅ C[2]. Its projection to the nonpositive columns has kernel
   the Hom total shifted by -1. The connecting map is multiplication by ell^r.
4. The long exact cohomology sequence
   (lem-weil-pbc-complex-ses-homology-long-exact) identifies the negative tail of
   C with tensor and its positive tail with shifted Hom. Boundedness of either
   kills one tail; periodicity kills all of C. Conversely acyclic C identifies
   tensor with Hom, so both are bounded. Exact restriction detects this vanishing.
5. Finite Tor amplitude implies bounded reduction by testing k
   (def-kun-tor-amplitude). Conversely choose a flat K-flat resolution Q
   (lem-kun-flat-resolution-existence) and a cohomology interval [u,v] for Q⊗k.
6. For every k-sheaf N, lem-exc-constant-field-sheaf-tensor-cohomology gives
   the same interval for (Q⊗k)⊗k N. The balanced pure-tensor maps identify this
   with Q⊗R N, using lem-pc-sites-module-sheafification-tensor.
7. Filter any R-module sheaf M by images ell^s M. The filtration ends at r+1;
   successive quotients are killed by ell and are k-module sheaves, by exact
   sheafification (lem-weil-pbc-site-module-presheaf-sheafification-exact).
8. Flatness (def-pc-flat-sheaf-modules), the long exact sequence of step 4 and
   descending induction give [u,v] for Q⊗M. This is finite Tor amplitude.
9. Under these conditions lem-sp-ringed-site-tor-flat-model supplies a bounded
   flat representative P, K-flat by lem-pc-bounded-above-flat-kflat-site.
10. Flatness gives ker(ell:M→M)=ell^r M and ker(ell^r:M→M)=ell M.
    Thus multiplication by ell^r identifies M/ell M with M[ell], residue-linearly.
11. The same alternating Hom resolution shows flat sheaves are acyclic for
    G=Hom_R(k,-). Its residue action is lem-weil-pbc-restricted-coefficient-hom;
    enough injectives is prop-pur-kinjective-resolutions-exist, and higher
    derived sheaves are lem-sp-derived-functor-single-identification.
12. src-right-derived-functor-plus-acyclic-unit computes RG on P termwise.
    Compose the termwise map of step 10 with that unit to obtain the displayed
    isomorphism over k. Canonicity follows from the derived tensor counit
    (lem-pur-derived-change-of-rings, lem-pur-left-derived-from-kflat-class),
    the right-derived unit (lem-weil-pbc-right-derived-plus-injective), and
    the localization property (def-weil-abstract-derived-category).
-/
theorem prime_power_hom_tensor_test (l r : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ δ : primePowerResidueExtension l r X ⟶
        coextendScalars (primePowerResidueMap.{u} l r) X,
      (∀ M : Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1))))),
        (Adjunction.ofIsRightAdjoint
            (Sheaf.restrictScalars X.smallEtaleTopology
              (primePowerResidueMap.{u} l r))).unit.app M ≫
          (Sheaf.restrictScalars X.smallEtaleTopology
            (primePowerResidueMap.{u} l r)).map (δ.app M) ≫
          (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology
            (primePowerResidueMap.{u} l r)).counit.app M = (l ^ r) • 𝟙 M) ∧
      ∀ K : _root_.DerivedCategory.Bounded
          (Sheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1)))))),
        ((∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
            (ULift.{u + 1} (ZMod (l ^ (r + 1)))) X a b K.obj) ↔
          _root_.DerivedCategory.TStructure.t.bounded
            (((derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1))))) X).obj
                K.obj).obj (primePowerResidueComplex l r X))) ∧
        (_root_.DerivedCategory.TStructure.t.bounded
            (((derivedTensor
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1))))) X).obj
                K.obj).obj (primePowerResidueComplex l r X)) ↔
          _root_.DerivedCategory.TStructure.t.bounded
            ((coextendScalars (primePowerResidueMap.{u} l r) X).rightDerivedFunctor.obj
              K.obj)) ∧
        ((∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
            (ULift.{u + 1} (ZMod (l ^ (r + 1)))) X a b K.obj) →
          (∃ (a b : ℤ)
            (P : CochainComplex (Sheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1)))))) ℤ),
            IsBoundedFlatComplex (ULift.{u + 1} (ZMod (l ^ (r + 1)))) a b P ∧
            Nonempty ((_root_.DerivedCategory.Q.obj P) ≅ K.obj)) ∧
          ∀ (a b : ℤ)
            (P : CochainComplex (Sheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1)))))) ℤ)
            (e : (_root_.DerivedCategory.Q.obj P) ≅ K.obj),
            IsBoundedFlatComplex (ULift.{u + 1} (ZMod (l ^ (r + 1)))) a b P →
            _root_.DerivedCategory.TStructure.t.bounded
              (_root_.DerivedCategory.Q.obj
                (((primePowerResidueExtension l r X).mapHomologicalComplex (.up ℤ)).obj P)) ∧
            IsIso
              ((coextendScalars (primePowerResidueMap.{u} l r) X).rightDerivedFunctorUnit.app
                ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ∧
            ∃ i : _root_.DerivedCategory.Q.obj
                (((primePowerResidueExtension l r X).mapHomologicalComplex (.up ℤ)).obj P) ≅
                (coextendScalars (primePowerResidueMap.{u} l r) X).rightDerivedFunctor.obj
                  K.obj,
              i.hom = _root_.DerivedCategory.Q.map
                  ((NatTrans.mapHomologicalComplex δ (.up ℤ)).app P) ≫
                (coextendScalars (primePowerResidueMap.{u} l r) X).rightDerivedFunctorUnit.app
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
                (coextendScalars (primePowerResidueMap.{u} l r) X).rightDerivedFunctor.map
                  e.hom ∧
              Nonempty ((Sheaf.restrictScalars X.smallEtaleTopology
                  (primePowerResidueMap.{u} l r)).mapDerivedCategory.obj
                    (_root_.DerivedCategory.Q.obj
                      (((primePowerResidueExtension l r X).mapHomologicalComplex (.up ℤ)).obj
                        P)) ≅
                (((derivedTensor
                  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (l ^ (r + 1))))) X).obj
                    K.obj).obj (primePowerResidueComplex l r X)))) := by
  sorry

end AlgebraicGeometry.Etale
