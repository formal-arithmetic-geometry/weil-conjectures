/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Point.Basic

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.GeometricStalkToposPoint
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Paper.SiteBoundedConstantModel
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Connected étale finite-Tor complexes are locally constant perfect complexes

Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI, lemma-connected-ctf-locally-constant;
the weakly contractible pro-étale corollary is from `proetale.tex`, Tag 09C6,
and `sites.tex`, Tag 090K (blueprint: lem-sfb-connected-etale-perfect-constant).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The derived geometric stalk, obtained from the exact fibre functor.
Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI
(blueprint: lem-sfb-connected-etale-perfect-constant). -/
noncomputable def geometricStalk
    (R : Type (u + 1)) [CommRing R] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} R) := by
  let F := (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)
  letI : F.Additive := (pointSmallEtale x).sheafFiber_additive
  exact F.mapDerivedCategory

/-- A connected étale complex with finite locally constant cohomology and finite Tor
amplitude is locally a constant perfect ring complex, with the same geometric stalk.

Source: Stacks Project, `etale-cohomology.tex`, Tag 09BI, lemma-connected-ctf-locally-constant;
the weakly contractible clause is the trivialization in `proetale.tex`, Tag 09C6,
using `sites.tex`, Tag 090K (blueprint: lem-sfb-connected-etale-perfect-constant).

Proof. Choose a K-flat flat-term representative and apply the bounded constant-model lemma
using the unit coefficient sheaf.  On overlaps, exact geometric stalks identify the local
models; openness of étale maps and connectedness of `X` show that one model occurs.  A
geometric stalk and the Tor hypothesis transfer the Tor interval to this finite complex;
the bounded finite-Tor perfectness theorem replaces it by a bounded finite-projective
complex `E`.  Exact constant-sheaf construction gives the asserted étale-local models and
stalk identifications.  For a weakly contractible affine pro-étale object, pull the cover
back, refine it by finitely many affines, form their finite disjoint coproduct, and split
its representable covering by weak contractibility.  Restriction along the resulting section
assembles the local isomorphisms over `W`, including the empty case.
-/
theorem connected_etale_perfect_constant
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X]
    (L : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L))
    (hlisse : ∀ q : ℤ,
      IsLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        Module.Finite R
          (((pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} R)).obj
            ((DerivedCategory.homologyFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj L)))
    (hTor : ∃ a b : ℤ, a ≤ b ∧ ∀
      (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (q : ℤ),
      q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) q).obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).obj
          ((DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) 0).obj F)))) :
    ∃ (E : _root_.DerivedCategory (ModuleCat.{u + 1} R)),
      DerivedCategory.IsPerfectRingComplex E ∧
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage X),
        (∀ i : 𝒰.I₀,
          Nonempty
            ((Etale.upperStar (ModuleCat.{u + 1} R) (𝒰.f i)).mapDerivedCategory.obj L ≅
              ((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E))) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (x : Spec (.of Ω) ⟶ X),
          Nonempty (E ≅ ((geometricStalk R x).obj L))) ∧
        (∀ (W : X.ProEt) [IsAffine W.left],
          (hW : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W) →
          Nonempty
            (((ProEtale.upperStar (ModuleCat.{u + 1} R) W.hom).mapDerivedCategory.obj
              ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L)) ≅
              ((constantSheaf (Scheme.ProEt.topology W.left)
                (ModuleCat.{u + 1} R)).mapDerivedCategory.obj E)))
    := by
  sorry

end AlgebraicGeometry.Etale
