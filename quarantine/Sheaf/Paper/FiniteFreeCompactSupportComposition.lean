/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteCoefficientAdjointComparisons
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.OpenExtensionFiniteTor
public import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.ProperOpenCoefficientRefinement
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.RefinementComparisonIsomorphism
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.SfDirectImageCTFNonproper
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.SixFunctors.ComparisonOpenTensorCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-! # Finite-free coefficient extension and compact-support composition

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: lem-pur-finite-free-compact-composition).
The two Boolean cases are the ordinary small etale site and its pro-etale realization.
All equations live in the B-linear derived category. The proper and open maps, and
both geometric comparisons, are the existing normalized constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteFreeCompactSupport

/-- Realization of an ordinary etale object on the selected site.
Source: blueprint transport Step 8 (blueprint: lem-pur-finite-free-compact-composition). -/
def realization (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.DerivedCategoryModule A X ⥤ Sites.D pro A X := by
  cases pro
  · exact 𝟭 _
  · exact Sites.nu A X

/-- The existing compactification candidate, on either of the two ordinary small sites.
Source: blueprint transport Steps 2 and 8
(blueprint: lem-pur-finite-free-compact-composition). -/
def support (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sites.D pro A X ⥤ Sites.D pro A Y := by
  cases pro
  · exact Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  · exact ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The specified coefficient map: the existing extended-counit proper map followed
by the balancing open map. In the pro-etale presentation it is the existing universal
scalar-adjunction formula for precisely those constituents.
Source: blueprint transport Steps 2 and 8
(blueprint: lem-pur-finite-free-compact-composition). -/
def coefficientMap (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Sites.D pro A X) :
    (Sites.scalar pro φ Y).obj ((support pro A c).obj K) ⟶
      (support pro B c).obj ((Sites.scalar pro φ X).obj K) := by
  cases pro
  · exact Etale.ExceptionalCoefficients.compactSupportMap φ c K
  · exact ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)).homEquiv _ _).symm
      ((support true A c).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).unit.app K) ≫
        (ProEtale.compactSupportRestrictionIso φ c).hom.app
          ((Sites.scalar true φ X).obj K))

/-- The canonical etale compositor in the ambient derived categories; only the
published D-plus compatibility isomorphisms are inserted.
Source: blueprint transport Steps 4--7
(blueprint: lem-pur-finite-free-compact-composition). -/
def etaleComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support false A d).obj ((support false A c).obj L.obj) ⟶
      (support false A e).obj L.obj :=
  (support false A d).map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj L) ≫
    DerivedCategory.Plus.ι.map ((ProEtale.coherenceEtaleCompositor A c d e).hom.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) e).hom.app L

/-- The actual canonical composition map at an etale realization.
Source: blueprint transport Steps 4--8
(blueprint: lem-pur-finite-free-compact-composition). -/
def compositionReal (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support pro A d).obj ((support pro A c).obj ((realization pro A X).obj L.obj)) ⟶
      (support pro A e).obj ((realization pro A X).obj L.obj) := by
  cases pro
  · exact etaleComposition A c d e L
  · exact ProEtale.coherenceProEtaleCompositor A c d e L

/-- Composition at an arbitrary retained origin witness, by canonical naturality.
Source: blueprint transport Steps 7--8
(blueprint: lem-pur-finite-free-compact-composition). -/
def composition (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    {K : Sites.D pro A X}
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (realization pro A X).obj L.obj ≅ K) :
    (support pro A d).obj ((support pro A c).obj K) ⟶ (support pro A e).obj K :=
  (support pro A d).map ((support pro A c).map α.inv) ≫
    compositionReal pro A c d e L ≫ (support pro A e).map α.hom

/-- The inverse of the recorded etale refinement comparison, in ambient categories.
Its direction is from the dominating compactification c to d.
Source: blueprint transport Step 3
(blueprint: lem-pur-finite-free-compact-composition). -/
def etaleRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support false A c).obj L.obj ⟶ (support false A d).obj L.obj :=
  (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).inv.app L ≫
    DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).hom.app L

/-- The actual proper-refinement arrow on each site, evaluated at a retained witness.
Source: blueprint transport Steps 3 and 8
(blueprint: lem-pur-finite-free-compact-composition). -/
def refinement (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    {K : Sites.D pro A X}
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (realization pro A X).obj L.obj ≅ K) :
    (support pro A c).obj K ⟶ (support pro A d).obj K :=
  (support pro A c).map α.inv ≫ (by
    cases pro
    · exact etaleRefinement A r L
    · exact (ProEtale.properTransportRefinement A r L).hom) ≫
    (support pro A d).map α.hom

/-- The coefficient/site square, with the proper/open site comparisons and the
scalar/site balancing explicitly inserted. N and gamma merely present the bounded
scalar extension of L; every possible such presentation is allowed.
Source: blueprint transport Step 8
(blueprint: lem-pur-finite-free-compact-composition). -/
def SiteCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (γ : N.obj ≅ (Sites.scalar false φ X).obj L.obj) : Prop :=
  coefficientMap true φ c ((Sites.nu A X).obj L.obj) =
    (Sites.scalar true φ Y).map
        ((ProEtale.compactSupportSiteComparison A c).hom.app L) ≫
      (Sites.scalarSite φ Y).hom.app ((support false A c).obj L.obj) ≫
      (Sites.nu B Y).map (coefficientMap false φ c L.obj) ≫
      (Sites.nu B Y).map ((support false B c).map γ.inv) ≫
      (ProEtale.compactSupportSiteComparison B c).inv.app N ≫
      (support true B c).map ((Sites.nu B X).map γ.hom) ≫
      (support true B c).map ((Sites.scalarSite φ X).inv.app L.obj)

/-- Finite-free extension preserves the specified coefficient maps, refinement and
composition, as actual B-linear arrows on both sites.
Source: blueprint main-20261015, sk-thm-purity-transport.proof.md Steps 1 and 3
(blueprint: lem-pur-finite-free-compact-composition).

Proof (the eight steps of the node):
1. lem-coef-finite-free-extension identifies the ramified quotient with the quotient
by the nth power of the base uniformizer, and makes its scalar map finite free.
lem-pur-derived-change-of-rings computes it termwise on K-flat representatives.
lem-trf-open-ctf, cor-sf-direct-image-ctf-nonproper, its pro-etale counterpart, and
lem-kun-dimension-finite-type certify every intermediate constructible Tor domain.
lem-sf-proetale-constructible-origin supplies all witnesses used in the statement.
2. On c=(j,p), lem-coef-finite-direct-image makes the proper extended-counit map
invertible. lem-pur-etale-open-derived-tensor gives the open balancing isomorphism.
Their composite is coefficientMap; both maps retain the B action.
3. Apply lem-sf-proper-open-coefficient-refinement to the specified proper/open alpha.
Apply Rp_* and naturality of its coefficient map, then its composition identity.
Invert the two geometric refinement comparisons to obtain the displayed square.
4. For compatible compactifications, the proper composition square is the identity
of lem-coef-finite-direct-image. The open composition square follows termwise from
lem-cbc-extension-zero-composition: both maps keep the same supported sections.
5. The middle proper/open interchange is the normalized map of
lem-cbc-proper-open-interchange-coherence. On bounded-below injectives it equals
lem-amb-unbounded-proper-open-interchange. Scalar/pullback balancing agrees on
K-flat tensors; lem-weil-pbc-mate-pasting gives its counit-mate exchange square.
6. Insert the open balancing unit identity into that square and transpose under the
open adjunction. Both transposes reduce to the proper coefficient map. Injectivity
of the adjunction bijection proves the B-linear interchange square. Pasting with
Step 4 gives the composition equation for the compatible compactifications.
7. Use Step 3 to conjugate by comparisons to arbitrary compactifications. Their
coherence (lem-amb-etale-compact-comparisons) cancels adjacent inverse comparisons.
8. Transport through lem-sf-class-compact-support-comparison. Scalar/site balancing
is Sites.scalarSite. Proper maps transport by the fixed counit mate and direct-image
composition; open maps by lem-cbc-proetale-extension-zero-comparison and
lem-sf-comparison-open-tensor-coherence. Mate pasting transports the interchange.
lem-pur-compact-support-site-coherence and the proper/open site normalization
transport both geometric comparisons. Naturality inserts any retained witness,
including arbitrary isomorphic realizations and identity witnesses. -/
theorem finite_free_compactSupport_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) (t : Stage l E) (a : Arrow (baseStage n) t)
    (_level : t.exponent = n) (pro : Bool)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (K : Sites.D pro (baseStage (l := l) (E := E) n).ring X)
    (_hK : Sites.Ctf pro (baseStage (l := l) (E := E) n).ring X K) :
    (∀ (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
          (baseStage (l := l) (E := E) n).ring))),
      Sites.Ctf false (baseStage (l := l) (E := E) n).ring X L.obj →
      ∀ (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
        (γ : N.obj ≅ (Sites.scalar false a.ringMap X).obj L.obj),
        SiteCompatibility a.ringMap c L N γ) ∧
    IsIso (coefficientMap pro a.ringMap c K) ∧
    (∀ (K' : Sites.D pro (baseStage (l := l) (E := E) n).ring X),
      Sites.Ctf pro (baseStage (l := l) (E := E) n).ring X K' → ∀ v : K ⟶ K',
      (Sites.scalar pro a.ringMap Y).map ((support pro _ c).map v) ≫
          coefficientMap pro a.ringMap c K' =
        coefficientMap pro a.ringMap c K ≫
          (support pro t.ring c).map ((Sites.scalar pro a.ringMap X).map v)) ∧
    (∃ (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (baseStage (l := l) (E := E) n).ring))),
      Nonempty ((realization pro _ X).obj L.obj ≅ K)) ∧
    (∃ (N : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring))),
      Nonempty ((realization pro _ X).obj N.obj ≅ (Sites.scalar pro a.ringMap X).obj K)) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (baseStage (l := l) (E := E) n).ring)))
      (α : (realization pro _ X).obj L.obj ≅ K)
      (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
      (β : (realization pro _ X).obj N.obj ≅ (Sites.scalar pro a.ringMap X).obj K),
      (Sites.scalar pro a.ringMap Z).map (composition pro _ c d e L α) ≫
          coefficientMap pro a.ringMap e K =
        coefficientMap pro a.ringMap d ((support pro _ c).obj K) ≫
          (support pro t.ring d).map (coefficientMap pro a.ringMap c K) ≫
            composition pro t.ring c d e N β ∧
      ∀ (c' : Compactification f) (r : c'.Refinement c),
        (Sites.scalar pro a.ringMap Y).map (refinement pro _ r L α) ≫
            coefficientMap pro a.ringMap c K =
          coefficientMap pro a.ringMap c' K ≫ refinement pro t.ring r N β) := by
  sorry

end AlgebraicGeometry.FiniteFreeCompactSupport
