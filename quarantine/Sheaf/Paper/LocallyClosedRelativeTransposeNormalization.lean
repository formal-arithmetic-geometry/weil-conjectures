/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison

public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Finite.Exact

/-! # Locally closed relative transpose normalization

Source: blueprint main-20261015, lem-weil-finite-duality-site-comparison, second paragraph;
Stacks Project, Tags 0037, 0B65 and 099V
(blueprint: lem-sf-locally-closed-relative-transpose-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The canonical chosen closure compactification, with its actual scheme-theoretic image.
Source: Stacks Tags 01R6--01R8; blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeClosure {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [QuasiCompact s] : Compactification s where
  Z := s.image
  g := s.imageι
  i := s.toImage
  comm := (Scheme.Hom.toImage_imageι s).symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The closed-then-open ordinary etale forward functor.
Source: blueprint locally closed comparison, F_e
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev relativeTransposeEtaleForward (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The closed-then-open ordinary pro-etale forward functor.
Source: blueprint locally closed comparison, F_p
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev relativeTransposeProEtaleForward (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory

/-- The actual pasted etale adjunction, with the closed right adjoint fixed by its
universal property. Source: blueprint locally closed comparison, F_e adjoint J_e
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeEtaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    relativeTransposeEtaleForward A c v ⊣
      (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.rightAdjoint :=
  (Adjunction.ofIsLeftAdjoint
    (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor).comp
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)

/-- The actual pasted closed-support/open pro-etale adjunction.
Source: blueprint locally closed comparison, F_p adjoint J_p; Stacks 09BM
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeProEtaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T W : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) (j : W ⟶ V)
    [IsClosedImmersion c] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcj : IsCompl (Set.range c.base) (Set.range j.base)) :
    relativeTransposeProEtaleForward A c v ⊣
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
        (closedUpperShriek (ModuleCat.{u + 1} A) c j).rightDerivedFunctor :=
  (derivedLowerStarClosedUpperShriekAdjunction (R := A) c j hcj).comp
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v)

/-- The open comparison on ordinary derived categories is the termwise sheaf comparison.
Source: Stacks 09AF; blueprint open comparison used in Delta
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeOpenComparison (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) [IsOpenImmersion v] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) v) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The closed counit mate, included into the ordinary categories via the canonical
bounded-below compatibility isomorphisms. Source: Stacks 099R, 0B65
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeClosedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V : Scheme.{u}} (c : S ⟶ V) [IsClosedImmersion c]
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.obj L.obj) ≅
      (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj) :=
  letI := isIso_fixedComparisonDirectImageMatePlus A c
  (comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategory.mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility.app
        L).symm ≪≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlusCompatibility.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus.obj L)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso ((fixedComparisonDirectImageMatePlus A c).app L)) ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlusCompatibility.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlus.obj L)) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategoryPlusCompatibility.app L)

/-- Delta is the open comparison followed by open extension of the named closed mate.
Source: blueprint locally closed comparison, displayed Delta_L
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeDelta (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        ((relativeTransposeEtaleForward A c v).obj L.obj) ≅
      (relativeTransposeProEtaleForward A c v).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj L.obj) :=
  (relativeTransposeOpenComparison A v).app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctor.obj L.obj) ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategory.mapIso
      (relativeTransposeClosedComparison A c L)


/-- The canonical complementary open subscheme to a closed immersion.
Source: Stacks 09BM; blueprint closed-support adjunction
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeComplement {S V : Scheme.{u}} (c : S ⟶ V)
    [IsClosedImmersion c] : V.Opens :=
  ⟨(Set.range c.base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding c).isClosed_range.isOpen_compl⟩

/-- Closed direct image is exact in the Noetherian ambient case, using the published
complementary-open exactness theorem. Source: Stacks 09BM
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
instance relativeTransposeClosedExact (A : Type (u + 1)) [CommRing A]
    {S V : Scheme.{u}} (c : S ⟶ V) [IsClosedImmersion c] [IsNoetherian V] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) c) :=
  preservesFiniteColimits_lowerStar_of_isCompl (R := A) c
    (relativeTransposeComplement c).ι
    (by rw [Scheme.Opens.range_ι]; exact isCompl_compl)

/-- The closure restriction normalization on fixed-scalar pro-etale sheaves, formed from
pullback composition, the closed counit, and inverse open unit. Source: Stacks 09BM, 03DI
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeProEtaleClosureRestriction (A : Type (u + 1)) [CommRing A]
    {S T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
      lowerStar (ModuleCat.{u + 1} A) s.imageι) ⋙
      upperStar (ModuleCat.{u + 1} A) s ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _
          (upperStarFactor (ModuleCat.{u + 1} A) (Scheme.Hom.toImage_imageι s)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (asIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s.imageι).counit) _ ≪≫
        Functor.leftUnitor _) ≪≫
    (asIso (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) s.toImage).unit).symm

/-- The closed-then-open restriction normalization on fixed-scalar pro-etale sheaves.
Source: Stacks 09BM, 03DI; blueprint identity-normalized factorization comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeProEtaleFactorRestriction (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (s : S ⟶ T) (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (hs : c ≫ v = s) :
    (lowerStar (ModuleCat.{u + 1} A) c ⋙ openImmersionLowerShriek
      (ModuleCat.{u + 1} A) v) ⋙ upperStar (ModuleCat.{u + 1} A) s ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (upperStarFactor (ModuleCat.{u + 1} A) hs) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (asIso (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) v).unit).symm _ ≪≫ Functor.leftUnitor _) ≪≫
    asIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c).counit

/-- Termwise descent of the specified etale factorization comparison, with the exact
closed direct images identified with their right derived functors. Source: Stacks 0GJ1
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeEtaleQ (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (q : Etale.lowerStar (ModuleCat.{u + 1} A) c ⋙
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v ≅
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
          Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι) :
    relativeTransposeEtaleForward A c v ≅
      Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (relativeTransposeClosure s) :=
  Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso q ≪≫ Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- Termwise descent of the specified pro-etale factorization comparison.
Source: Stacks 09BM, 03DI; blueprint normalized locally closed extension coherence
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeProEtaleQ (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (s : S ⟶ T) [IsImmersion s] [QuasiCompact s]
    [IsNoetherian V] [IsNoetherian T]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (q : lowerStar (ModuleCat.{u + 1} A) c ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) v ≅
        openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
          lowerStar (ModuleCat.{u + 1} A) s.imageι) :
    relativeTransposeProEtaleForward A c v ≅
      rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (relativeTransposeClosure s) :=
  Functor.isoWhiskerRight
      (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorIsoMapDerivedCategory _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso q ≪≫ Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _
      (lowerStar (ModuleCat.{u + 1} A) s.imageι).rightDerivedFunctorIsoMapDerivedCategory.symm


/-- The geometric hypotheses of the locally closed normalization, with the supplied
closed-then-open factorization retained. This is a bundle of the quantified inputs only.
Source: blueprint locally closed comparison, first paragraph
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
structure RelativeTransposeGeometry (P : WeilConjectures.PurityFiniteSetting.{u}) where
  S : Scheme.{u}
  V : Scheme.{u}
  T : Scheme.{u}
  aS : S ⟶ Spec (.of P.field.k)
  aT : T ⟶ Spec (.of P.field.k)
  [finiteTypeS : LocallyOfFiniteType aS]
  [quasiCompactS : QuasiCompact aS]
  [separatedS : IsSeparated aS]
  [finiteTypeT : LocallyOfFiniteType aT]
  [quasiCompactT : QuasiCompact aT]
  [separatedT : IsSeparated aT]
  c : S ⟶ V
  v : V ⟶ T
  [closed : IsClosedImmersion c]
  [opened : IsOpenImmersion v]
  over_base : (c ≫ v) ≫ aT = aS

attribute [instance] RelativeTransposeGeometry.finiteTypeS
  RelativeTransposeGeometry.quasiCompactS RelativeTransposeGeometry.separatedS
  RelativeTransposeGeometry.finiteTypeT RelativeTransposeGeometry.quasiCompactT
  RelativeTransposeGeometry.separatedT RelativeTransposeGeometry.closed
  RelativeTransposeGeometry.opened

namespace RelativeTransposeGeometry
variable {P : WeilConjectures.PurityFiniteSetting.{u}} (D : RelativeTransposeGeometry P)

/-- The immersion s is the retained composite. Source: blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev s := D.c ≫ D.v

/-- The target is Noetherian by its given finite-type structure map over the field.
Source: Stacks 01T6; blueprint Noetherian domain check
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
instance noetherianT : IsNoetherian D.T := isNoetherian_of_locallyOfFiniteType D.aT

/-- The open ambient scheme is Noetherian as an open of the given Noetherian target.
Source: Stacks 01T6; blueprint Noetherian domain check
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
instance noetherianV : IsNoetherian D.V where
  toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion D.v
  toCompactSpace :=
    letI : TopologicalSpace.NoetherianSpace D.V := D.v.isOpenEmbedding.isInducing.noetherianSpace
    inferInstance

/-- F_e of the node. Source: blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Fe := relativeTransposeEtaleForward P.Coefficient D.c D.v

/-- F_p of the node. Source: blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Fp := relativeTransposeProEtaleForward P.Coefficient D.c D.v

/-- J_e of the node, on the ordinary derived category. Source: blueprint local comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Je :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) D.v).mapDerivedCategory ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) D.c).rightDerivedFunctor.rightAdjoint

/-- J_p of the node, using the canonical complementary open in the support kernel.
Source: Stacks 09BM; blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Jp :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) D.v).mapDerivedCategory ⋙
    (closedUpperShriek (ModuleCat.{u + 1} P.Coefficient) D.c
      (relativeTransposeComplement D.c).ι).rightDerivedFunctor

/-- The etale pasted adjunction. Source: blueprint locally closed comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def adjE : D.Fe ⊣ D.Je := relativeTransposeEtaleAdjunction P.Coefficient D.c D.v

/-- The pro-etale pasted adjunction. Source: Stacks 09BM; blueprint local comparison
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def adjP : D.Fp ⊣ D.Jp :=
  relativeTransposeProEtaleAdjunction P.Coefficient D.c D.v
    (relativeTransposeComplement D.c).ι
    (by rw [Scheme.Opens.range_ι]; exact isCompl_compl)

/-- The exact comparison functor at S. Source: Stacks 099R
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev CS := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) D.S).mapDerivedCategory

/-- The exact comparison functor at T. Source: Stacks 099R
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev CT := (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) D.T).mapDerivedCategory

/-- The canonical chosen-closure compactification. Source: Stacks 01R6--01R8
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev closure := relativeTransposeClosure D.s

/-- E_e is ordinary etale compact support at the canonical closure. Source: blueprint
locally closed comparison (blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Ee := Etale.rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} P.Coefficient) D.closure

/-- E_p is ordinary pro-etale compact support at that same closure. Source: blueprint
locally closed comparison (blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Ep := rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} P.Coefficient) D.closure

/-- The actual natural isomorphism Delta. Source: blueprint displayed Delta_L
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def delta (L : DerivedCategory.Plus
    (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    D.CT.obj (D.Fe.obj L.obj) ≅ D.Fp.obj (D.CS.obj L.obj) :=
  relativeTransposeDelta P.Coefficient D.c D.v L

/-- B is the inverse of the published closure compact-support comparison, hence uses
exactly the closed counit mate and open comparison. Source: blueprint displayed B_L
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def B (L : DerivedCategory.Plus
    (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) :
    D.CT.obj (D.Ee.obj L.obj) ≅ D.Ep.obj (D.CS.obj L.obj) :=
  (compactSupportSiteComparison P.Coefficient D.closure).symm.app L

end RelativeTransposeGeometry

/-- The supplied identity-normalized termwise extension identifications, with exactly
the compatibility square assumed in the node. No comparison is selected from bare
existence: both retained maps must restrict to the displayed identity normalizations.
Source: Stacks 0GJ1 and 09BM; blueprint locally closed normalization, q_e and q_p
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
structure RelativeTransposeIdentifications {P : WeilConjectures.PurityFiniteSetting.{u}}
    (D : RelativeTransposeGeometry P) where
  etale : Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) D.c ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.v ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.s.toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) D.s.imageι
  etale_normalized :
    Functor.isoWhiskerRight etale (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) D.s) ≪≫
      etaleLocallyClosedExtensionRestrictionIso (A := P.Coefficient) D.s inferInstance =
        etaleFactorizationRestrictionIso (A := P.Coefficient) D.s D.c D.v rfl
  proetale : lowerStar (ModuleCat.{u + 1} P.Coefficient) D.c ⋙
    openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.v ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.s.toImage ⋙
        lowerStar (ModuleCat.{u + 1} P.Coefficient) D.s.imageι
  proetale_normalized :
    Functor.isoWhiskerRight proetale (upperStar (ModuleCat.{u + 1} P.Coefficient) D.s) ≪≫
      relativeTransposeProEtaleClosureRestriction P.Coefficient D.s =
        relativeTransposeProEtaleFactorRestriction P.Coefficient D.s D.c D.v rfl
  square : ∀ L : DerivedCategory.Plus
      (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    (D.delta L).hom ≫
        (relativeTransposeProEtaleQ P.Coefficient D.s D.c D.v proetale).hom.app
          (D.CS.obj L.obj) =
      D.CT.map ((relativeTransposeEtaleQ P.Coefficient D.s D.c D.v etale).hom.app L.obj) ≫
        (D.B L).hom

namespace RelativeTransposeIdentifications
variable {P : WeilConjectures.PurityFiniteSetting.{u}} {D : RelativeTransposeGeometry P}
  (N : RelativeTransposeIdentifications D)

/-- The retained termwise q_e, on ordinary derived categories. Source: blueprint q_e
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def qE : D.Fe ≅ D.Ee := relativeTransposeEtaleQ P.Coefficient D.s D.c D.v N.etale

/-- The retained termwise q_p, on ordinary derived categories. Source: blueprint q_p
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def qP : D.Fp ≅ D.Ep := relativeTransposeProEtaleQ P.Coefficient D.s D.c D.v N.proetale

/-- The conjugated compact-support adjunction: in these coordinates s-times is J_e,
and its counit is the pasted counit precomposed with q_e inverse. Source: Stacks 0B65
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def closureAdjunction : D.Ee ⊣ D.Je := D.adjE.ofNatIsoLeft N.qE

/-- The specified Phi, literally the published chosen-compactification transpose at the
canonical closure and conjugated etale adjunction. Source: blueprint Phi formula
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def phi (L : DerivedCategory.Plus
    (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology D.T)
      (ModuleCat.{u + 1} P.Coefficient)))
    (z : D.Ep.obj (D.CS.obj L.obj) ⟶ K) :=
  boundedSiteTranspose P.Coefficient D.closure D.Je N.closureAdjunction L K z

end RelativeTransposeIdentifications

namespace RelativeTransposeGeometry
variable {P : WeilConjectures.PurityFiniteSetting.{u}} (D : RelativeTransposeGeometry P)

/-- The already defined exceptional composite in the conjugated J_e coordinates.
Source: blueprint G_s = C_S s-times U_T
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev G := (comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) D.T).rightDerivedFunctor ⋙
  D.Je ⋙ D.CS

/-- The map rho is comparison applied to J_e of the actual comparison unit.
Source: blueprint rho_M; Stacks 099V
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def rho (M : Etale.DerivedCategoryModule P.Coefficient D.T) :
    D.CS.obj (D.Je.obj M) ⟶ D.G.obj (D.CT.obj M) :=
  boundedSiteRho P.Coefficient D.Je M

end RelativeTransposeGeometry

/-- The precise target domain: bounded constructible M with J_e M bounded below.
This is just the hypotheses on M in the node, not a new constructibility notion.
Source: blueprint locally closed comparison, third paragraph
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
structure RelativeTransposeTarget {P : WeilConjectures.PurityFiniteSetting.{u}}
    (D : RelativeTransposeGeometry P) where
  obj : Etale.DerivedCategoryModule P.Coefficient D.T
  constructible : Etale.DerivedCategory.isBoundedConstructible P.Coefficient D.T obj
  right_plus : _root_.DerivedCategory.TStructure.t.plus (D.Je.obj obj)

/-- The supplied natural gamma and its specified pasted-counit normalization.
Source: blueprint locally closed normalization, gamma_M and its displayed counit equation
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
structure RelativeTransposeGamma {P : WeilConjectures.PurityFiniteSetting.{u}}
    (D : RelativeTransposeGeometry P) where
  iso : ∀ M : RelativeTransposeTarget D, D.CS.obj (D.Je.obj M.obj) ≅ D.Jp.obj (D.CT.obj M.obj)
  naturality : ∀ (M M' : RelativeTransposeTarget D) (b : M.obj ⟶ M'.obj),
    D.CS.map (D.Je.map b) ≫ (iso M').hom = (iso M).hom ≫ D.Jp.map (D.CT.map b)
  counit : ∀ M : RelativeTransposeTarget D,
    (D.delta ⟨D.Je.obj M.obj, M.right_plus⟩).hom ≫
      D.Fp.map (iso M).hom ≫ D.adjP.counit.app (D.CT.obj M.obj) =
        D.CT.map (D.adjE.counit.app M.obj)

namespace RelativeTransposeGamma
variable {P : WeilConjectures.PurityFiniteSetting.{u}} {D : RelativeTransposeGeometry P}
  (γ : RelativeTransposeGamma D)

/-- The specified comparison theta, with the order gamma inverse then rho.
Source: blueprint theta_M = rho_M gamma_M inverse
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def theta (M : RelativeTransposeTarget D) :
    D.Jp.obj (D.CT.obj M.obj) ⟶ D.G.obj (D.CT.obj M.obj) :=
  (γ.iso M).inv ≫ D.rho M.obj

end RelativeTransposeGamma


/-- Transport of the actual chosen-closure Hom function along a retained etale witness.
The inverse of alpha changes the source back to K. Source: blueprint witness clause
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def relativeTransposeWitnessPhi {P : WeilConjectures.PurityFiniteSetting.{u}}
    {D : RelativeTransposeGeometry P} (N : RelativeTransposeIdentifications D)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology D.S)
      (ModuleCat.{u + 1} P.Coefficient)))
    (L : DerivedCategory.Plus
      (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (α : D.CS.obj L.obj ≅ K) (M : RelativeTransposeTarget D)
    (h : D.Ep.obj K ⟶ D.CT.obj M.obj) : K ⟶ D.G.obj (D.CT.obj M.obj) :=
  α.inv ≫ N.phi L (D.CT.obj M.obj) (D.Ep.map α.hom ≫ h)

/-- The complete relative transpose normalization on the stated comparison class.
Source: blueprint main-20261015, lem-weil-finite-duality-site-comparison.proof.md,
second paragraph; Stacks Tags 0037, 0B65 and 099V
(blueprint: lem-sf-locally-closed-relative-transpose-normalization).

Proof plan, following the node's eight steps:
1. A closed immersion is finite, so etale closed direct image is exact
(lemma-weil-pbc-finite-direct-image-exact). Open extension is exact
(lem-weil-pbc-extension-by-zero-exact). Hence F_e L and E_e L are bounded below.
The named closed mate and open comparison make Delta and B natural isomorphisms
(lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-cbc-proetale-extension-zero-comparison). Pro-etale closed exactness follows from
lem-sfb-locally-closed-extension-coherence, with identity open factor.
2. Full faithfulness of comparison on bounded-below objects
(thm-weil-pbc-site-comparison) gives the unique h_0 with Delta_L followed by h equal
to C_T(h_0). Invertibility of Delta recovers h from h_0.
3. Write g_0 = adj_e(h_0). The inverse adjunction formula writes h_0 as F_e(g_0)
followed by the etale counit. Naturality of Delta at g_0 and the assumed gamma
counit equation show that the inverse ambient transpose of C_S(g_0) followed by
gamma is h, after cancelling Delta. This proves the ambient formula.
4. Put z = q_p inverse followed by h and a = q_e inverse followed by h_0.
The assumed q/Delta/B square gives B followed by z = C_T(a). Conjugation by q_e
(def-weil-pbc-adjunction-conjugate) identifies the closure transpose of a with g_0.
5. Expand the specified boundedSiteTranspose (lem-pur-bounded-site-adjunction-transpose).
Naturality of eta identifies the comparison transpose of C_T(a) with a followed
by eta_M. Naturality of the etale adjunction then gives C_S(g_0) followed by rho.
The comparison unit is invertible on bounded-below M, so rho is invertible.
6. Theta is gamma inverse followed by rho. The two formulas identify the actual
Hom functions and their inverses. Evaluating them on identities identifies every
unit and counit for which the objects are in the indicated domains. In particular
the gamma witness of J_p C_T M supplies its defined counit comparison.
7. Transport by an arbitrary alpha : C_S L isomorphic to K. Two witnesses differ
by a uniquely lifted etale isomorphism, by full faithfulness. Naturality in L
identifies the transported functions, giving witness independence and the specified
comparison-class Hom bijection (thm-sf-ambient-adjoint-class). Naturality in M uses
the assumed naturality of gamma and the naturality of eta.
8. For a compatible normalized factorization change, its left comparison transports
h and h_0 by inverse precomposition. Adjunction conjugation transports their
transposes. Uniqueness of normalized extension comparisons identifies the two q
maps (lem-sfb-etale-locally-closed-extension-comparison and
lem-sfb-locally-closed-extension-coherence). Cancelling B and comparison faithfulness
gives the etale q square. Thus the closure arrow and its Phi do not change; the
conjugate right comparison identifies the two theta maps. Identity and composition
follow from these same equalities. This last assertion is stated separately below.
-/
theorem locallyClosedRelativeTransposeNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (D : RelativeTransposeGeometry P)
    (N : RelativeTransposeIdentifications D) (γ : RelativeTransposeGamma D)
    (M : RelativeTransposeTarget D) :
    IsIso (D.rho M.obj) ∧ IsIso (γ.theta M) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      ∃! h₀ : D.Fe.obj L.obj ⟶ M.obj, (D.delta L).hom ≫ h = D.CT.map h₀) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj)
      (h₀ : D.Fe.obj L.obj ⟶ M.obj), (D.delta L).hom ≫ h = D.CT.map h₀ →
      D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj M.obj) h =
          D.CS.map (D.adjE.homEquiv L.obj M.obj h₀) ≫ (γ.iso M).hom ∧
        N.phi L (D.CT.obj M.obj) (N.qP.inv.app (D.CS.obj L.obj) ≫ h) =
          D.CS.map (D.adjE.homEquiv L.obj M.obj h₀) ≫ D.rho M.obj) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      N.phi L (D.CT.obj M.obj) z =
        D.CS.map (N.closureAdjunction.homEquiv L.obj _
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) D.T).unit.app
              (D.Ee.obj L.obj) ≫
            ((comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) D.T).rightDerivedFunctor).map
              ((D.B L).hom ≫ z)))) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj M.obj) h ≫ γ.theta M =
        N.phi L (D.CT.obj M.obj) (N.qP.inv.app (D.CS.obj L.obj) ≫ h)) ∧
    (∀ L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      Function.Bijective (N.phi L (D.CT.obj M.obj))) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (g : D.CS.obj L.obj ⟶ D.Jp.obj (D.CT.obj M.obj)),
      N.phi L (D.CT.obj M.obj)
          (N.qP.inv.app (D.CS.obj L.obj) ≫
            (D.adjP.homEquiv (D.CS.obj L.obj) (D.CT.obj M.obj)).symm g) =
        g ≫ γ.theta M) ∧
    (∀ (K : DerivedCategory (Sheaf (Scheme.ProEt.topology D.S)
        (ModuleCat.{u + 1} P.Coefficient)))
      (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (α : D.CS.obj L.obj ≅ K) (h : D.Fp.obj K ⟶ D.CT.obj M.obj),
      relativeTransposeWitnessPhi N K L α M (N.qP.inv.app K ≫ h) =
        D.adjP.homEquiv K (D.CT.obj M.obj) h ≫ γ.theta M) ∧
    (∀ (K : DerivedCategory (Sheaf (Scheme.ProEt.topology D.S)
        (ModuleCat.{u + 1} P.Coefficient)))
      (L L' : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (α : D.CS.obj L.obj ≅ K) (β : D.CS.obj L'.obj ≅ K)
      (h : D.Ep.obj K ⟶ D.CT.obj M.obj),
      relativeTransposeWitnessPhi N K L α M h = relativeTransposeWitnessPhi N K L' β M h) ∧
    (∀ (L L' : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (b : L'.obj ⟶ L.obj) (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      N.phi L' (D.CT.obj M.obj) (D.Ep.map (D.CS.map b) ≫ z) =
        D.CS.map b ≫ N.phi L (D.CT.obj M.obj) z) ∧
    (∀ (M' : RelativeTransposeTarget D) (b : M.obj ⟶ M'.obj),
      D.Jp.map (D.CT.map b) ≫ γ.theta M' = γ.theta M ≫ D.G.map (D.CT.map b)) ∧
    (∀ (M' : RelativeTransposeTarget D) (b : M.obj ⟶ M'.obj)
      (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (z : D.Ep.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      N.phi L (D.CT.obj M'.obj) (z ≫ D.CT.map b) =
        N.phi L (D.CT.obj M.obj) z ≫ D.G.map (D.CT.map b)) ∧
    (relativeTransposeWitnessPhi N (D.Jp.obj (D.CT.obj M.obj))
      ⟨D.Je.obj M.obj, M.right_plus⟩ (γ.iso M) M
      (N.qP.inv.app (D.Jp.obj (D.CT.obj M.obj)) ≫ D.adjP.counit.app (D.CT.obj M.obj)) =
        γ.theta M) ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (e : D.Fp.obj (D.CS.obj L.obj) ≅ D.CT.obj M.obj),
      D.adjP.unit.app (D.CS.obj L.obj) ≫ D.Jp.map e.hom ≫ γ.theta M =
        N.phi L (D.CT.obj M.obj) (N.qP.inv.app (D.CS.obj L.obj) ≫ e.hom)) := by
  sorry


/-- A second actual factorization of the same immersion, with normalized sheaf comparisons
to the same scheme-theoretic closure. The comparison square is precisely the stipulated
compatibility with Delta. Source: blueprint final factorization-naturality clause
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
structure RelativeTransposeRefactor {P : WeilConjectures.PurityFiniteSetting.{u}}
    {D : RelativeTransposeGeometry P} (N : RelativeTransposeIdentifications D) where
  V : Scheme.{u}
  c : D.S ⟶ V
  v : V ⟶ D.T
  [closed : IsClosedImmersion c]
  [opened : IsOpenImmersion v]
  fac : c ≫ v = D.s
  etale : Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) c ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) v ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.s.toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) D.s.imageι
  etale_normalized :
    Functor.isoWhiskerRight etale (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) D.s) ≪≫
      etaleLocallyClosedExtensionRestrictionIso (A := P.Coefficient) D.s inferInstance =
        etaleFactorizationRestrictionIso (A := P.Coefficient) D.s c v fac
  proetale : lowerStar (ModuleCat.{u + 1} P.Coefficient) c ⋙
    openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) v ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) D.s.toImage ⋙
        lowerStar (ModuleCat.{u + 1} P.Coefficient) D.s.imageι
  proetale_normalized :
    Functor.isoWhiskerRight proetale (upperStar (ModuleCat.{u + 1} P.Coefficient) D.s) ≪≫
      relativeTransposeProEtaleClosureRestriction P.Coefficient D.s =
        relativeTransposeProEtaleFactorRestriction P.Coefficient D.s c v fac

attribute [instance] RelativeTransposeRefactor.closed RelativeTransposeRefactor.opened

namespace RelativeTransposeRefactor
variable {P : WeilConjectures.PurityFiniteSetting.{u}} {D : RelativeTransposeGeometry P}
  {N : RelativeTransposeIdentifications D} (R : RelativeTransposeRefactor N)

/-- The open ambient scheme in a second factorization is Noetherian.
Source: Stacks 01T6; blueprint factorization domain check
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
instance noetherianV : IsNoetherian R.V where
  toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion R.v
  toCompactSpace :=
    letI : TopologicalSpace.NoetherianSpace R.V := R.v.isOpenEmbedding.isInducing.noetherianSpace
    inferInstance

/-- The new q_e to the fixed closure. Source: blueprint normalized factorization change
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def qE := relativeTransposeEtaleQ P.Coefficient D.s R.c R.v R.etale

/-- The new q_p to the fixed closure. Source: blueprint normalized factorization change
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def qP := relativeTransposeProEtaleQ P.Coefficient D.s R.c R.v R.proetale

/-- The pro-etale right adjoint in the new closed-then-open factorization.
Source: Stacks 09BM; blueprint factorization naturality
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
abbrev Jp :=
  (upperStar (ModuleCat.{u + 1} P.Coefficient) R.v).mapDerivedCategory ⋙
    (closedUpperShriek (ModuleCat.{u + 1} P.Coefficient) R.c
      (relativeTransposeComplement R.c).ι).rightDerivedFunctor

/-- The new ordinary pasted pro-etale adjunction. Source: blueprint factorization change
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def adjP : relativeTransposeProEtaleForward P.Coefficient R.c R.v ⊣ R.Jp :=
  relativeTransposeProEtaleAdjunction P.Coefficient R.c R.v
    (relativeTransposeComplement R.c).ι
    (by rw [Scheme.Opens.range_ι]; exact isCompl_compl)

/-- The conjugate right-adjoint comparison t, with the direction fixed by inverse r_p.
Source: Stacks 0B65; blueprint final factorization clause
(blueprint: lem-sf-locally-closed-relative-transpose-normalization). -/
def rightComparison : D.Jp ≅ R.Jp :=
  conjugateIsoEquiv D.adjP R.adjP (R.qP ≪≫ N.qP.symm)

end RelativeTransposeRefactor

/-- Normalization is coherent under every identity-normalized change of actual
closed-then-open factorization commuting with Delta. The etale right adjoint is kept
in the fixed closure coordinates by conjugation, exactly as in the node.
Source: blueprint locally closed relative transpose normalization, final sentence;
Stacks Tag 0B65 (blueprint: lem-sf-locally-closed-relative-transpose-normalization).

Proof: apply steps 2--5 of locallyClosedRelativeTransposeNormalization to the new
factorization. Compatibility of r with Delta identifies the etale lifts by inverse
precomposition. The conjugate counit square shows that the new ambient transpose
is the old one followed by t. Apply this to the normalized counit at C_S J_e M:
its transpose is gamma, so the new gamma is gamma followed by t. The normalized
closure comparisons give q'_p r_p = q_p and, by the Delta squares, cancellation
of B and faithfulness of C_T give q'_e r_e = q_e. Thus the two closure arrows are
equal and have the same Phi. Composing gamma inverse with rho gives theta' t =
theta. Identity and composition follow by cancellation of the intermediate q and
the conjugate-composition law; these require no arbitrary pro-etale adjunction.
-/
theorem locallyClosedRelativeTransposeNormalization_refactor
    (P : WeilConjectures.PurityFiniteSetting.{u}) (D : RelativeTransposeGeometry P)
    (N : RelativeTransposeIdentifications D) (γ : RelativeTransposeGamma D)
    (R : RelativeTransposeRefactor N)
    (compatible : ∀ L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
      (D.delta L).hom ≫ (N.qP ≪≫ R.qP.symm).hom.app (D.CS.obj L.obj) =
        D.CT.map ((N.qE ≪≫ R.qE.symm).hom.app L.obj) ≫
          (relativeTransposeDelta P.Coefficient R.c R.v L).hom)
    (M : RelativeTransposeTarget D)
    (γ' : D.CS.obj (D.Je.obj M.obj) ≅ R.Jp.obj (D.CT.obj M.obj))
    (normalized :
      (relativeTransposeDelta P.Coefficient R.c R.v
        ⟨D.Je.obj M.obj, M.right_plus⟩).hom ≫
        (relativeTransposeProEtaleForward P.Coefficient R.c R.v).map γ'.hom ≫
          R.adjP.counit.app (D.CT.obj M.obj) =
        D.CT.map ((N.closureAdjunction.ofNatIsoLeft R.qE.symm).counit.app M.obj)) :
    (γ.iso M).hom ≫ R.rightComparison.hom.app (D.CT.obj M.obj) = γ'.hom ∧
    R.rightComparison.hom.app (D.CT.obj M.obj) ≫ γ'.inv ≫ D.rho M.obj = γ.theta M ∧
    (∀ (L : DerivedCategory.Plus
        (Sheaf D.S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (h : D.Fp.obj (D.CS.obj L.obj) ⟶ D.CT.obj M.obj),
      R.qP.inv.app (D.CS.obj L.obj) ≫
          (N.qP ≪≫ R.qP.symm).inv.app (D.CS.obj L.obj) ≫ h =
        N.qP.inv.app (D.CS.obj L.obj) ≫ h) ∧
    (conjugateIsoEquiv D.adjP D.adjP (Iso.refl D.Fp) = Iso.refl D.Jp) ∧
    (∀ R' : RelativeTransposeRefactor N,
      R.rightComparison ≪≫
        conjugateIsoEquiv R.adjP R'.adjP (R'.qP ≪≫ R.qP.symm) = R'.rightComparison) := by
  sorry

end AlgebraicGeometry.ProEtale
