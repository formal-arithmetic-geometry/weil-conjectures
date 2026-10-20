/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Paper.PbcCompletedPullbackActual
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

/-!
# Exceptional restriction of a Verdier dual

Source: the current Weil conjectures blueprint, six-functors basics,
`sk-prop-sf-biduality-general/lem-weil-closed-costalk-duality.md`
(blueprint: lem-weil-closed-costalk-duality).

The two statements cover the small etale and small pro-etale sites. A termwise
localization comparison specifies each derived functor, rather than allowing an
unrelated functor. The duals are the recorded derived internal Hom construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Modules over arbitrary commutative etale coefficients, without boundedness.
Source: Stacks, Modules on Sites, Tag 03D1
(blueprint: lem-weil-closed-costalk-duality). -/
abbrev closedCostalkEtaleModules (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1} ((sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

/-- The standard ordinary unbounded localization on the small etale site.
Source: Stacks, Tag 05RU (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModules_hasDerivedCategory (X : Scheme.{u})
    (R : Sheaf X.smallEtaleTopology CommRingCat.{u + 1}) :
    HasDerivedCategory (closedCostalkEtaleModules X R) :=
  HasDerivedCategory.standard _

/-- Ring inverse image, by left Kan extension and sheafification on the actual etale sites.
Source: Stacks, Tags 00VC and 00WX (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology CommRingCat.{u + 1} :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The canonical ring-sheaf adjunction determining the coefficient unit.
Source: Stacks, Tag 00YV (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    closedCostalkEtaleRingPullback f ⊣
      (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) CommRingCat.{u + 1}
    (Y.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- Actual closed direct image with scalars restricted through the inverse-image unit.
Source: Stacks, Modules on Sites, Tag 03D6
(blueprint: lem-weil-closed-costalk-duality). -/
noncomputable def closedCostalkEtaleModulePush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    closedCostalkEtaleModules X ((closedCostalkEtaleRingPullback f).obj R) ⥤
      closedCostalkEtaleModules Y R :=
  SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.pullback @Etale ⊤ f)
    (J := Y.smallGrothendieckTopology @Etale) (K := X.smallGrothendieckTopology @Etale)
    (S := (sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (R := (sheafCompose X.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((closedCostalkEtaleRingPullback f).obj R))
    ⟨Functor.whiskerRight ((closedCostalkEtaleRingAdjunction f).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Closed direct image is additive since its linear components are unchanged.
Source: Stacks, Tag 03D6 (blueprint: lem-weil-closed-costalk-duality). -/
noncomputable instance closedCostalkEtaleModulePush_additive {X Y : Scheme.{u}}
    (f : X ⟶ Y) (R : Sheaf Y.smallEtaleTopology CommRingCat.{u + 1}) :
    (closedCostalkEtaleModulePush f R).Additive where
  map_add := by intros; rfl

/-- Exceptional restriction of derived internal Hom, on the small etale site.
The underived inverse image is specified by its adjunction to the actual module
pushforward; the two factorization isomorphisms specify termwise descent through Q.
Thus all presentations of the source's exact inverse image and closed direct image
are allowed, and their derived functors are determined up to unique isomorphism.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 04CA, 07A4, 08J9 and 08JA (blueprint: lem-weil-closed-costalk-duality).

Proof:
1. Closed pushforward is exact and fully faithful, with invertible inverse-image
counit, by lem-kun-04ca and the closed geometric-stalk formula. Geometric stalks
are exact and conservative. Its composite with complementary open restriction is zero.
2. Exact inverse image and closed direct image descend termwise. Pullback commutes
with derived tensor (lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
3. The projection morphism i_*N tensor K -> i_*(N tensor i^*K), adjoint to
pullback-tensor comparison followed by the closed counit, is invertible: its
closed restriction is invertible and its open restriction is a map of zero objects.
Apply both restrictions to its cone; joint detection makes the cone zero.
4. Currying and derived global Hom (lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections) give Hom(P,RHom(Q,L)) = Hom(P tensor Q,L).
5. For every N, apply the exceptional adjunction, tensor-Hom, the inverse projection
identity, the exceptional adjunction again, and tensor-Hom. This identifies
Hom(N,Ri! RHom(K,omega)) with Hom(N,RHom(i^*K,Ri!omega)).
6. These bijections are natural in N and K. Their values on identities and their
inverse values on identities give mutually inverse Yoneda maps, natural in K.
All arrows are induced by adjunction and evaluation, as in the source. -/
theorem exceptionalRestrictionVerdierDuality_etale
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf T.smallEtaleTopology CommRingCat.{u + 1})
    (iStar : closedCostalkEtaleModules T R ⥤
      closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R))
    [iStar.Additive] (_ai : iStar ⊣ closedCostalkEtaleModulePush i R)
    (iPull : DerivedCategory (closedCostalkEtaleModules T R) ⥤
      DerivedCategory (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_pullFactors : DerivedCategory.Q ⋙ iPull ≅
      iStar.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (iPush : DerivedCategory
        (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)) ⥤
      DerivedCategory (closedCostalkEtaleModules T R))
    (_pushFactors : DerivedCategory.Q ⋙ iPush ≅
      (closedCostalkEtaleModulePush i R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (riExcl : DerivedCategory (closedCostalkEtaleModules T R) ⥤ DerivedCategory
      (closedCostalkEtaleModules Z ((closedCostalkEtaleRingPullback i).obj R)))
    (_adj : iPush ⊣ riExcl) (ωT : DerivedCategory (closedCostalkEtaleModules T R)) :
    let ΛU := (closedCostalkEtaleRingPullback j).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (closedCostalkEtaleModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} T.smallEtaleTopology R) ⋙ riExcl ≅
      iPull.op ⋙ ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} Z.smallEtaleTopology
          ((closedCostalkEtaleRingPullback i).obj R)) := by
  sorry

/-- Exceptional restriction of a Verdier dual, on the small pro-etale site.
Here the open complement is quasi-compact, as required for the ringed recollement.
The coefficient ring on Z is exactly the actual inverse image of R; its identification
in the recorded ringed derived operations is the identity. The dualizing object on Z
is Ri!omegaT itself, and both duals are the recorded K-injective internal Hom.

Source: current blueprint, six-functors basics, closed-costalk-duality;
Stacks, Tags 09AA, 09BM, 09AH, 07A4, 08J9 and 08JA
(blueprint: lem-weil-closed-costalk-duality).

Proof: follow the six steps in exceptionalRestrictionVerdierDuality_etale, replacing
geometric-stalk detection in step 1 by lem-weil-pbc-proetale-ringed-open-closed.
Its quasi-compact-complement hypothesis is supplied by j. The closed counit and the
open-closed exact sequence give joint detection, so the projection map is invertible
on arbitrary unbounded complexes. The ringed tensor-Hom and global-Hom comparisons
and the assumed ambient exceptional adjunction give the same natural Hom chain.
Yoneda gives the natural isomorphism, without a biduality or Tor bound. -/
theorem exceptionalRestrictionVerdierDuality
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (riExcl : DerivedCategory (proEtaleRingModules T R) ⥤ DerivedCategory
      (proEtaleRingModules Z ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)))
    (_adj : proEtaleRingDerivedDirectImage i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _) ⊣ riExcl)
    (ωT : DerivedCategory (proEtaleRingModules T R)) :
    let ΛU := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
    Nonempty
      ((((𝟭 (DerivedCategory (proEtaleRingModules T R))ᵒᵖ).prod'
          ((Functor.const _).obj ωT)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology T) R) ⋙ riExcl ≅
      (proEtaleRingDerivedPullback i R
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).op ⋙
      ((𝟭 _).prod' ((Functor.const _).obj (riExcl.obj ωT))) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, 0, u + 2} (ProEt.topology Z)
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) := by
  sorry

end AlgebraicGeometry.Scheme
