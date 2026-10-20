/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q88 and P1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleIdentifiedSupportedReconstruction
import Sheaf.AlgebraicGeometry.ProEtaleLocallyClosedExtension
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage

/-!
# Normalized locally closed extensions on module sheaves

Source: Stacks Project, proetale.tex, Tags 09AA, 09BM, 09BN and 09AH;
sites-modules.tex, Tags 03DI and 03DJ; schemes.tex, Tag 02V0;
blueprint main-20261015, det-prop-scalar-six-pullback, proof (2)
(blueprint: lem-sfb-locally-closed-extension-coherence).

The structures below package the witnesses in this single coherence assertion.
They do not choose a functor from a mere existence theorem. The only categories and
inverse/direct images used are the published module-sheaf constructions. An open
extension is specified by its adjunction, equivalently by slice extension followed
by module sheafification. Closed extensions are identified with actual direct image.
The derived-category comparison is constructed separately in
`LocallyClosedExtensionCoherence`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A Noetherian scheme with an arbitrary commutative coefficient sheaf; a bundle of
parameters for the coherence assertion, not an additional hypothesis on coefficients.
Source: Stacks, Tags 01OV and 09A5
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedCoefficients where
  scheme : Scheme.{u}
  locallyNoetherian : IsLocallyNoetherian scheme
  compact : CompactSpace scheme
  ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}

attribute [instance] LocallyClosedCoefficients.locallyNoetherian
  LocallyClosedCoefficients.compact

/-- A locally closed immersion with its inverse-image coefficient identification.
Taking the source ring literally to be inverse image is the special case `Iso.refl`;
allowing its identified presentation permits composition without silently equating rings.
Source: Stacks, Tags 01IO and 03D2
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedCoefficientImmersion (S X : LocallyClosedCoefficients.{u}) where
  hom : S.scheme ⟶ X.scheme
  immersion : IsImmersion hom
  coefficient : (proEtaleSheafInverseImage hom CommRingCat.{u + 1}).obj X.ring ≅ S.ring

attribute [instance] LocallyClosedCoefficientImmersion.immersion

namespace LocallyClosedCoefficientImmersion

/-- Identity with the actual identity inverse-image comparison.
Source: Stacks, Tag 09A5 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
def identity (X : LocallyClosedCoefficients.{u}) : LocallyClosedCoefficientImmersion X X where
  hom := 𝟙 X.scheme
  immersion := inferInstance
  coefficient := (proEtaleRingInverseImageId X.scheme).app X.ring

/-- Composition with the actual composition of inverse-image coefficient identifications.
Source: Stacks, Tags 02V0 and 03D8
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def comp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    LocallyClosedCoefficientImmersion T X where
  hom := b.hom ≫ a.hom
  immersion := inferInstance
  coefficient := proEtaleRingCompositeCoefficients b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient

/-- Exact inverse image with the specified inverse-image coefficients.
Source: Stacks, Tag 03D2 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev pull {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient

/-- Actual direct image with action through the coefficient adjunction unit.
Source: Stacks, Tag 03D3 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev push {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleDirectImage a.hom X.ring S.ring a.coefficient

/-- The canonical inverse-image composition, fixed by the sectionwise fibre-product map.
Source: Stacks, Tag 03D8 (blueprint: lem-sfb-locally-closed-extension-coherence). -/
def pullComp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    (a.comp b).pull ≅ a.pull ⋙ b.pull :=
  exchangeModuleComposition b.hom a.hom X.ring S.ring T.ring a.coefficient b.coefficient

end LocallyClosedCoefficientImmersion

/-- Witnesses for the exact module extensions in the assertion. The open adjunction and
closed counit normalize restriction. The coefficients of every arrow are inverse images.
Source: Stacks, Tags 09AA, 09BM, 09BN, 03DI and 03DJ
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure LocallyClosedExtensionData where
  extension : ∀ {S X : LocallyClosedCoefficients.{u}}, LocallyClosedCoefficientImmersion S X →
    proEtaleRingModules S.scheme S.ring ⥤ proEtaleRingModules X.scheme X.ring
  additive : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (extension a).Additive
  finiteLimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteLimits (extension a)
  finiteColimits : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), PreservesFiniteColimits (extension a)
  restriction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), extension a ⋙ a.pull ≅ 𝟭 _
  openAdjunction : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsOpenImmersion a.hom),
    extension a ⊣ a.pull
  openNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsOpenImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (openAdjunction a ha).unit.app M ≫ (restriction a).hom.app M = 𝟙 M
  closedComparison : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (_ : IsClosedImmersion a.hom),
    extension a ≅ a.push
  closedNormalization : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (ha : IsClosedImmersion a.hom)
    (M : proEtaleRingModules S.scheme S.ring),
    (restriction a).hom.app M = a.pull.map ((closedComparison a ha).hom.app M) ≫
      (proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient).counit.app M
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    extension b ⋙ extension a ≅ extension (a.comp b)
  identity : ∀ X : LocallyClosedCoefficients.{u},
    extension (.identity X) ≅ 𝟭 (proEtaleRingModules X.scheme X.ring)

attribute [instance] LocallyClosedExtensionData.additive LocallyClosedExtensionData.finiteLimits
  LocallyClosedExtensionData.finiteColimits

namespace LocallyClosedExtensionData

/-- The actual termwise extension on the ordinary unbounded derived categories.
Source: Stacks, Tags 015F and 05RU
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
abbrev derived (E : LocallyClosedExtensionData.{u}) {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) := (E.extension a).mapDerivedCategory

/-- The specified closed-then-open factorization of extension. Its open factor is the
left adjoint to actual inverse image from `openAdjunction`, hence the sheafified
extension-by-zero presheaf; its closed factor is actual direct image.
Source: Stacks, Tags 03DI, 09AA and 09BN
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def closedOpenFactorization (E : LocallyClosedExtensionData.{u})
    {S V X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (hc : IsClosedImmersion c.hom)
    (_hv : IsOpenImmersion v.hom) :
    E.extension (v.comp c) ≅ c.push ⋙ E.extension v :=
  (E.gamma v c).symm ≪≫ Functor.isoWhiskerRight (E.closedComparison c hc) (E.extension v)

/-- The specified opposite factorization, with open followed by closed. This uses
exactly the same normalized composition comparison, including the mixed case.
Source: Stacks, Tags 02V0 and 09AH
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def openClosedFactorization (E : LocallyClosedExtensionData.{u})
    {S Z X : LocallyClosedCoefficients.{u}} (i : LocallyClosedCoefficientImmersion Z X)
    (j : LocallyClosedCoefficientImmersion S Z) (hi : IsClosedImmersion i.hom)
    (_hj : IsOpenImmersion j.hom) :
    E.extension (i.comp j) ≅ E.extension j ⋙ i.push :=
  (E.gamma i j).symm ≪≫ Functor.isoWhiskerLeft (E.extension j) (E.closedComparison i hi)

/-- Comparison of any two closed-then-open factorizations with the same composite
coefficient identification. In a coherent system its restriction is the identity,
and it is the unique isomorphism with that normalization by `Coherent.homBijection`.
Source: Stacks, Tags 02V0 and 09AH, the intersection-and-shrinking argument
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
def factorizationComparison (E : LocallyClosedExtensionData.{u})
    {S V V' X : LocallyClosedCoefficients.{u}} (v : LocallyClosedCoefficientImmersion V X)
    (c : LocallyClosedCoefficientImmersion S V) (v' : LocallyClosedCoefficientImmersion V' X)
    (c' : LocallyClosedCoefficientImmersion S V')
    (hc : IsClosedImmersion c.hom) (hv : IsOpenImmersion v.hom)
    (hc' : IsClosedImmersion c'.hom) (hv' : IsOpenImmersion v'.hom)
    (h : v.comp c = v'.comp c') :
    c.push ⋙ E.extension v ≅ c'.push ⋙ E.extension v' :=
  (E.closedOpenFactorization v c hc hv).symm ≪≫ eqToIso (congrArg E.extension h) ≪≫
    E.closedOpenFactorization v' c' hc' hv'

/-- Normalized comparison laws on module sheaves. The two factorization orders follow
by composing `gamma` with `closedComparison` and the open adjunction; normalization
and the Hom bijection make the comparison between any two factorizations unique.
Source: Stacks, Tags 02V0 and 09AH, composite consequence described in the node proof
(blueprint: lem-sfb-locally-closed-extension-coherence). -/
structure Coherent (E : LocallyClosedExtensionData.{u}) : Prop where
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.extension a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.extension a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (M N : proEtaleRingModules S.scheme S.ring),
    Function.Bijective (fun f : (E.extension a).obj M ⟶ (E.extension a).obj N ↦
      (E.restriction a).inv.app M ≫ a.pull.map f ≫ (E.restriction a).hom.app N)
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring),
    (a.comp b).pull.map ((E.gamma a b).hom.app M) ≫ (E.restriction (a.comp b)).hom.app M =
      (a.pullComp b).hom.app ((E.extension a).obj ((E.extension b).obj M)) ≫
        b.pull.map ((E.restriction a).hom.app ((E.extension b).obj M)) ≫
          (E.restriction b).hom.app M
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

/-- The normalized composition laws for an exact extension system. Full faithfulness
and the restriction Hom bijection are consequences of the separate open and closed
adjunctions and a closed/open factorization, and are proved in the importing module.

Source: Stacks, Tags 02V0 and 09AH, the shrinking and support-reconstruction argument
(blueprint: lem-sfb-locally-closed-module-extension-coherence). -/
structure NormalizedComposition (E : LocallyClosedExtensionData.{u}) : Prop where
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring),
    (a.comp b).pull.map ((E.gamma a b).hom.app M) ≫ (E.restriction (a.comp b)).hom.app M =
      (a.pullComp b).hom.app ((E.extension a).obj ((E.extension b).obj M)) ≫
        b.pull.map ((E.restriction a).hom.app ((E.extension b).obj M)) ≫
          (E.restriction b).hom.app M
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

end LocallyClosedExtensionData

/-- Exact locally closed extension on module sheaves, with normalized factorization
comparisons and unital, associative composition.

Source: Stacks, proetale.tex Tags 09AA, 09BM, 09BN and 09AH; sites-modules.tex
Tags 03DI and 03DJ; schemes.tex Tag 02V0; blueprint main-20261015,
det-prop-scalar-six-pullback proof (2)
(blueprint: lem-sfb-locally-closed-module-extension-coherence).

Proof, following the module-sheaf steps of the DAG node:
1. Apply proEtaleLocallyClosedExtension to obtain each exact module extension and its
   restriction comparison. Its proof constructs the closed-then-open functor and the
   coefficient transport. For the special open and closed factors use
   proEtaleIdentifiedOpenClosed: it supplies the actual open adjunction with invertible
   unit and the actual closed direct image with invertible specified counit. No
   composite shriek adjunction is asserted.
2. The localization sequence detects zeros and isomorphisms. Two successive Hom
   transpositions, separately for the open and closed adjunctions, prove full faithfulness
   and identify the Hom map with restriction conjugated by its comparison.
3. On open slices closed direct image is evaluation on the same fibre product. Open
   extension restricts to extension on the intersection. The extension-presheaf formula,
   module sheafification and lem-cbc-sieve-slice-sheafification prove these statements,
   compatibly with the closed counit and scalar action.
4. Pure open composition uses unit-normalized uniqueness of left adjoints
   (lem-weil-pbc-conjugate-iso-unit-equation); pure closed composition uses fibre-product
   pasting (lem-weil-pbc-site-morphism-composition).
5. Shrinking an ambient open containing the closed support does not change extension:
   its restriction to the complementary closed subscheme vanishes, so localization
   identifies the open-extension counit with an isomorphism. The actual-coefficient
   counit criterion is supplied by proEtaleIdentifiedOpenClosed.
6. Intersect two ambient opens. Apply shrinking to identify both factorizations with
   the one on the intersection. The Hom bijection proves uniqueness and the cocycle law.
7. For the opposite factorization i u, lift the open in the closed subscheme to an ambient
   open. The localization sequence on the closed subscheme identifies the restriction
   of the closed-then-open extension with u_!. Transpose under i inverse image adjoint
   to i_*; closed and complementary open restrictions detect that this is an isomorphism.
   proEtaleIdentifiedSupportedReconstruction gives the invertible normalized comparison,
   its uniqueness and its naturality, for the actual coefficient identifications.
8. Lift the intermediate open in a composition of two factorizations as in Tag 02V0.
   Interchange the middle closed/open factors by step 7, compose pure factors by step 4,
   and compare with the chosen factorization by step 6. This constructs gamma.
9. After restriction both candidates for any unit or associativity diagram are identities.
   They lie in the same extension image; step 2 makes them equal.
-/
theorem locallyClosedModuleExtensionCoherence :
    ∃ E : LocallyClosedExtensionData.{u}, E.NormalizedComposition := by
  sorry

end AlgebraicGeometry.Scheme
