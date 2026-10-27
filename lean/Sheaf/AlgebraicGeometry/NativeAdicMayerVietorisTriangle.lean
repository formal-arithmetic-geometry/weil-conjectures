module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Mayer-Vietoris for native adic direct images

Source: `WeilConjectures/SixFunctors/ProEtale/Adic/LowerStar.lean`,
`finiteLowerStar_of_openCover`, and Stacks Project Tag 08BV
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle).

The coefficient field is the fixed algebraic closure `PadicAlgCl l` with its extended
absolute-value topology. `AdicSheaf` is the native module category over locally finite
continuous functions, with the ordinary direct image and its total unbounded right derived
functor. The arrows below are derived from the ordinary open adjunction units.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry.ProEtale

/-- The restriction arrow after derived direct image, induced by the open adjunction unit
and the canonical composition of ordinary direct images.
Source: `LowerStar.lean`, `finiteLowerStar_of_openCover`, and Stacks Tag 08BV
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle). -/
noncomputable def adicDerivedOpenRestriction
    (l : ℕ) [Fact l.Prime] {X Y U : Scheme.{u}} (f : X ⟶ Y)
    (j : U ⟶ X) [IsOpenImmersion j] (C : DerivedCategory (AdicSheaf l X)) :
    (adicLowerStar l f).rightDerivedFunctor.obj C ⟶
      (adicLowerStar l (j ≫ f)).rightDerivedFunctor.obj
        ((adicUpperStar l j).mapDerivedCategory.obj C) :=
  (Functor.rightDerivedPullback (adicUpperStar l j)
    (Functor.whiskerRight (adicUpperStarLowerStarAdjunction l j).unit (adicLowerStar l f) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (adicUpperStar l j) (adicLowerStarComp l j f).hom)).app C

/-- Canonical identification of the two iterated restrictions to an overlap.
Source: `Module.lean`, `adicUpperStarCompIso`; restriction is termwise exact
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle). -/
noncomputable def adicDerivedOverlapIso
    (l : ℕ) [Fact l.Prime] {X U V W : Scheme.{u}}
    (jU : U ⟶ X) (jV : V ⟶ X) (pU : W ⟶ U) (pV : W ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    [IsOpenImmersion pU] [IsOpenImmersion pV] (h : pU ≫ jU = pV ≫ jV)
    (C : DerivedCategory (AdicSheaf l X)) :
    (adicUpperStar l pV).mapDerivedCategory.obj
        ((adicUpperStar l jV).mapDerivedCategory.obj C) ≅
      (adicUpperStar l pU).mapDerivedCategory.obj
        ((adicUpperStar l jU).mapDerivedCategory.obj C) :=
  ((Functor.mapDerivedCategoryCompIso (adicUpperStar l jV) (adicUpperStar l pV)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso (adicUpperStar l jU) (adicUpperStar l pU)).app C

/-- The first Mayer-Vietoris arrow is the pair of canonical restrictions.
Source: Stacks Tag 08BV, diagonal restriction map
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle). -/
noncomputable def adicMayerVietorisFirst
    (l : ℕ) [Fact l.Prime] {X Y U V : Scheme.{u}} (f : X ⟶ Y)
    (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]
    (C : DerivedCategory (AdicSheaf l X)) :=
  biprod.lift (adicDerivedOpenRestriction l f jU C) (adicDerivedOpenRestriction l f jV C)

/-- The second Mayer-Vietoris arrow is restriction from U minus restriction from V.
Both targets are identified by the canonical pullback and composition isomorphisms.
Source: Stacks Tag 08BV, difference of restrictions
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle). -/
noncomputable def adicMayerVietorisSecond
    (l : ℕ) [Fact l.Prime] {X Y U V W : Scheme.{u}} (f : X ⟶ Y)
    (jU : U ⟶ X) (jV : V ⟶ X) (pU : W ⟶ U) (pV : W ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    [IsOpenImmersion pU] [IsOpenImmersion pV] (h : pU ≫ jU = pV ≫ jV)
    (C : DerivedCategory (AdicSheaf l X)) :=
  biprod.desc
    (adicDerivedOpenRestriction l (jU ≫ f) pU
      ((adicUpperStar l jU).mapDerivedCategory.obj C))
    (-(adicDerivedOpenRestriction l (jV ≫ f) pV
      ((adicUpperStar l jV).mapDerivedCategory.obj C) ≫
      (Functor.rightDerivedFunctorNatIso (adicLowerStarCongr l
        (by simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ f) h.symm))).hom.app _ ≫
      (adicLowerStar l (pU ≫ jU ≫ f)).rightDerivedFunctor.map
        (adicDerivedOverlapIso l jU jV pU pV h C).hom))

/-- The canonical native adic Mayer-Vietoris arrows extend to a distinguished triangle,
for any two-open cover and any unbounded complex, with no finiteness assumptions.

Source: `LowerStar.lean`, `finiteLowerStar_of_openCover`, lines 175-243;
Stacks Project Tags 08BV, 079P, 08FI, 093X, 070Y and 0152
(blueprint: lem-sf-native-adic-mayer-vietoris-triangle).

Proof:
1. Identify each open pro-etale site with the corresponding localized site
   (lem-weil-proetale-weakly-etale-localization). The coefficient functions and their
   restrictions are identical, so B restricts to the same native coefficient sheaf.
   Restriction is exact (lem-sfb-ringed-site-restriction-kflat).
2. The ordinary adjunction unit is restriction on sections; nested restrictions agree
   by precomposition (def-pur-localized-ringed-site). The definitions above derive
   precisely those units, including the composition comparison of direct images.
3. Choose a K-injective representative I with injective terms
   (prop-pur-kinjective-resolutions-exist). Its three restrictions remain K-injective
   (lem-pur-kinjective-restrict-localized), with no boundedness assumption.
4. On every pro-etale test object over Y, its base change to X is covered by the
   base changes to U and V. Weak etaleness and open immersions are stable under base
   change (lem-weil-pbc-weakly-etale-composition-base-change and
   lem-weil-pbc-open-immersion-base-change). The sheaf axiom gives exactness at the
   first two terms of the sectionwise sequence for I in each degree. Restriction of
   an injective along the overlap monomorphism is surjective
   (lem-pur-ringed-site-injective-mono-restriction), giving exactness at the last term.
5. Thus the ordinary direct images form a degreewise short exact sequence. Compute
   the four derived direct images on the K-injective representatives
   (lem-weil-pbc-kinjective-total-derived and def-sfb-right-derived-functor).
6. Open direct image preserves K-injectives by its exact left adjoint
   (lem-weil-pbc-right-adjoint-preserves-kinjective). The K-injective Hom bijection
   (lem-weil-pbc-kinjective-hom-derived) identifies the derived units with the ordinary
   restriction maps. The overlap comparison identifies the nested restrictions.
7. The difference map is literally U restriction minus V restriction, with zero
   composite with the first map. Apply lem-weil-pbc-complex-ses-triangle and transport
   its distinguished triangle by the canonical K-injective computation isomorphisms.
-/
theorem nativeAdic_mayerVietoris_triangle
    (l : ℕ) [Fact l.Prime] {X Y U V W : Scheme.{u}} (f : X ⟶ Y)
    (jU : U ⟶ X) (jV : V ⟶ X) (pU : W ⟶ U) (pV : W ⟶ V)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    [IsOpenImmersion pU] [IsOpenImmersion pV]
    (_hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base)
    (hsq : IsPullback pU pV jU jV) (C : DerivedCategory (AdicSheaf l X)) :
    ∃ δ : (adicLowerStar l (pU ≫ jU ≫ f)).rightDerivedFunctor.obj
        ((adicUpperStar l pU).mapDerivedCategory.obj
          ((adicUpperStar l jU).mapDerivedCategory.obj C)) ⟶
        ((adicLowerStar l f).rightDerivedFunctor.obj C)⟦(1 : ℤ)⟧,
      Triangle.mk (adicMayerVietorisFirst l f jU jV C)
        (adicMayerVietorisSecond l f jU jV pU pV hsq.w C) δ ∈
          distTriang (DerivedCategory (AdicSheaf l Y)) := by
  sorry

end AlgebraicGeometry.ProEtale
