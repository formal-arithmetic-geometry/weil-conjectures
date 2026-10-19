/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Naturality of the supported Hom identification under base change

Source: literature/stacks-project/etale-cohomology.tex, Tag 0A45,
lemma-cohomology-with-support-triangle;
blueprint sec-smooth-purity/sk-prop-sf-cbc
(blueprint: lem-asd-supported-kummer-support-hom-naturality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Functorial degreewise-injective K-injective replacement, on the specified etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolution (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (CochainComplex.kInjectiveResolutionFunctor _).obj K

/-- Termwise ordinary Hom from the closed constant sheaf. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomComplex (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      (ordinaryFiniteConstant A D)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- The derived Hom object of the recorded closed-support theorem. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomObject (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  ((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      (ordinaryFiniteConstant A D)))).rightDerivedFunctor.obj (DerivedCategory.Q.obj K)

/-- The canonical map from derived Hom to its chosen resolution model. It is the derived
image of the resolution unit followed by the published computation on K-injectives.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomModelMap (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    supportedHomObject A i K ⟶
      DerivedCategory.Q.obj (supportedHomComplex A i (supportedResolution A T K)) :=
  ((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      (ordinaryFiniteConstant A D)))).rightDerivedFunctor.map
        (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution _).app K)) ≫
    (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
      (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
        (ordinaryFiniteConstant A D)))).rightDerivedFunctorObjQIso
          ((CochainComplex.kInjectiveResolutionFunctor _).obj K)).hom

/-- Evaluation at 1 identifies a map from the rank-one constant sheaf with a global section.
Use the constant-sheaf adjunction and the published terminal-section/global-section iso.
Source: Stacks, Tag 095L (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedEvaluateSection (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : ordinaryFiniteConstant A T ⟶ F) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F :=
  (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).inv.app F
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).homEquiv _ _ c) 1)

/-- The inverse image of a complex is taken termwise; exactness makes this derived pullback.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedPullbackComplex (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  ((upperStar (ModuleCat.{u + 1} A) h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- A normalized representative of the recorded `closedSupportHom` comparison. Every map is
fixed: restriction degreewise, Hom-model comparison by the derived resolution unit, kernel
inclusion by its two cone projections, and forgetting support by projection to sections.
The comparison is therefore the kernel-inclusion normalization, with no scalar ambiguity.
Source: Stacks, Tags 095L, 0A45; blueprint lem-amb-closed-support-hom
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomConeModel (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) where
  q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ)
  q_spec : ∀ (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (n : ℤ), (q.app I).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (I.X n)
  modelIso : ∀ K, supportedHomObject A i K ≅
    DerivedCategory.Q.obj (supportedHomComplex A i (supportedResolution A T K))
  modelIso_spec : ∀ K, (modelIso K).hom = supportedHomModelMap A i K
  toSections : ∀ K, supportedHomComplex A i (supportedResolution A T K) ⟶
    ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportedResolution A T K)
  toSections_spec : ∀ K (n : ℤ)
      (c : (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D) ⟶
        (supportedResolution A T K).X n),
    ((toSections K).f n) c = supportedEvaluateSection A T _ (supportedConstantUnit A i ≫ c)
  inclusion : ∀ K, supportedHomComplex A i (supportedResolution A T K) ⟶
    (CochainComplex.mappingCone (q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧
  inclusion_fst : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (supportedResolution A T K)) m n hn =
      (toSections K).f n
  inclusion_snd : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (q.app (supportedResolution A T K)) m = 0
  comparison : ∀ K, supportedHomObject A i K ≅ DerivedCategory.Q.obj
    ((CochainComplex.mappingCone (q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧)
  comparison_spec : ∀ K, (comparison K).hom =
    (modelIso K).hom ≫ DerivedCategory.Q.map (inclusion K)
  comparison_naturality : ∀
      (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (f : K ⟶ L),
    ((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
      (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
        (ordinaryFiniteConstant A D)))).rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (comparison L).hom =
      (comparison K).hom ≫ DerivedCategory.Q.map
        ((shiftFunctor (CochainComplex (ModuleCat.{u + 1} A) ℤ) (-1 : ℤ)).map
          (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm))
  projection : ∀ K,
    (CochainComplex.mappingCone (q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧ ⟶
      ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (supportedResolution A T K)
  projection_spec : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (projection K).f n = (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (supportedResolution A T K)) m n hn

/-- The relative object uses the actual shifted restriction cone. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedRelativeObject (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q.obj
    ((CochainComplex.mappingCone (M.q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧)

/-- The normalized supported-Hom identification on cohomology. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomIdentification (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).obj
      (supportedRelativeObject A M K) ≅
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).obj (supportedHomObject A i K) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).mapIso (M.comparison K).symm

/-- The canonical representative maps for pullback of a closed/open pair. A resolution
comparison must extend the pulled-back resolution unit. Its section maps and Hom map are
specified degreewise; the relative pullback is then the diagonal mapping-cone map.
Source: Stacks, Tag 0A45 and blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedKummerSupportHomData (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T)
    (i' : D' ⟶ T') (hD : D' ⟶ D) (v : V ⟶ T) (v' : V' ⟶ T')
    (sqD : IsPullback hD i' i h) (hV : V' ⟶ V) (sqV : IsPullback hV v' v h) where
  sourceModel : SupportedHomConeModel A i v
  targetModel : SupportedHomConeModel A i' v'
  exchange_isIso : IsIso (supportedConstantExchange A i i' h hD sqD.toCommSq)
  exchangeInverse : (lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D') ⟶
    (upperStar (ModuleCat.{u + 1} A) h).obj
      ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
  exchange_hom_inv : supportedConstantExchange A i i' h hD sqD.toCommSq ≫ exchangeInverse = 𝟙 _
  exchange_inv_hom : exchangeInverse ≫ supportedConstantExchange A i i' h hD sqD.toCommSq = 𝟙 _
  resolutionComparison : ∀ K, supportedPullbackComplex A h (supportedResolution A T K) ⟶
    supportedResolution A T' (supportedPullbackComplex A h K)
  resolutionComparison_spec : ∀ K,
    ((upperStar (ModuleCat.{u + 1} A) h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((CochainComplex.toKInjectiveResolution _).app K) ≫ resolutionComparison K =
      (CochainComplex.toKInjectiveResolution _).app (supportedPullbackComplex A h K)
  sectionsMap : ∀ K,
    ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportedResolution A T K) ⟶
    ((Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (supportedResolution A T' (supportedPullbackComplex A h K))
  sectionsMap_spec : ∀ K (n : ℤ), (sectionsMap K).f n =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h ((supportedResolution A T K).X n) ≫
      (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((resolutionComparison K).f n)
  openSectionsMap : ∀ K,
    ((upperStar (ModuleCat.{u + 1} A) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (supportedResolution A T K) ⟶
    ((upperStar (ModuleCat.{u + 1} A) v' ⋙
      Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (supportedResolution A T' (supportedPullbackComplex A h K))
  openSectionsMap_spec : ∀ K (n : ℤ), (openSectionsMap K).f n =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
      ((upperStar (ModuleCat.{u + 1} A) v).obj ((supportedResolution A T K).X n)) ≫
    (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
      ((upperStarComp (ModuleCat.{u + 1} A) hV v).inv.app _ ≫
        (upperStarComp (ModuleCat.{u + 1} A) v' h (hV ≫ v) sqV.w).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) v').map ((resolutionComparison K).f n))
  restriction_square : ∀ K,
    sectionsMap K ≫ targetModel.q.app
        (supportedResolution A T' (supportedPullbackComplex A h K)) =
      sourceModel.q.app (supportedResolution A T K) ≫ openSectionsMap K
  homMap : ∀ K, supportedHomComplex A i (supportedResolution A T K) ⟶
    supportedHomComplex A i' (supportedResolution A T' (supportedPullbackComplex A h K))
  homMap_spec : ∀ K (n : ℤ)
      (c : (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D) ⟶
        (supportedResolution A T K).X n),
    ((homMap K).f n) c = exchangeInverse ≫
      (upperStar (ModuleCat.{u + 1} A) h).map c ≫ (resolutionComparison K).f n

/-- Actual relative pullback: apply localization and cohomology to the shifted diagonal
cone map, whose two components have specified section formulas. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedRelativePullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    supportedRelativeObject A N.sourceModel K ⟶
      supportedRelativeObject A N.targetModel (supportedPullbackComplex A h K) :=
  DerivedCategory.Q.map ((shiftFunctor (CochainComplex (ModuleCat.{u + 1} A) ℤ) (-1 : ℤ)).map
    (CochainComplex.mappingCone.map _ _ (N.sectionsMap K) (N.openSectionsMap K)
      (N.restriction_square K).symm))

/-- Actual Hom pullback: pull a representative back and precompose with the inverse of
closed exchange, then transport through the specified resolution-model isomorphisms.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomPullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    supportedHomObject A i K ⟶ supportedHomObject A i' (supportedPullbackComplex A h K) :=
  (N.sourceModel.modelIso K).hom ≫ DerivedCategory.Q.map (N.homMap K) ≫
    (N.targetModel.modelIso (supportedPullbackComplex A h K)).inv

/-- The supported-Hom identification intertwines the actual relative pullback and
inverse-image/precomposition map. Forgetting support is the actual cone projection, with
fixed target the global-section complex, and corresponds to precomposition with the unit.
Source: Stacks, Tags 0A45, 095L; blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality).

Proof:
1. Base change preserves the closed immersion (lem-weil-pbc-closed-immersion-base-change).
   On a geometric point in D', the mate defining exchange is the identity on the stalk
   (lemma-openclosed-stalk-upperstar, lemma-openclosed-stalk-lowerstar). Off D', both stalks
   vanish. Conservativity (lemma-weil-pbc-geometric-stalk-conservative) makes exchange
   invertible. The constant comparison is A-linear, and the mate sends the pulled-back
   constant unit to the primed unit (prop-weil-pbc-inverse-image-modules-exact).
2. The etale module categories are Grothendieck abelian
   (lem-weil-pbc-module-sheaves-grothendieck-abelian). Choose the functorial degreewise
   injective K-injective resolutions (lem-pur-kinjective-degreewise-existence). Exact
   inverse image sends the resolution unit to a monomorphic quasi-isomorphism. The
   fibrant lifting property of the target resolution supplies resolutionComparison
   extending that unit. Pullback is not assumed to preserve injectives.
3. Apply Hom into each injective term to 0 → v_! A_V → A_T → i_* A_D → 0
   (lem-weil-pbc-open-closed-short-exact, def-sp-injective-resolutions). The resulting
   short exact sequence C → E → B has C the specified Hom complex, E global sections
   by evaluation at 1, and B sections over V by extension-by-zero adjunction
   (lem-weil-pbc-extension-by-zero-adjunction). Its maps are exactly toSections and q.
4. Restriction preserves K-injectives since it is right adjoint to exact v_!
   (lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-right-adjoint-preserves-kinjective).
   Thus E, B and C compute the derived section and Hom objects
   (lem-weil-pbc-kinjective-total-derived), with the specified modelIso.
5. The inclusion c ↦ (0,k(c)) into Cone(q)[-1] is a quasi-isomorphism. With differential
   (b,s) ↦ (-d_B b-q(s),d_E s), lift -b to t in E to reduce a cocycle to (0,s-d_E t).
   If (0,k(c))=d(b,s), lift b to t; then s+d_E t is in ker q and has differential k(c).
   This is precisely the kernel-inclusion normalization of lem-amb-closed-support-hom.
6. Define sectionsMap by section pullback followed by resolutionComparison; define
   openSectionsMap using the square's composition comparison, and homMap by the displayed
   inverse-exchange/precomposition formula. Restriction commutes with pullback, giving
   restriction_square. Exchange preserves the units, so the square with toSections also
   commutes. The actual diagonal cone map therefore commutes with inclusion.
7. Take H^n, invert the cohomology of the kernel inclusions, and identify cocycles modulo
   homotopy with derived morphisms (lem-weil-pbc-kinjective-hom-derived). This gives the
   displayed pullback equation. Other comparison lifts are homotopic: compatible
   homotopies s_E,s_B give the cone homotopy (b,s) ↦ (-s_B b,s_E s). Thus the formulas
   depend only on the derived coefficient pullback, in every degree and every model.
8. Projection of the shifted cone to E composed with inclusion is toSections. By its
   component formula this is precomposition with A_T → i_* A_D. Apply H^n to obtain
   the displayed forgetting-support equation (def-weil-abstract-derived-category).
-/
theorem supportedKummerSupportHomNaturality (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) [IsClosedImmersion i]
    (i' : D' ⟶ T') (hD : D' ⟶ D) (sqD : IsPullback hD i' i h) [IsClosedImmersion i']
    (v : V ⟶ T) (v' : V' ⟶ T') [IsOpenImmersion v] [IsOpenImmersion v']
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (hcomp' : Set.range v'.base = (Set.range i'.base)ᶜ) :
    ∃ N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV,
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (_hK : ∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (K.X n)) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (supportedRelativePullback A N K) ≫
          (supportedHomIdentification A N.targetModel (supportedPullbackComplex A h K) n).hom =
        (supportedHomIdentification A N.sourceModel K n).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (supportedHomPullback A N K)) ∧
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (DerivedCategory.Q.map (N.sourceModel.projection K)) =
          (supportedHomIdentification A N.sourceModel K n).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
              ((N.sourceModel.modelIso K).hom ≫
                DerivedCategory.Q.map (N.sourceModel.toSections K))) ∧
      (∀ (K : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
            (DerivedCategory.Q.map (N.targetModel.projection K)) =
          (supportedHomIdentification A N.targetModel K n).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).map
              ((N.targetModel.modelIso K).hom ≫
                DerivedCategory.Q.map (N.targetModel.toSections K))) := by
  sorry

end AlgebraicGeometry.Etale
