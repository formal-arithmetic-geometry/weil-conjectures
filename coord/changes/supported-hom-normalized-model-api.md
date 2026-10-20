# AlgebraicGeometry.Etale.SupportedHomConeModel

## Reason

The original concrete model and pullback records repeatedly specialize functorial
K-injective replacement, derived localization and the category of module sheaves in their
fields. The original public interface alone exceeded the 60-second single-file compile
limit. The proof needs the same normalized data, but its construction must elaborate once
at a generic categorical interface before specialization. Local instance priorities select
the canonical preadditive and zero-morphism parents of the given abelian category; these
priorities are not exported.

The original existential `closedSupportHomSequence` does not specify its first map.
Expose the canonical map already constructed in its proof, together with its exactness,
so evaluation at one can normalize the cone inclusion. Expose the already proved cone,
derived-resolution and rank-one-section helpers used by this argument. These changes are
under `Sheaf`, not in the adopted `WeilConjectures` source tree. The two additional modules
were unclaimed when their claim records were checked.

The existing theorem signatures, including the assigned theorem, are unchanged. The old
concrete records become specializations of generic records with the same normalized
data. The elementwise evaluation condition is represented by equality with the canonical
chain map; `supportedHomSectionNormalization_iff` proves equivalence to the original
condition. The pullback data group the two models and their comparison maps in one
record; accessors retain all existing names. The resolution is still the existing
functorial degreewise-injective K-injective resolution, and `supportedHomObject` is still
the existing right derived Hom object. In particular, it is not replaced by an arbitrary
isomorphic object. The specified model map, kernel inclusion, restriction, actual cone
map, inverse-exchange Hom map and forgetting-support target all retain their formulas.
Every intermediate datum is explicitly constructed or obtained from a proved theorem.

Definition changes reopen the statement-meaning check for targets using these definitions;
this delivery claims preservation, not exemption from that independent review. No target
statement or DAG mathematical statement is changed.

The standard resolution is packaged with its proved K-injectivity, mono quasi-isomorphism
unit and lifting property. Its object and unit are still the published construction. The
canonical sequence and the model share `closedSupportHomFunctor`. The unused specialized
`supportedHomModelMap` wrapper is removed; the generic record uses the same canonical
map directly as `Functor.supportedHomResolutionMap`. A repository search found no external
use of the removed wrapper.

The standard sheafification, weak sheafification and global-section properties are named
proofs. `closedSupportEtaleAbelian` exposes the pointwise preadditive parent of the canonical
abelian structure; its equality with the existing instance is proved by reflexivity in
`closedSupportEtaleAbelian_eq`. Local instances use these compact terms consistently in the
support sequence and model. This fixes the same structures and maps and changes no data
choice. The private generic cone constructor now fixes the canonical normalization itself,
avoiding a large specialized reflexivity term.

The linear structure is also named as `closedSupportEtaleLinear`; its equality with the
existing structure, including scalar multiplication on morphisms, is proved by reflexivity.
The zero-composite and exactness accessors of the canonical sequence choose only proofs;
their use does not choose any new map or object. The Hom-complex map is constructed first
for arbitrary linear categories. The private evaluation-square property is formed on the
generic map record, avoiding repeated checks of its native composite's middle object.

The shared Hom source is now the named explicit construction `closedSupportHomSource`.
Its equality theorem gives exactly the original direct image of the rank-one constant
sheaf. The restriction natural transformation is likewise explicitly constructed as
`closedSupportSectionsPullback`, with the original component formula, and is reused by
the existing `closedSupportHom` proof. The normalization family is formed on arbitrary
complexes; specialization to the chosen resolutions occurs in a generic lemma.
`ClosedSupportHom` publicly imports `ClosedSupportHomSequence`, because the latter's
canonical sheaf structures now occur in its public helper signatures.

The generic diagram constructor takes the canonical natural transformation itself and
derives its normalization predicate as equality with the associated chain map. This
replaces an equivalent separately supplied predicate. Both the native diagram and its
constructor now use the identical generic expression, avoiding repeated specialization
of the expanded normalization lambda. The public normalization-equivalence theorem
still gives exactly the original elementwise evaluation formula.

The private Hom-map family is explicitly typed with the public complex functors. Its
inferred type previously forced the same large conversion at every use of the family.
Checking that conversion once in its definition makes the full module fit the existing
single-file compilation limit. Its component formula uses categorical associativity.

## Old

The item interface and the supporting modules, verbatim:

`Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`:

```lean
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
```

`Sheaf.AlgebraicGeometry.ClosedSupportHom`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

import Sheaf.AlgebraicGeometry.ClosedSupportHomSequence
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Closed support as a relative section complex

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md (blueprint: lem-amb-closed-support-hom).
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace CochainComplex
private noncomputable def closedConeLift
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0) :
    S ⟶ (mappingCone f)⟦(-1 : ℤ)⟧ where
  f p := a.f p ≫
    homotopyCofiber.inlX f p (p + (-1)) (ComplexShape.up_mk _ _ (by omega))
  comm' p q hpq := by
    obtain rfl : q = p + 1 := by simpa using hpq.symm
    rw [shiftFunctor_obj_d', Category.assoc]
    change a.f p ≫ homotopyCofiber.inlX f p (p + (-1)) _ ≫
      ((-1 : ℤ).negOnePow • (mappingCone f).d (p + (-1)) (p + 1 + (-1))) =
      S.d p (p + 1) ≫ a.f (p + 1) ≫
        homotopyCofiber.inlX f (p + 1) (p + 1 + (-1)) (ComplexShape.up_mk _ _ (by omega))
    dsimp only [mappingCone, homotopyCofiber_d]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
    have h : -( a.f p ≫ homotopyCofiber.inlX f p (p + (-1))
        (ComplexShape.up_mk _ _ (by omega)) ≫ homotopyCofiber.d f (p + (-1)) p) =
        S.d p (p + 1) ≫ a.f (p + 1) ≫
          homotopyCofiber.inlX f (p + 1) p (ComplexShape.up_mk _ _ rfl) := by
      rw [homotopyCofiber.inlX_d f (p + (-1)) p (p + 1)
        (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)]
      simp only [Preadditive.comp_add, Preadditive.comp_neg]
      have hz : a.f p ≫ f.f p = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) ha
      simp only [reassoc_of% hz, zero_comp, add_zero, neg_neg]
      rw [reassoc_of% (a.comm p (p + 1))]
    convert h using 1
    · simp only [show p + 1 + (-1) = p by omega, homotopyCofiber_X]
    · congr! 10 <;> omega
    · congr! 10 <;> omega


private lemma closedConeLift_projections
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0)
    (p r : ℤ) (hr : r = p + (-1)) :
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.sndX f r = 0 ∧
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.fstX f r p (by change r + 1 = p; omega) = a.f p := by
  subst r
  dsimp only [closedConeLift, shiftFunctorObjXIso]
  simp

private lemma closedConeLift_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (closedConeLift S.g S.f S.zero) := by
  classical
  have hf (p : ℤ) : Epi (S.g.f p) := by
    have := hS.epi_g
    infer_instance
  obtain ⟨κ, hκ, hqκ, _⟩ := exists_kernel_to_shifted_mappingCone_of_degreewise_epi S.g hf
  let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    hS.fIsKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g) WalkingParallelPair.zero
  have h : closedConeLift S.g S.f S.zero = e.hom ≫ κ := by
    ext p
    apply (cancel_mono
      ((mappingCone S.g).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom).mp
    apply homotopyCofiber.ext_to_X S.g (p - 1) p (by change p - 1 + 1 = p; omega)
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.2, hκ p |>.2]
      exact congrArg (fun t ↦ t.f p) he.symm
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.1, hκ p |>.1, comp_zero]
  rw [h]
  have := hqκ
  infer_instance

private lemma closedConeLift_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q S' P' Q' : CochainComplex C ℤ}
    (q : P ⟶ Q) (q' : P' ⟶ Q') (a : S ⟶ P) (a' : S' ⟶ P')
    (ha : a ≫ q = 0) (ha' : a' ≫ q' = 0)
    (s : S ⟶ S') (p : P ⟶ P') (b : Q ⟶ Q')
    (hs : s ≫ a' = a ≫ p) (hp : p ≫ q' = q ≫ b) :
    s ≫ closedConeLift q' a' ha' = closedConeLift q a ha ≫
      (mappingCone.map q q' p b hp.symm)⟦(-1 : ℤ)⟧' := by
  ext n
  dsimp only [comp_f, closedConeLift, shiftFunctor_map_f]
  rw [← Category.assoc, ← comp_f, hs, comp_f, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun t ↦ a.f n ≫ t)
  change p.f n ≫ (mappingCone.inl q').v n (n + -1) rfl =
    (mappingCone.inl q).v n (n + -1) rfl ≫
      (mappingCone.map q q' p b hp.symm).f (n + -1)
  simp [mappingCone.map]

end CochainComplex


namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

set_option backward.isDefEq.respectTransparency false in
private lemma closedSupport_objQ_naturality (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let π := HomotopyCategory.quotient C (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ)
  have hC : DerivedCategory.Q.map f ≫
      ((DerivedCategory.quotientCompQhIso C).app J).inv =
      ((DerivedCategory.quotientCompQhIso C).app I).inv ≫
        DerivedCategory.Qh.map (π.map f) :=
    (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have hD : DerivedCategory.Qh.map (H.map (π.map f)) ≫
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    (DerivedCategory.quotientCompQhIso D).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map f)
  have hU : F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) ≫
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj J)) =
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj I)) ≫
        DerivedCategory.Qh.map (H.map (π.map f)) := by
    apply (cancel_mono (F.rightDerivedFunctorUnit.app (π.obj J))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hu := F.rightDerivedFunctorUnit.naturality (π.map f)
    change DerivedCategory.Qh.map (H.map (π.map f)) ≫
      F.rightDerivedFunctorUnit.app (π.obj J) =
      F.rightDerivedFunctorUnit.app (π.obj I) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) at hu
    rw [hu, IsIso.inv_hom_id_assoc]
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  simp only [Category.assoc]
  rw [← F.rightDerivedFunctor.map_comp_assoc, hC, F.rightDerivedFunctor.map_comp,
    Category.assoc, ← Category.assoc _ _
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom, hU]
  simp only [Category.assoc]
  rw [hD]

private noncomputable def closedSupport_resolutionIso (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K)) := by
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{w} C).app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2
  exact F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w} C).app K))) ≪≫
    F.rightDerivedFunctorObjQIso _

private lemma closedSupport_resolutionIso_naturality (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (closedSupport_resolutionIso F L).hom =
      (closedSupport_resolutionIso F K).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)) := by
  dsimp only [closedSupport_resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← F.rightDerivedFunctor.map_comp, ← DerivedCategory.Q.map_comp]
  rw [show f ≫ (CochainComplex.toKInjectiveResolution.{w} C).app L =
    (CochainComplex.toKInjectiveResolution.{w} C).app K ≫
      (CochainComplex.kInjectiveResolutionFunctor.{w} C).map f from
      (CochainComplex.toKInjectiveResolution.{w} C).naturality f]
  rw [DerivedCategory.Q.map_comp, F.rightDerivedFunctor.map_comp, Category.assoc,
    closedSupport_objQ_naturality]
  simp only [Category.assoc]
attribute [local irreducible] closedSupport_resolutionIso

set_option backward.isDefEq.respectTransparency false in
private theorem closedSupport_comparison
    (F E B : C ⥤ D) [F.Additive] [E.Additive] [B.Additive]
    (α : F ⟶ E) (τ : E ⟶ B) (hzero : ∀ J, α.app J ≫ τ.app J = 0)
    (hExact : ∀ J, Injective J →
      (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact) :
    let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
    ∃ e : ∀ K : CochainComplex C ℤ,
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex C ℤ) (f : K ⟶ L),
        F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ (e L).hom =
          (e K).hom ≫ (shiftFunctor (DerivedCategory D) (-1 : ℤ)).map
            (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
              ((E.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              ((B.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              (q.naturality ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)).symm)) := by
  let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  let R := CochainComplex.kInjectiveResolutionFunctor.{w} C
  let a := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
  have hz (K : CochainComplex C ℤ) :
      a.app K ≫ q.app K = 0 := by
    ext n : 1
    exact hzero (K.X n)
  let S (K : CochainComplex C ℤ) :=
    ShortComplex.mk (a.app (R.obj K)) (q.app (R.obj K)) (hz (R.obj K))
  have hS (K : CochainComplex C ℤ) :
      (S K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact hExact ((R.obj K).X n) inferInstance
  let κ (K : CochainComplex C ℤ) :=
    CochainComplex.closedConeLift (q.app (R.obj K)) (a.app (R.obj K)) (hz (R.obj K))
  have hκ (K : CochainComplex C ℤ) :
      QuasiIso (κ K) := CochainComplex.closedConeLift_quasiIso (S K) (hS K)
  let e (K : CochainComplex C ℤ) :=
    closedSupport_resolutionIso F K ≪≫
      asIso (DerivedCategory.Q.map (κ K)) ≪≫
        (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app
          (CochainComplex.mappingCone (q.app (R.obj K)))
  refine ⟨e, ?_⟩
  intro K L f
  dsimp only [e, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc,
    closedSupport_resolutionIso_naturality,
    Category.assoc, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun t ↦ (closedSupport_resolutionIso F K).hom ≫ t)
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hn := CochainComplex.closedConeLift_naturality
    (q.app (R.obj K)) (q.app (R.obj L)) (a.app (R.obj K)) (a.app (R.obj L))
    (hz (R.obj K)) (hz (R.obj L))
    ((F.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((B.mapHomologicalComplex (.up ℤ)).map (R.map f))
    (a.naturality (R.map f)) (q.naturality (R.map f))
  rw [hn, DerivedCategory.Q.map_comp, Category.assoc]
  apply congrArg (fun t ↦ DerivedCategory.Q.map (κ K) ≫ t)
  exact ((DerivedCategory.Q (C := D)).commShiftIso (-1 : ℤ)).hom.naturality
    (CochainComplex.mappingCone.map (q.app (R.obj K)) (q.app (R.obj L))
      ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
      ((B.mapHomologicalComplex (.up ℤ)).map (R.map f)) (q.naturality (R.map f)).symm)


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem closedSupportHom_globalSections_natural {A : Type (u + 1)} [CommRing A]
    {L K : Scheme.{u}} (m : K ⟶ L)
    {F F' : Sheaf L.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ L.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ K.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections L.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).hom.naturality_assoc k]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m).unit.naturality k
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.app ((upperStar (ModuleCat.{u + 1} A) m).obj F')) hu.symm

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary global derived Hom from `i_* A_D` is the shifted cone of restriction of
ordinary derived global sections to the complementary open. The existential `q` is fixed
in every degree by the existing global-section pullback map, so is not an arbitrary arrow.
The cone is computed on the functorial K-injective resolution, and the final equation is
naturality in every map of complexes. Both sides invert quasi-isomorphisms, hence this
also expresses naturality on the derived category. No boundedness is assumed.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-closed-support-hom.md
(blueprint: lem-amb-closed-support-hom).

Proof: Construct the restriction natural transformation on sheaves and map it to complexes.
The underived closed-support Hom sequence is short exact on each injective sheaf, so applying
it to the functorial resolution gives a short exact sequence of complexes. The explicit map
from its first term to the shifted cone is inclusion in the source summand. The existing
kernel-to-shifted-cone theorem proves it is a quasi-isomorphism, and the formula for cone maps
proves its naturality. The concrete K-injective computation of the right derived functor,
together with the resolution quasi-isomorphism, identifies the source with ordinary derived
Hom. Naturality of its unit, of the resolution, and of the shift comparison gives the stated
equation. This concrete formulation needs no separate derived computation of the open term.
-/
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm)) := by
  let τ : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    { app := fun F => globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v F
      naturality := fun F F' k => closedSupportHom_globalSections_natural v k }
  let q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ) := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  have hq : ∀ (K : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
      (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n) := by
    intro K n
    exact NatTrans.mapHomologicalComplex_app_f τ (ComplexShape.up ℤ) K n
  let F := (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))))
  obtain ⟨α, hzero, hExact⟩ := closedSupportHomSequence A i v hcomp τ (fun _ ↦ rfl)
  refine ⟨q, hq, ?_⟩
  have : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  have : (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  exact CategoryTheory.Functor.closedSupport_comparison F
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)) α τ hzero hExact

end AlgebraicGeometry.Etale
```

`Sheaf.AlgebraicGeometry.ClosedSupportHomSequence`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The closed-support Hom sequence

The ordinary injective-sheaf exact sequence used in the derived closed-support comparison.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
private lemma restriction_unit_formula
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : C ⥤ D) (L : D ⥤ C) (B : C ⥤ E) (G : D ⥤ E)
    (adj : U ⊣ L) (b : L ⋙ B ≅ G) {P : C} {PV : D} {M : E}
    (c : U.obj P ≅ PV) (ηT : M ⟶ B.obj P) (ηV : M ⟶ G.obj PV)
    (h : ηT ≫ B.map (adj.unit.app P ≫ L.map c.hom) ≫ b.hom.app PV = ηV)
    {J : C} (f : P ⟶ J) :
    ηT ≫ B.map f ≫ B.map (adj.unit.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ G.map (c.inv ≫ U.map f) := by
  have hb : ηT ≫ B.map (adj.unit.app P) ≫ b.hom.app (U.obj P) =
      ηV ≫ G.map c.inv := by
    apply (cancel_mono (G.map c.hom)).mp
    simp only [Category.assoc, ← G.map_comp, c.inv_hom_id, Functor.map_id,
      Category.comp_id]
    rw [← b.hom.naturality]
    dsimp only [Functor.comp_map]
    rw [← B.map_comp_assoc]
    exact h
  have hn : f ≫ adj.unit.app J = adj.unit.app P ≫ L.map (U.map f) :=
    adj.unit.naturality f
  rw [← B.map_comp_assoc, hn, B.map_comp, Category.assoc]
  have hbn : B.map (L.map (U.map f)) ≫ b.hom.app (U.obj J) =
      b.hom.app (U.obj P) ≫ G.map (U.map f) := b.hom.naturality (U.map f)
  rw [hbn, reassoc_of% hb, G.map_comp]
private noncomputable def adjunctionHomLinearEquiv
    (R : Type*) [Ring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Linear R]
    (adj : F ⊣ G) (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
    rw [Functor.map_smul, Linear.comp_smul]

end CategoryTheory

namespace AlgebraicGeometry.Etale
private noncomputable def rankOneSectionsEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj J := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  have : ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (⊤_ T.Etale))).Linear A := adj.right_adjoint_linear
  let e : (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (ModuleCat.of A A ⟶ ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).obj J) :=
    CategoryTheory.adjunctionHomLinearEquiv A adj (ModuleCat.of A A) J
  exact (e.trans (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf A A _))).trans
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).app J).symm.toLinearEquiv

private lemma rankOneSectionsEquiv_naturality (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {J J' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : J ⟶ J') (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    rankOneSectionsEquiv A T J' (f ≫ k) =
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
        (rankOneSectionsEquiv A T J f) := by
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).inv.app J'
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).homEquiv _ _ (f ≫ k)) (1 : A)) =
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).inv.app J
        (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
          terminalIsTerminal).homEquiv _ _ f) (1 : A)))
  rw [Adjunction.homEquiv_naturality_right]
  exact congrArg (fun g ↦ g
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ f) (1 : A)))
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality k)

private lemma unit_app_upperStarConstantSheafIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) (a : ModuleCat.{u + 1} A) :
    (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} A) v).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.app _ =
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v))
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit] at this
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at this
  rw [← this, Scheme.upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.naturality]
  rfl

private lemma rankOneSections_restriction (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
      (rankOneSectionsEquiv A T J f) =
    rankOneSectionsEquiv A V ((upperStar (ModuleCat.{u + 1} A) v).obj J)
      (((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)).inv ≫ (upperStar (ModuleCat.{u + 1} A) v).map f) := by
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let U := upperStar (ModuleCat.{u + 1} A) v
  let B := (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ T.Etale))
  let C := (sheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ V.Etale))
  let b := lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v
  let c := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit
  let ηT := (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  let ηV := (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  have hmap : ηT ≫ B.map f ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ C.map (c.inv ≫ U.map f) :=
    CategoryTheory.restriction_unit_formula U (lowerStar (ModuleCat.{u + 1} A) v) B C
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v) b c ηT ηV
        (unit_app_upperStarConstantSheafIso A v (ModuleCat.of A A)) f
  let eT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  let eV := Sheaf.ΓNatIsoSheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  have hr : (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J =
      ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J) := by
    change (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      (eT.hom.app J ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) ≫
        eV.inv.app (U.obj J)) = _
    simp only [Category.assoc, eT.inv_hom_id_app_assoc]
    rw [reassoc_of% hmap]
  change ((ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) (1 : A) =
    (ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J)) (1 : A)
  exact congrArg (fun g ↦ g (1 : A)) hr

end AlgebraicGeometry.Etale

namespace CategoryTheory
universe v u' w
variable {C : Type u'} [Category.{v} C] [Abelian C]
  (R : Type w) [Ring R] [Linear R C]
private noncomputable def linearHomShortComplex (S : ShortComplex C) (J : C) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (((linearCoyoneda R C).map S.g.op).app J)
    (((linearCoyoneda R C).map S.f.op).app J) (by
      ext x
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp])
private lemma linearHomShortComplex_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    (J : C) [Injective J] : (linearHomShortComplex R S J).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    constructor
    · intro h
      obtain ⟨x, hx⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel y h
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp]
  · intro x y hxy
    exact (cancel_epi S.g).1 hxy
  · intro z
    exact ⟨Injective.factorThru z S.f, Injective.comp_factorThru z S.f⟩
end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- Maps out of the closed constant sheaf form the kernel of restriction on an
injective sheaf, naturally in the target sheaf.

Source: Stacks Project, Etale Cohomology Tag 095L (the open–closed exact sequence),
Modules on Sites Tag 03DI (extension by zero and its adjunction), and
literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md, proof steps 1 and 3.
(blueprint: new-lem-amb-closed-support-hom-sequence).

Proof: Apply the open–closed short exact sequence to the constant rank-one sheaf A_T.
The canonical inverse-image identifications give the sequence
0 → v_! A_V → A_T → i_* A_D → 0, whose maps are the counit and unit.
Precomposition with the last map, followed by the identification
Hom(A_T,J) ≅ Γ(T,J) sending a morphism to the image of 1, defines α.
Associativity of composition proves naturality in J. The extension-by-zero
adjunction identifies Hom(v_! A_V,J) with Γ(V,v^*J), and the counit formula
identifies precomposition with the first map with the prescribed τ.
The composite is zero because the open–closed sequence is a complex.
Precomposition with its epimorphism is injective; a map from A_T which vanishes
on v_! A_V factors uniquely through the cokernel i_* A_D. This is exactness
at Γ(T,J). When J is injective, every map v_! A_V → J extends across the
monomorphism v_! A_V → A_T, so τ is surjective. These arguments include the
empty open or closed scheme and the zero coefficient ring. -/
theorem closedSupportHomSequence (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∃ (α : (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
        (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)))) ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hzero : ∀ J, α.app J ≫ τ.app J = 0),
      ∀ J, Injective J → (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact := by
  classical
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  have hicomp : Set.range i.base = (Set.range v.base)ᶜ := by
    rw [hcomp, compl_compl]
  let S := openClosedShortComplex (ModuleCat.{u + 1} A) v i
    (disjoint_range_of_range_eq_compl v i hicomp) P
  have hS : S.ShortExact := shortExact_openClosedShortComplex
    (ModuleCat.{u + 1} A) v i P hicomp
  let c := (lowerStar (ModuleCat.{u + 1} A) i).mapIso
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A))
  let g := S.g ≫ c.hom
  let α : (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
      (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)))) ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
    { app J := ModuleCat.ofHom ((rankOneSectionsEquiv A T J).toLinearMap.comp
        (Linear.leftComp A J g))
      naturality J J' k := by
        ext f
        change rankOneSectionsEquiv A T J' (g ≫ f ≫ k) = _
        rw [← Category.assoc, rankOneSectionsEquiv_naturality]
        rfl }
  let U := upperStar (ModuleCat.{u + 1} A) v
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
  have : U.Linear A := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).left_adjoint_linear
  let d := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let e₃ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (S.X₁ ⟶ J) ≃ₗ[A] (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (U.obj J) :=
    (CategoryTheory.adjunctionHomLinearEquiv A a (U.obj P) J).trans
      ((Linear.homCongr A d (Iso.refl (U.obj J))).trans
        (rankOneSectionsEquiv A V (U.obj J)))
  have hβ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (f : P ⟶ J) :
      τ.app J (rankOneSectionsEquiv A T J f) = e₃ J (S.f ≫ f) := by
    rw [hτ]
    erw [rankOneSections_restriction]
    dsimp only [e₃, LinearEquiv.trans_apply, Linear.homCongr_apply]
    apply congrArg (rankOneSectionsEquiv A V (U.obj J))
    change d.inv ≫ U.map f = d.inv ≫ a.homEquiv _ _ (a.counit.app P ≫ f)
    rw [Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_symm_id]
    erw [Equiv.apply_symm_apply, Category.id_comp]
  have hzero (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      α.app J ≫ τ.app J = 0 := by
    ext f
    change τ.app J (rankOneSectionsEquiv A T J (g ≫ f)) = 0
    rw [hβ]
    have hz : S.f ≫ g ≫ f = 0 := by
      dsimp only [g]
      rw [← Category.assoc, ← Category.assoc, S.zero, zero_comp, zero_comp]
    rw [hz, map_zero]
  refine ⟨α, hzero, ?_⟩
  intro J hJ
  let := hJ
  let e₁ := (Linear.homCongr A c (Iso.refl J)).toModuleIso
  let e₂ := (rankOneSectionsEquiv A T J).toModuleIso
  let e := ShortComplex.isoMk (S₁ := CategoryTheory.linearHomShortComplex A S J)
    (S₂ := ShortComplex.mk (α.app J) (τ.app J) (hzero J))
    e₁ e₂ (e₃ J).toModuleIso (by
      ext f
      change rankOneSectionsEquiv A T J (g ≫ ((c.inv ≫ f) ≫ 𝟙 J)) =
        rankOneSectionsEquiv A T J (S.g ≫ f)
      simp [g]) (by
      ext f
      exact hβ J f)
  exact ShortComplex.shortExact_of_iso e
    (CategoryTheory.linearHomShortComplex_shortExact A S hS J)
end AlgebraicGeometry.Etale
```

## New

The item interface and the supporting modules, verbatim:

`Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`:

```lean
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
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Naturality of the supported Hom identification under base change

Source: literature/stacks-project/etale-cohomology.tex, Tag 0A45,
lemma-cohomology-with-support-triangle;
blueprint sec-smooth-purity/sk-prop-sf-cbc
(blueprint: lem-asd-supported-kummer-support-hom-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true

universe w v u v' u' v'' u'' v₀ u₀

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor ZeroObject

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections

/-- The standard resolution functor and its unit, packaged before site specialization.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] where
  R : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  unit : 𝟭 (CochainComplex C ℤ) ⟶ R
  isKInjective : ∀ K, (R.obj K).IsKInjective
  unitMonoQuasiIso : ∀ K, HomologicalComplex.monoQuasiIso C (.up ℤ) (unit.app K)
  isFibrant : ∀ K, (HomologicalComplex.monoQuasiIso C (.up ℤ)).rlp
    (0 : R.obj K ⟶ (0 : CochainComplex C ℤ))

/-- Package the existing functorial resolution, without changing its chosen objects.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionData (C : Type u') [Category.{v'} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] : SupportedHomResolutionData C where
  R := CochainComplex.kInjectiveResolutionFunctor C
  unit := CochainComplex.toKInjectiveResolution C
  isKInjective := fun _ ↦ inferInstance
  unitMonoQuasiIso := CochainComplex.monoQuasiIso_toKInjectiveResolution_app C
  isFibrant := by
    intro K
    let d := MorphismProperty.functorialFactorizationData
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.monoQuasiIso C (ComplexShape.up ℤ)).rlp
    have hp := d.hp ((CochainComplex.toArrowZero C).obj K)
    have he : d.p.app ((CochainComplex.toArrowZero C).obj K) = 0 :=
      (isZero_zero (CochainComplex C ℤ)).eq_of_tgt _ _
    rw [he] at hp
    exact hp

namespace CategoryTheory.Functor

/-- The canonical comparison from a derived functor to its functorial resolution model.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomResolutionMap
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {B : Type u} [Category.{v} B] [Abelian B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} B]
    (F : C ⥤ B) [F.Additive] (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((supportedHomResolutionData C).R.obj K)) := by
  letI := (supportedHomResolutionData C).isKInjective K
  exact F.rightDerivedFunctor.map
      (DerivedCategory.Q.map ((supportedHomResolutionData C).unit.app K)) ≫
    (F.rightDerivedFunctorObjQIso ((supportedHomResolutionData C).R.obj K)).hom

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 200000] closedSupportEtaleAbelian
attribute [local instance 200000] closedSupportEtaleLinear

/-- The Grothendieck property for the same fixed abelian structure.
Source: Stacks, Tag 03DA (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
theorem supportedEtaleGrothendieck (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance 200000] supportedEtaleGrothendieck


/-- The fixed functorial resolution on the etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).R

/-- The resolution unit, with its target functor fixed explicitly.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedResolutionUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    𝟭 (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) ⟶
      supportedResolutionFunctor A T :=
  (supportedHomResolutionData (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).unit

/-- Functorial degreewise-injective K-injective replacement, on the specified etale site.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedResolution (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedResolutionFunctor A T).obj K

/-- The functor of complexes of Hom from the closed constant sheaf.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomComplexFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :=
  (closedSupportHomFunctor A i).mapHomologicalComplex (.up ℤ)

/-- The derived Hom functor on complexes, with its model fixed before specialization.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDerivedFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q ⋙ (closedSupportHomFunctor A i).rightDerivedFunctor

/-- The global-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The open-section functor on complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedOpenSectionsComplexFunctor (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :=
  (upperStar (ModuleCat.{u + 1} A) v ⋙
    Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise ordinary Hom from the closed constant sheaf. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomComplex (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (ModuleCat.{u + 1} A) ℤ :=
  (supportedHomComplexFunctor A i).obj I

/-- The derived Hom object of the recorded closed-support theorem. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomObject (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  (supportedHomDerivedFunctor A i).obj K

/-- Evaluation at 1 identifies a map from the rank-one constant sheaf with a global section.
Use the constant-sheaf adjunction and the published terminal-section/global-section iso.
Source: Stacks, Tag 095L (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedEvaluateSection (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : ordinaryFiniteConstant A T ⟶ F) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj F :=
  rankOneSectionsEquiv A T F c

/-- Termwise inverse image as a fixed functor on complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedPullbackComplexFunctor (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T) :
    CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ ⥤
      CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (upperStar (ModuleCat.{u + 1} A) h).mapHomologicalComplex (.up ℤ)

/-- The inverse image of a complex is taken termwise; exactness makes this derived pullback.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedPullbackComplex (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ :=
  (supportedPullbackComplexFunctor A h).obj K


/-- The normalized cone model, with its complex functors supplied as parameters.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomDiagram (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] where
  R : C ⥤ C
  F : C ⥤ CochainComplex B₀ ℤ
  E : C ⥤ CochainComplex B₀ ℤ
  B : C ⥤ CochainComplex B₀ ℤ
  H : C ⥤ D₀
  modelMap : ∀ K, H.obj K ⟶ Q₀.obj (F.obj (R.obj K))
  restriction : ∀ I n, (E.obj I).X n ⟶ (B.obj I).X n
  normalization : ∀ I, (F.obj I ⟶ E.obj I) → Prop

/-- A normalized cone model of a fixed diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomConeModelCore (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀]
    (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C]
    (d : SupportedHomDiagram B₀ D₀ Q₀ C) where
  q : d.E ⟶ d.B
  q_spec : ∀ I n, (q.app I).f n = d.restriction I n
  modelIso : ∀ K, d.H.obj K ≅ Q₀.obj (d.F.obj (d.R.obj K))
  modelIso_spec : ∀ K, (modelIso K).hom = d.modelMap K
  toSections : ∀ K, d.F.obj (d.R.obj K) ⟶ d.E.obj (d.R.obj K)
  toSections_spec : ∀ K, d.normalization (d.R.obj K) (toSections K)
  inclusion : ∀ K, d.F.obj (d.R.obj K) ⟶
    (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧
  inclusion_fst : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn =
        (toSections K).f n
  inclusion_snd : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)),
    (inclusion K).f n ≫ (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.sndX (q.app (d.R.obj K)) m = 0
  comparison : ∀ K, d.H.obj K ≅
    Q₀.obj ((CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧)
  comparison_spec : ∀ K, (comparison K).hom =
    (modelIso K).hom ≫ Q₀.map (inclusion K)
  comparison_naturality : ∀ (K L : C) (f : K ⟶ L),
    d.H.map f ≫ (comparison L).hom =
      (comparison K).hom ≫ Q₀.map
        ((shiftFunctor (CochainComplex (B₀) ℤ) (-1 : ℤ)).map
          (CochainComplex.mappingCone.map _ _ (d.E.map (d.R.map f)) (d.B.map (d.R.map f))
            (q.naturality (d.R.map f)).symm))
  projection : ∀ K, (CochainComplex.mappingCone (q.app (d.R.obj K)))⟦(-1 : ℤ)⟧ ⟶ d.E.obj (d.R.obj K)
  projection_spec : ∀ K (n m : ℤ) (hm : m = n + (-1 : ℤ)) (hn : m + 1 = n),
    (projection K).f n = (CochainComplex.shiftFunctorObjXIso _ (-1) n m hm).hom ≫
      HomologicalComplex.homotopyCofiber.fstX (q.app (d.R.obj K)) m n hn

/-- Transport a map through the two fixed derived models.
Source: Stacks, Tag 070K (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev SupportedHomConeModelCore.transport
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀]
    {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C]
    {d : SupportedHomDiagram B₀ D₀ Q₀ C}
    {C' : Type u''} [Category.{v''} C']
    {d' : SupportedHomDiagram B₀ D₀ Q₀ C'}
    (M : SupportedHomConeModelCore B₀ D₀ Q₀ C d)
    (M' : SupportedHomConeModelCore B₀ D₀ Q₀ C' d')
    (K : C) (K' : C') (f : d.F.obj (d.R.obj K) ⟶ d'.F.obj (d'.R.obj K')) :
    d.H.obj K ⟶ d'.H.obj K' :=
  (M.modelIso K).hom ≫ Q₀.map f ≫ (M'.modelIso K').inv

/-- Evaluation normalization on a chosen resolution, with its complex functors fixed.
Source: Stacks, Tag 095L (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedHomSectionNormalization (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (t : (supportedHomComplexFunctor A i).obj I ⟶
      (supportedSectionsComplexFunctor A T).obj I) : Prop :=
  t = (NatTrans.mapHomologicalComplex (closedSupportHomToSections A i) (.up ℤ)).app I

/-- Equality with the canonical map is exactly the original evaluation normalization.
Source: Stacks, Tags 095L, 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality).

Evaluate the canonical map componentwise for the forward implication. Conversely, equality
on every element gives equality of the module maps in each degree and hence of chain maps. -/
theorem supportedHomSectionNormalization_iff (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (t : (supportedHomComplexFunctor A i).obj I ⟶
      (supportedSectionsComplexFunctor A T).obj I) :
    supportedHomSectionNormalization A i I t ↔
      ∀ (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n),
        (t.f n) c = supportedEvaluateSection A T (I.X n) (supportedConstantUnit A i ≫ c) := by
  have hc (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n) :
      (((NatTrans.mapHomologicalComplex (closedSupportHomToSections A i) (.up ℤ)).app I).f n)
        c = supportedEvaluateSection A T (I.X n) (supportedConstantUnit A i ≫ c) := by
    change (closedSupportHomToSections A i).app (I.X n) c = _
    simpa only [supportedEvaluateSection, supportedConstantUnit, ordinaryFiniteConstant] using
      (closedSupportHomToSections_apply A i (I.X n) c)
  constructor
  · intro h n c
    change t = _ at h
    rw [h]
    exact hc n c
  · intro h
    change t = _
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (h n c).trans (hc n c).symm

/-- Build the resolution and section diagram before specifying a concrete sheaf category.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagramFactory
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u} [Category.{v} D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{v} D]
    (F E B : C ⥤ D) [F.Additive] [E.PreservesZeroMorphisms] [B.PreservesZeroMorphisms]
    (restriction : ∀ (I : CochainComplex C ℤ) n,
      ((E.mapHomologicalComplex (.up ℤ)).obj I).X n ⟶
        ((B.mapHomologicalComplex (.up ℤ)).obj I).X n)
    (α : F ⟶ E) :
    SupportedHomDiagram D (DerivedCategory.{v} D) DerivedCategory.Q (CochainComplex C ℤ) where
  R := (supportedHomResolutionData C).R
  F := F.mapHomologicalComplex (.up ℤ)
  E := E.mapHomologicalComplex (.up ℤ)
  B := B.mapHomologicalComplex (.up ℤ)
  H := DerivedCategory.Q ⋙ F.rightDerivedFunctor
  modelMap := CategoryTheory.Functor.supportedHomResolutionMap F
  restriction := restriction
  normalization := fun I t ↦
    t = (NatTrans.mapHomologicalComplex α (.up ℤ)).app I

/-- The functors and normalization maps defining the supported-Hom diagram.
Source: Stacks, Tags 070K, 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomDiagram (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) :
    SupportedHomDiagram (ModuleCat.{u + 1} A)
      (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
      (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  supportedHomDiagramFactory
    (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := ModuleCat.{u + 1} A) (closedSupportHomFunctor A i)
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (fun I n ↦ (closedSupportSectionsPullback A v).app (I.X n))
    (closedSupportHomToSections A i)

/-- The etale specialization of the normalized supported-Hom cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev SupportedHomConeModel (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) (v : V ⟶ T) :=
  SupportedHomConeModelCore (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (supportedHomDiagram A i v)

/-- The relative object uses the actual shifted restriction cone. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedRelativeObject (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} A) :=
  DerivedCategory.Q.obj
    ((CochainComplex.mappingCone (M.q.app (supportedResolution A T K)))⟦(-1 : ℤ)⟧)

/-- The normalized supported-Hom identification on cohomology. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomIdentification (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} {i : D ⟶ T} {v : V ⟶ T} (M : SupportedHomConeModel A i v)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) (n : ℤ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) n).mapIso (M.comparison K).symm

/-- The condition that a resolution comparison extends the resolution unit.
Source: Stacks, Tag 079P (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedResolutionComparisonCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h (supportedResolution A T K) ⟶
      supportedResolution A T' (supportedPullbackComplex A h K)) : Prop :=
  (supportedPullbackComplexFunctor A h).map
    ((supportedResolutionUnit A T).app K) ≫ a =
      (supportedResolutionUnit A T').app (supportedPullbackComplex A h K)

/-- The degreewise formula for pullback of sections along a comparison of complexes.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T : Scheme.{u}} (h : T' ⟶ T)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (s : (supportedSectionsComplexFunctor A T).obj I ⟶
      (supportedSectionsComplexFunctor A T').obj J) : Prop :=
  ∀ n, s.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) h (I.X n) ≫
    (Sheaf.Γ T'.smallEtaleTopology (ModuleCat.{u + 1} A)).map (a.f n)

/-- The degreewise formula for the open part of a pullback square.
Source: Stacks, Tag 03Q1 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedOpenSectionsMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T V' V : Scheme.{u}} (h : T' ⟶ T) (v : V ⟶ T) (v' : V' ⟶ T')
    (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (b : (supportedOpenSectionsComplexFunctor A v).obj I ⟶
      (supportedOpenSectionsComplexFunctor A v').obj J) : Prop :=
  ∀ n, b.f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) hV
    ((upperStar (ModuleCat.{u + 1} A) v).obj (I.X n)) ≫
      (Sheaf.Γ V'.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStarComp (ModuleCat.{u + 1} A) hV v).inv.app _ ≫
          (upperStarComp (ModuleCat.{u + 1} A) v' h (hV ≫ v) sqV.w).hom.app _ ≫
          (upperStar (ModuleCat.{u + 1} A) v').map (a.f n))

/-- The degreewise formula for inverse-image and precomposition on Hom complexes.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
def supportedHomMapCondition (A : Type (u + 1)) [CommRing A]
    {T' T D' D : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i)))
    (I : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a : supportedPullbackComplex A h I ⟶ J)
    (f : supportedHomComplex A i I ⟶ supportedHomComplex A i' J) : Prop :=
  ∀ (n : ℤ) (c : (closedSupportHomSource A i) ⟶ I.X n),
    (f.f n) c = e ≫ (upperStar (ModuleCat.{u + 1} A) h).map c ≫ a.f n

/-- Pullback maps with the source complexes and their functors left abstract.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackDiagram
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C'] where
  source : SupportedHomDiagram B₀ D₀ Q₀ C
  target : SupportedHomDiagram B₀ D₀ Q₀ C'
  P : C ⥤ C'
  unitSpec : ∀ K, (P.obj (source.R.obj K) ⟶ target.R.obj (P.obj K)) → Prop
  sectionsSpec : ∀ I J, (P.obj I ⟶ J) → (source.E.obj I ⟶ target.E.obj J) → Prop
  openSpec : ∀ I J, (P.obj I ⟶ J) → (source.B.obj I ⟶ target.B.obj J) → Prop
  homSpec : ∀ I J, (P.obj I ⟶ J) → (source.F.obj I ⟶ target.F.obj J) → Prop

/-- Normalized representative maps for a fixed pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedHomPullbackMaps
    (B₀ : Type u) [Category.{v} B₀] [Abelian B₀]
    (D₀ : Type u₀) [Category.{v₀} D₀] (Q₀ : CochainComplex B₀ ℤ ⥤ D₀)
    (C : Type u') [Category.{v'} C] (C' : Type u'') [Category.{v''} C']
    (d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C') where
  sourceModel : SupportedHomConeModelCore B₀ D₀ Q₀ C d.source
  targetModel : SupportedHomConeModelCore B₀ D₀ Q₀ C' d.target
  resolutionComparison : ∀ K, d.P.obj (d.source.R.obj K) ⟶ d.target.R.obj (d.P.obj K)
  resolutionComparison_spec : ∀ K, d.unitSpec K (resolutionComparison K)
  sectionsMap : ∀ K, d.source.E.obj (d.source.R.obj K) ⟶ d.target.E.obj (d.target.R.obj (d.P.obj K))
  sectionsMap_spec : ∀ K, d.sectionsSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (sectionsMap K)
  openSectionsMap : ∀ K, d.source.B.obj (d.source.R.obj K) ⟶
    d.target.B.obj (d.target.R.obj (d.P.obj K))
  openSectionsMap_spec : ∀ K, d.openSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (openSectionsMap K)
  restriction_square : ∀ K, sectionsMap K ≫ targetModel.q.app (d.target.R.obj (d.P.obj K)) =
    sourceModel.q.app (d.source.R.obj K) ≫ openSectionsMap K
  homMap : ∀ K, d.source.F.obj (d.source.R.obj K) ⟶ d.target.F.obj (d.target.R.obj (d.P.obj K))
  homMap_spec : ∀ K, d.homSpec (d.source.R.obj K)
    (d.target.R.obj (d.P.obj K)) (resolutionComparison K) (homMap K)

/-- Hom transport through normalized models of an abstract pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def SupportedHomPullbackMaps.homPullback
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'} (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    (K : C) :=
  SupportedHomConeModelCore.transport N.sourceModel N.targetModel K (d.P.obj K) (N.homMap K)

/-- The diagonal cone map of an abstract pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def SupportedHomPullbackMaps.relativePullback
    {B₀ : Type u} [Category.{v} B₀] [Abelian B₀]
    {D₀ : Type u₀} [Category.{v₀} D₀] {Q₀ : CochainComplex B₀ ℤ ⥤ D₀}
    {C : Type u'} [Category.{v'} C] {C' : Type u''} [Category.{v''} C']
    {d : SupportedHomPullbackDiagram B₀ D₀ Q₀ C C'} (N : SupportedHomPullbackMaps B₀ D₀ Q₀ C C' d)
    (K : C) :=
  Q₀.map ((shiftFunctor (CochainComplex B₀ ℤ) (-1 : ℤ)).map
    (CochainComplex.mappingCone.map _ _ (N.sectionsMap K) (N.openSectionsMap K)
      (N.restriction_square K).symm))

/-- The specialization of the representative-map record to an etale pullback square.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def supportedHomPullbackDiagram (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :
  SupportedHomPullbackDiagram (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) where
  source := supportedHomDiagram A i v
  target := supportedHomDiagram A i' v'
  P := supportedPullbackComplexFunctor A h
  unitSpec := supportedResolutionComparisonCondition A h
  sectionsSpec := supportedSectionsMapCondition A h
  openSpec := supportedOpenSectionsMapCondition A h v v' hV sqV
  homSpec := supportedHomMapCondition A h i i' e

/-- The type of normalized maps on the fixed etale pullback diagram.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev supportedHomPullbackMapsType (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T) (i' : D' ⟶ T')
    (v : V ⟶ T) (v' : V' ⟶ T') (hV : V' ⟶ V) (sqV : IsPullback hV v' v h)
    (e : (closedSupportHomSource A i') ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((closedSupportHomSource A i))) :=
  SupportedHomPullbackMaps (ModuleCat.{u + 1} A)
    (DerivedCategory.{u + 1} (ModuleCat.{u + 1} A)) DerivedCategory.Q
    (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (CochainComplex (Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (supportedHomPullbackDiagram A h i i' v v' hV sqV e)

/-- The canonical representative maps for pullback of a closed/open pair. A resolution
comparison must extend the pulled-back resolution unit. Its section maps and Hom map are
specified degreewise; the relative pullback is then the diagonal mapping-cone map.
Source: Stacks, Tag 0A45 and blueprint lem-amb-cartier-kummer-map, penultimate paragraph
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
structure SupportedKummerSupportHomData (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} (h : T' ⟶ T) (i : D ⟶ T)
    (i' : D' ⟶ T') (hD : D' ⟶ D) (v : V ⟶ T) (v' : V' ⟶ T')
    (sqD : IsPullback hD i' i h) (hV : V' ⟶ V) (sqV : IsPullback hV v' v h) where
  exchange_isIso : IsIso (supportedConstantExchange A i i' h hD sqD.toCommSq)
  exchangeInverse : (closedSupportHomSource A i') ⟶
    (upperStar (ModuleCat.{u + 1} A) h).obj
      ((closedSupportHomSource A i))
  exchange_hom_inv : supportedConstantExchange A i i' h hD sqD.toCommSq ≫ exchangeInverse = 𝟙 _
  exchange_inv_hom : exchangeInverse ≫ supportedConstantExchange A i i' h hD sqD.toCommSq = 𝟙 _
  maps : supportedHomPullbackMapsType A h i i' v v' hV sqV exchangeInverse

namespace SupportedKummerSupportHomData

variable {A : Type (u + 1)} [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}

/-- The source normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev sourceModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.sourceModel

/-- The target normalized cone model.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev targetModel
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) := N.maps.targetModel

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def resolutionComparison
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev resolutionComparison_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.resolutionComparison_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def sectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev sectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.sectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def openSectionsMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev openSectionsMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.openSectionsMap_spec

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev restriction_square
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.restriction_square

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable def homMap
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap

/-- The original normalized representative-map interface.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
abbrev homMap_spec
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV) :=
  N.maps.homMap_spec

end SupportedKummerSupportHomData

/-- Actual relative pullback: apply localization and cohomology to the shifted diagonal
cone map, whose two components have specified section formulas. Source: Stacks, Tag 0A45
(blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedRelativePullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  N.maps.relativePullback K

/-- Actual Hom pullback: pull a representative back and precompose with the inverse of
closed exchange, then transport through the specified resolution-model isomorphisms.
Source: Stacks, Tag 0A45 (blueprint: lem-asd-supported-kummer-support-hom-naturality). -/
noncomputable abbrev supportedHomPullback (A : Type (u + 1)) [CommRing A]
    {T' T D' D V' V : Scheme.{u}} {h : T' ⟶ T} {i : D ⟶ T} {i' : D' ⟶ T'}
    {hD : D' ⟶ D} {v : V ⟶ T} {v' : V' ⟶ T'} {sqD : IsPullback hD i' i h}
    {hV : V' ⟶ V} {sqV : IsPullback hV v' v h}
    (N : SupportedKummerSupportHomData A h i i' hD v v' sqD hV sqV)
    (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  N.maps.homPullback K
```

`Sheaf.AlgebraicGeometry.ClosedSupportHom`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

public import Sheaf.AlgebraicGeometry.ClosedSupportHomSequence
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-!
# Closed support as a relative section complex

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md (blueprint: lem-amb-closed-support-hom).
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

universe w v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace CochainComplex
/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedConeLift
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0) :
    S ⟶ (mappingCone f)⟦(-1 : ℤ)⟧ where
  f p := a.f p ≫
    homotopyCofiber.inlX f p (p + (-1)) (ComplexShape.up_mk _ _ (by omega))
  comm' p q hpq := by
    obtain rfl : q = p + 1 := by simpa using hpq.symm
    rw [shiftFunctor_obj_d', Category.assoc]
    change a.f p ≫ homotopyCofiber.inlX f p (p + (-1)) _ ≫
      ((-1 : ℤ).negOnePow • (mappingCone f).d (p + (-1)) (p + 1 + (-1))) =
      S.d p (p + 1) ≫ a.f (p + 1) ≫
        homotopyCofiber.inlX f (p + 1) (p + 1 + (-1)) (ComplexShape.up_mk _ _ (by omega))
    dsimp only [mappingCone, homotopyCofiber_d]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Preadditive.comp_neg]
    have h : -( a.f p ≫ homotopyCofiber.inlX f p (p + (-1))
        (ComplexShape.up_mk _ _ (by omega)) ≫ homotopyCofiber.d f (p + (-1)) p) =
        S.d p (p + 1) ≫ a.f (p + 1) ≫
          homotopyCofiber.inlX f (p + 1) p (ComplexShape.up_mk _ _ rfl) := by
      rw [homotopyCofiber.inlX_d f (p + (-1)) p (p + 1)
        (ComplexShape.up_mk _ _ (by omega)) (ComplexShape.up_mk _ _ rfl)]
      simp only [Preadditive.comp_add, Preadditive.comp_neg]
      have hz : a.f p ≫ f.f p = 0 := by
        simpa only [comp_f, zero_f] using congrArg (fun g ↦ g.f p) ha
      simp only [reassoc_of% hz, zero_comp, add_zero, neg_neg]
      rw [reassoc_of% (a.comm p (p + 1))]
    convert h using 1
    · simp only [show p + 1 + (-1) = p by omega, homotopyCofiber_X]
    · congr! 10 <;> omega
    · congr! 10 <;> omega


/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_projections
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q : CochainComplex C ℤ} (f : P ⟶ Q) (a : S ⟶ P) (ha : a ≫ f = 0)
    (p r : ℤ) (hr : r = p + (-1)) :
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.sndX f r = 0 ∧
    (closedConeLift f a ha).f p ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) p r hr).hom ≫
          homotopyCofiber.fstX f r p (by change r + 1 = p; omega) = a.f p := by
  subst r
  dsimp only [closedConeLift, shiftFunctorObjXIso]
  simp

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) :
    QuasiIso (closedConeLift S.g S.f S.zero) := by
  classical
  have hf (p : ℤ) : Epi (S.g.f p) := by
    have := hS.epi_g
    infer_instance
  obtain ⟨κ, hκ, hqκ, _⟩ := exists_kernel_to_shifted_mappingCone_of_degreewise_epi S.g hf
  let e := hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel S.g)
  have he : e.hom ≫ kernel.ι S.g = S.f :=
    hS.fIsKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g) WalkingParallelPair.zero
  have h : closedConeLift S.g S.f S.zero = e.hom ≫ κ := by
    ext p
    apply (cancel_mono
      ((mappingCone S.g).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom).mp
    apply homotopyCofiber.ext_to_X S.g (p - 1) p (by change p - 1 + 1 = p; omega)
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.2, hκ p |>.2]
      exact congrArg (fun t ↦ t.f p) he.symm
    · simp only [Category.assoc, comp_f, closedConeLift_projections S.g S.f S.zero p
        (p - 1) (by omega) |>.1, hκ p |>.1, comp_zero]
  rw [h]
  have := hqκ
  infer_instance

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedConeLift_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S P Q S' P' Q' : CochainComplex C ℤ}
    (q : P ⟶ Q) (q' : P' ⟶ Q') (a : S ⟶ P) (a' : S' ⟶ P')
    (ha : a ≫ q = 0) (ha' : a' ≫ q' = 0)
    (s : S ⟶ S') (p : P ⟶ P') (b : Q ⟶ Q')
    (hs : s ≫ a' = a ≫ p) (hp : p ≫ q' = q ≫ b) :
    s ≫ closedConeLift q' a' ha' = closedConeLift q a ha ≫
      (mappingCone.map q q' p b hp.symm)⟦(-1 : ℤ)⟧' := by
  ext n
  dsimp only [comp_f, closedConeLift, shiftFunctor_map_f]
  rw [← Category.assoc, ← comp_f, hs, comp_f, Category.assoc]
  rw [Category.assoc]
  apply congrArg (fun t ↦ a.f n ≫ t)
  change p.f n ≫ (mappingCone.inl q').v n (n + -1) rfl =
    (mappingCone.inl q).v n (n + -1) rfl ≫
      (mappingCone.map q q' p b hp.symm).f (n + -1)
  simp [mappingCone.map]

end CochainComplex


namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

set_option backward.isDefEq.respectTransparency false in
private lemma closedSupport_objQ_naturality (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (F.rightDerivedFunctorObjQIso J).hom =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let π := HomotopyCategory.quotient C (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ)
  have hC : DerivedCategory.Q.map f ≫
      ((DerivedCategory.quotientCompQhIso C).app J).inv =
      ((DerivedCategory.quotientCompQhIso C).app I).inv ≫
        DerivedCategory.Qh.map (π.map f) :=
    (DerivedCategory.quotientCompQhIso C).inv.naturality f
  have hD : DerivedCategory.Qh.map (H.map (π.map f)) ≫
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom =
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) :=
    (DerivedCategory.quotientCompQhIso D).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map f)
  have hU : F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) ≫
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj J)) =
      CategoryTheory.inv (F.rightDerivedFunctorUnit.app (π.obj I)) ≫
        DerivedCategory.Qh.map (H.map (π.map f)) := by
    apply (cancel_mono (F.rightDerivedFunctorUnit.app (π.obj J))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hu := F.rightDerivedFunctorUnit.naturality (π.map f)
    change DerivedCategory.Qh.map (H.map (π.map f)) ≫
      F.rightDerivedFunctorUnit.app (π.obj J) =
      F.rightDerivedFunctorUnit.app (π.obj I) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Qh.map (π.map f)) at hu
    rw [hu, IsIso.inv_hom_id_assoc]
  dsimp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv]
  simp only [Category.assoc]
  rw [← F.rightDerivedFunctor.map_comp_assoc, hC, F.rightDerivedFunctor.map_comp,
    Category.assoc, ← Category.assoc _ _
      ((DerivedCategory.quotientCompQhIso D).app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)).hom, hU]
  simp only [Category.assoc]
  rw [hD]

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedSupport_resolutionIso (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K)) := by
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{w} C).app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2
  exact F.rightDerivedFunctor.mapIso
      (asIso (DerivedCategory.Q.map ((CochainComplex.toKInjectiveResolution.{w} C).app K))) ≪≫
    F.rightDerivedFunctorObjQIso _

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
lemma closedSupport_resolutionIso_naturality (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        (closedSupport_resolutionIso F L).hom =
      (closedSupport_resolutionIso F K).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
          ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)) := by
  dsimp only [closedSupport_resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← F.rightDerivedFunctor.map_comp, ← DerivedCategory.Q.map_comp]
  rw [show f ≫ (CochainComplex.toKInjectiveResolution.{w} C).app L =
    (CochainComplex.toKInjectiveResolution.{w} C).app K ≫
      (CochainComplex.kInjectiveResolutionFunctor.{w} C).map f from
      (CochainComplex.toKInjectiveResolution.{w} C).naturality f]
  rw [DerivedCategory.Q.map_comp, F.rightDerivedFunctor.map_comp, Category.assoc,
    closedSupport_objQ_naturality]
  simp only [Category.assoc]
attribute [local irreducible] closedSupport_resolutionIso

set_option backward.isDefEq.respectTransparency false in
private theorem closedSupport_comparison
    (F E B : C ⥤ D) [F.Additive] [E.Additive] [B.Additive]
    (α : F ⟶ E) (τ : E ⟶ B) (hzero : ∀ J, α.app J ≫ τ.app J = 0)
    (hExact : ∀ J, Injective J →
      (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact) :
    let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
    ∃ e : ∀ K : CochainComplex C ℤ,
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor.{w} C).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex C ℤ) (f : K ⟶ L),
        F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ (e L).hom =
          (e K).hom ≫ (shiftFunctor (DerivedCategory D) (-1 : ℤ)).map
            (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
              ((E.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              ((B.mapHomologicalComplex (.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f))
              (q.naturality ((CochainComplex.kInjectiveResolutionFunctor.{w} C).map f)).symm)) := by
  let q := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  let R := CochainComplex.kInjectiveResolutionFunctor.{w} C
  let a := NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)
  have hz (K : CochainComplex C ℤ) :
      a.app K ≫ q.app K = 0 := by
    ext n : 1
    exact hzero (K.X n)
  let S (K : CochainComplex C ℤ) :=
    ShortComplex.mk (a.app (R.obj K)) (q.app (R.obj K)) (hz (R.obj K))
  have hS (K : CochainComplex C ℤ) :
      (S K).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    exact hExact ((R.obj K).X n) inferInstance
  let κ (K : CochainComplex C ℤ) :=
    CochainComplex.closedConeLift (q.app (R.obj K)) (a.app (R.obj K)) (hz (R.obj K))
  have hκ (K : CochainComplex C ℤ) :
      QuasiIso (κ K) := CochainComplex.closedConeLift_quasiIso (S K) (hS K)
  let e (K : CochainComplex C ℤ) :=
    closedSupport_resolutionIso F K ≪≫
      asIso (DerivedCategory.Q.map (κ K)) ≪≫
        (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app
          (CochainComplex.mappingCone (q.app (R.obj K)))
  refine ⟨e, ?_⟩
  intro K L f
  dsimp only [e, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc,
    closedSupport_resolutionIso_naturality,
    Category.assoc, Category.assoc]
  simp only [Category.assoc]
  apply congrArg (fun t ↦ (closedSupport_resolutionIso F K).hom ≫ t)
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hn := CochainComplex.closedConeLift_naturality
    (q.app (R.obj K)) (q.app (R.obj L)) (a.app (R.obj K)) (a.app (R.obj L))
    (hz (R.obj K)) (hz (R.obj L))
    ((F.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
    ((B.mapHomologicalComplex (.up ℤ)).map (R.map f))
    (a.naturality (R.map f)) (q.naturality (R.map f))
  rw [hn, DerivedCategory.Q.map_comp, Category.assoc]
  apply congrArg (fun t ↦ DerivedCategory.Q.map (κ K) ≫ t)
  exact ((DerivedCategory.Q (C := D)).commShiftIso (-1 : ℤ)).hom.naturality
    (CochainComplex.mappingCone.map (q.app (R.obj K)) (q.app (R.obj L))
      ((E.mapHomologicalComplex (.up ℤ)).map (R.map f))
      ((B.mapHomologicalComplex (.up ℤ)).map (R.map f)) (q.naturality (R.map f)).symm)


end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical closed-support construction and its normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: lem-amb-closed-support-hom). -/
theorem closedSupportHom_globalSections_natural {A : Type (u + 1)} [CommRing A]
    {L K : Scheme.{u}} (m : K ⟶ L)
    {F F' : Sheaf L.smallEtaleTopology (ModuleCat.{u + 1} A)} (k : F ⟶ F') :
    (Sheaf.Γ L.smallEtaleTopology (ModuleCat.{u + 1} A)).map k ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F' =
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) m F ≫
      (Sheaf.Γ K.smallEtaleTopology (ModuleCat.{u + 1} A)).map
        ((upperStar (ModuleCat.{u + 1} A) m).map k) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections L.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).hom.naturality_assoc k]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) m).unit.naturality k
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar (ModuleCat.{u + 1} A) m).map k).hom.naturality
    (PreservesTerminal.iso m.Etale).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections K.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.app ((upperStar (ModuleCat.{u + 1} A) m).obj F')) hu.symm

/-- Pullback of global sections as a natural transformation on sheaves.
Source: Stacks, Tag 03Q1 (blueprint: lem-amb-closed-support-hom). -/
noncomputable def closedSupportSectionsPullback (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙ Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A) where
  app J := globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
  naturality _ _ f := closedSupportHom_globalSections_natural v f

/-- The component of the canonical section-pullback transformation.
Source: Stacks, Tag 03Q1 (blueprint: lem-amb-closed-support-hom). -/
theorem closedSupportSectionsPullback_app (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (closedSupportSectionsPullback A v).app J =
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary global derived Hom from `i_* A_D` is the shifted cone of restriction of
ordinary derived global sections to the complementary open. The existential `q` is fixed
in every degree by the existing global-section pullback map, so is not an arbitrary arrow.
The cone is computed on the functorial K-injective resolution, and the final equation is
naturality in every map of complexes. Both sides invert quasi-isomorphisms, hence this
also expresses naturality on the derived category. No boundedness is assumed.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-closed-support-hom.md
(blueprint: lem-amb-closed-support-hom).

Proof: Construct the restriction natural transformation on sheaves and map it to complexes.
The underived closed-support Hom sequence is short exact on each injective sheaf, so applying
it to the functorial resolution gives a short exact sequence of complexes. The explicit map
from its first term to the shifted cone is inclusion in the source summand. The existing
kernel-to-shifted-cone theorem proves it is a quasi-isomorphism, and the formula for cone maps
proves its naturality. The concrete K-injective computation of the right derived functor,
together with the resolution quasi-isomorphism, identifies the source with ordinary derived
Hom. Naturality of its unit, of the resolution, and of the shift comparison gives the stated
equation. This concrete formulation needs no separate derived computation of the open term.
-/
theorem closedSupportHom (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ) :
    ∃ q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ),
      (∀ (K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (n : ℤ), (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n)) ∧
      ∃ e : ∀ K : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).obj (DerivedCategory.Q.obj K) ≅
        (DerivedCategory.Q.obj (CochainComplex.mappingCone
          (q.app ((CochainComplex.kInjectiveResolutionFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj K))))⟦(-1 : ℤ)⟧,
      ∀ (K L : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (f : K ⟶ L),
        (((linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
          (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
            ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
              (ModuleCat.of A A))))).rightDerivedFunctor).map (DerivedCategory.Q.map f) ≫
          (e L).hom =
        (e K).hom ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u + 1} A)) (-1 : ℤ)).map
          (DerivedCategory.Q.map (CochainComplex.mappingCone.map _ _
            (((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
              ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (((upperStar (ModuleCat.{u + 1} A) v ⋙
              Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
                ((CochainComplex.kInjectiveResolutionFunctor _).map f))
            (q.naturality ((CochainComplex.kInjectiveResolutionFunctor _).map f)).symm)) := by
  let τ := closedSupportSectionsPullback A v
  let q : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).mapHomologicalComplex
          (ComplexShape.up ℤ) := NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)
  have hq : ∀ (K : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A)) ℤ) (n : ℤ),
      (q.app K).f n = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v (K.X n) := by
    intro K n
    exact NatTrans.mapHomologicalComplex_app_f τ (ComplexShape.up ℤ) K n
  let F := (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))))
  obtain ⟨α, hzero, hExact⟩ := closedSupportHomSequence A i v hcomp τ (fun _ ↦ rfl)
  refine ⟨q, hq, ?_⟩
  have : (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  have : (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).Additive :=
    (constantSheafΓAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)).right_adjoint_additive
  exact CategoryTheory.Functor.closedSupport_comparison F
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (upperStar (ModuleCat.{u + 1} A) v ⋙
      Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)) α τ hzero hExact

end AlgebraicGeometry.Etale
```

`Sheaf.AlgebraicGeometry.ClosedSupportHomSequence`:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.ConstructibleSheaf.Defs

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# The closed-support Hom sequence

The ordinary injective-sheaf exact sequence used in the derived closed-support comparison.
-/

@[expose] public section

attribute [local instance 200000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 200000] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The standard sheafification property, named before constructing the support maps.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasSheafify

/-- The same weak sheafification instance, with its proof fixed once on the site.
Source: Stacks, Tag 00W1 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasWeakSheafify (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasWeakSheafify

/-- Existence of the standard global-section adjunction, named once on the site.
Source: Stacks, Tag 009F (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleHasGlobalSections (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    HasGlobalSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A) := inferInstance

attribute [local instance 200000] closedSupportEtaleHasGlobalSections


/-- The canonical abelian structure, with pointwise addition on sheaf morphisms exposed.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleAbelian (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  { (inferInstance : Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) with
    toPreadditive := @Preadditive.fullSubcategory _ _
      (CategoryTheory.functorCategoryPreadditive (C := T.Etaleᵒᵖ)
        (D := ModuleCat.{u + 1} A)) _ }

/-- Exposing pointwise addition leaves the existing abelian structure unchanged.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleAbelian_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    closedSupportEtaleAbelian A T =
      (inferInstance : Abelian (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) := rfl

attribute [local instance 200000] closedSupportEtaleAbelian

/-- The existing linear structure on module sheaves, named for use in Hom functors.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
@[instance_reducible]
noncomputable def closedSupportEtaleLinear (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Linear A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance

/-- Naming the linear structure does not change scalar multiplication on sheaf maps.
Source: Stacks, Tag 03DA (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportEtaleLinear_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    closedSupportEtaleLinear A T =
      (inferInstance : Linear A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) := rfl

end AlgebraicGeometry.Etale

attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasWeakSheafify
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleHasGlobalSections
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleAbelian
attribute [local instance 200000] AlgebraicGeometry.Etale.closedSupportEtaleLinear

namespace CategoryTheory
private lemma restriction_unit_formula
    {C D E : Type*} [Category C] [Category D] [Category E]
    (U : C ⥤ D) (L : D ⥤ C) (B : C ⥤ E) (G : D ⥤ E)
    (adj : U ⊣ L) (b : L ⋙ B ≅ G) {P : C} {PV : D} {M : E}
    (c : U.obj P ≅ PV) (ηT : M ⟶ B.obj P) (ηV : M ⟶ G.obj PV)
    (h : ηT ≫ B.map (adj.unit.app P ≫ L.map c.hom) ≫ b.hom.app PV = ηV)
    {J : C} (f : P ⟶ J) :
    ηT ≫ B.map f ≫ B.map (adj.unit.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ G.map (c.inv ≫ U.map f) := by
  have hb : ηT ≫ B.map (adj.unit.app P) ≫ b.hom.app (U.obj P) =
      ηV ≫ G.map c.inv := by
    apply (cancel_mono (G.map c.hom)).mp
    simp only [Category.assoc, ← G.map_comp, c.inv_hom_id, Functor.map_id,
      Category.comp_id]
    rw [← b.hom.naturality]
    dsimp only [Functor.comp_map]
    rw [← B.map_comp_assoc]
    exact h
  have hn : f ≫ adj.unit.app J = adj.unit.app P ≫ L.map (U.map f) :=
    adj.unit.naturality f
  rw [← B.map_comp_assoc, hn, B.map_comp, Category.assoc]
  have hbn : B.map (L.map (U.map f)) ≫ b.hom.app (U.obj J) =
      b.hom.app (U.obj P) ≫ G.map (U.map f) := b.hom.naturality (U.map f)
  rw [hbn, reassoc_of% hb, G.map_comp]
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def adjunctionHomLinearEquiv
    (R : Type*) [Ring R] {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Linear R]
    (adj : F ⊣ G) (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homAddEquiv X Y
  map_smul' r f := by
    change adj.unit.app X ≫ G.map (r • f) = r • (adj.unit.app X ≫ G.map f)
    rw [Functor.map_smul, Linear.comp_smul]

end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def rankOneSectionsEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj J := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal
  have : ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (⊤_ T.Etale))).Linear A := adj.right_adjoint_linear
  let e : (((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) ≃ₗ[A]
      (ModuleCat.of A A ⟶ ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).obj J) :=
    CategoryTheory.adjunctionHomLinearEquiv A adj (ModuleCat.of A A) J
  exact (e.trans (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf A A _))).trans
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).app J).symm.toLinearEquiv

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
lemma rankOneSectionsEquiv_naturality (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {J J' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : J ⟶ J') (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    rankOneSectionsEquiv A T J' (f ≫ k) =
      (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
        (rankOneSectionsEquiv A T J f) := by
  change (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).inv.app J'
      (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).homEquiv _ _ (f ≫ k)) (1 : A)) =
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).map k
      ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).inv.app J
        (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
          terminalIsTerminal).homEquiv _ _ f) (1 : A)))
  rw [Adjunction.homEquiv_naturality_right]
  exact congrArg (fun g ↦ g
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).homEquiv _ _ f) (1 : A)))
    ((Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).inv.naturality k)

private lemma unit_app_upperStarConstantSheafIso (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T) (a : ModuleCat.{u + 1} A) :
    (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
        terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (op (⊤_ T.Etale))).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} A) v).map
            ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app a)) ≫
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.app _ =
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      terminalIsTerminal).comp (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)).ofNatIsoRight
      (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v))
    (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A) terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit] at this
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at this
  rw [← this, Scheme.upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v).hom.naturality]
  rfl

/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
lemma rankOneSections_restriction (A : Type (u + 1)) [CommRing A]
    {V T : Scheme.{u}} (v : V ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A)) ⟶ J) :
    globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J
      (rankOneSectionsEquiv A T J f) =
    rankOneSectionsEquiv A V ((upperStar (ModuleCat.{u + 1} A) v).obj J)
      (((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
        (ModuleCat.of A A)).inv ≫ (upperStar (ModuleCat.{u + 1} A) v).map f) := by
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  let U := upperStar (ModuleCat.{u + 1} A) v
  let B := (sheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ T.Etale))
  let C := (sheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (op (⊤_ V.Etale))
  let b := lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} A) v
  let c := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).unit
  let ηT := (constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  let ηV := (constantSheafAdj V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal).unit.app (ModuleCat.of A A)
  have hmap : ηT ≫ B.map f ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) =
      ηV ≫ C.map (c.inv ≫ U.map f) :=
    CategoryTheory.restriction_unit_formula U (lowerStar (ModuleCat.{u + 1} A) v) B C
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v) b c ηT ηV
        (unit_app_upperStarConstantSheafIso A v (ModuleCat.of A A)) f
  let eT := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  let eV := Sheaf.ΓNatIsoSheafSections V.smallEtaleTopology (ModuleCat.{u + 1} A)
    terminalIsTerminal
  have hr : (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J =
      ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J) := by
    change (ηT ≫ B.map f ≫ eT.inv.app J) ≫
      (eT.hom.app J ≫ B.map (η.app J) ≫ b.hom.app (U.obj J) ≫
        eV.inv.app (U.obj J)) = _
    simp only [Category.assoc, eT.inv_hom_id_app_assoc]
    rw [reassoc_of% hmap]
  change ((ηT ≫ B.map f ≫ eT.inv.app J) ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) (1 : A) =
    (ηV ≫ C.map (c.inv ≫ U.map f) ≫ eV.inv.app (U.obj J)) (1 : A)
  exact congrArg (fun g ↦ g (1 : A)) hr

end AlgebraicGeometry.Etale

namespace CategoryTheory
universe v u' w
variable {C : Type u'} [Category.{v} C] [Abelian C]
  (R : Type w) [Ring R] [Linear R C]
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
private noncomputable def linearHomShortComplex (S : ShortComplex C) (J : C) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (((linearCoyoneda R C).map S.g.op).app J)
    (((linearCoyoneda R C).map S.f.op).app J) (by
      ext x
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp])
/-- Canonical closed-support Hom and section normalization.
Source: Stacks, Tags 0A45, 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
private lemma linearHomShortComplex_shortExact (S : ShortComplex C) (hS : S.ShortExact)
    (J : C) [Injective J] : (linearHomShortComplex R S J).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · intro y
    constructor
    · intro h
      obtain ⟨x, hx⟩ := CokernelCofork.IsColimit.desc' hS.gIsCokernel y h
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      change S.f ≫ S.g ≫ x = 0
      rw [← Category.assoc, S.zero, zero_comp]
  · intro x y hxy
    exact (cancel_epi S.g).1 hxy
  · intro z
    exact ⟨Injective.factorThru z S.f, Injective.comp_factorThru z S.f⟩
end CategoryTheory

namespace AlgebraicGeometry.Etale
/-- The closed constant sheaf from which supported Hom is taken.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomSource (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj
    ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))

/-- The named source is exactly the direct image of the rank-one constant sheaf.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence). -/
theorem closedSupportHomSource_eq (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    closedSupportHomSource A i = (lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) := rfl

/-- The ordinary Hom functor used by the canonical closed-support sequence.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomFunctor (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
    (op (closedSupportHomSource A i))

/-- The closed-support Hom functor is additive.
Source: Stacks, Tag 0A45 (blueprint: new-lem-amb-closed-support-hom-sequence). -/
instance closedSupportHomFunctor_additive (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) : (closedSupportHomFunctor A i).Additive := by
  dsimp only [closedSupportHomFunctor]
  infer_instance

/-- The canonical left map of the closed-support Hom sequence.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence). -/
noncomputable def closedSupportHomToSections (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    closedSupportHomFunctor A i ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let g := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom
  exact
    { app J := ModuleCat.ofHom ((rankOneSectionsEquiv A T J).toLinearMap.comp
        (Linear.leftComp A J g))
      naturality J J' k := by
        ext f
        change rankOneSectionsEquiv A T J' (g ≫ f ≫ k) = _
        rw [← Category.assoc, rankOneSectionsEquiv_naturality]
        rfl }

/-- The exact sequence with its left map fixed as evaluation after the closed unit.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence).

Apply Hom into an injective sheaf to the open–closed short exact sequence. Evaluation at
one identifies the middle term with global sections. Extension-by-zero adjunction
identifies the last term with sections on the open, and the counit formula identifies
its map with restriction. The left map is the explicit `closedSupportHomToSections`,
so its normalization is retained instead of hidden by an existential choice. -/
theorem closedSupportHomSequenceNormalized (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∃ (hzero : ∀ J, (closedSupportHomToSections A i).app J ≫ τ.app J = 0),
      ∀ J, Injective J →
        (ShortComplex.mk ((closedSupportHomToSections A i).app J) (τ.app J)
          (hzero J)).ShortExact := by
  classical
  let P := (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
    (ModuleCat.of A A)
  have hicomp : Set.range i.base = (Set.range v.base)ᶜ := by
    rw [hcomp, compl_compl]
  let S := openClosedShortComplex (ModuleCat.{u + 1} A) v i
    (disjoint_range_of_range_eq_compl v i hicomp) P
  have hS : S.ShortExact := shortExact_openClosedShortComplex
    (ModuleCat.{u + 1} A) v i P hicomp
  let c := (lowerStar (ModuleCat.{u + 1} A) i).mapIso
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app (ModuleCat.of A A))
  let g := S.g ≫ c.hom
  let α := closedSupportHomToSections A i
  let U := upperStar (ModuleCat.{u + 1} A) v
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
  have : U.Linear A := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).left_adjoint_linear
  let d := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)
  let e₃ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (S.X₁ ⟶ J) ≃ₗ[A] (Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (U.obj J) :=
    (CategoryTheory.adjunctionHomLinearEquiv A a (U.obj P) J).trans
      ((Linear.homCongr A d (Iso.refl (U.obj J))).trans
        (rankOneSectionsEquiv A V (U.obj J)))
  have hβ (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (f : P ⟶ J) :
      τ.app J (rankOneSectionsEquiv A T J f) = e₃ J (S.f ≫ f) := by
    rw [hτ]
    erw [rankOneSections_restriction]
    dsimp only [e₃, LinearEquiv.trans_apply, Linear.homCongr_apply]
    apply congrArg (rankOneSectionsEquiv A V (U.obj J))
    change d.inv ≫ U.map f = d.inv ≫ a.homEquiv _ _ (a.counit.app P ≫ f)
    rw [Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_symm_id]
    erw [Equiv.apply_symm_apply, Category.id_comp]
  have hzero (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      α.app J ≫ τ.app J = 0 := by
    ext f
    change τ.app J (rankOneSectionsEquiv A T J (g ≫ f)) = 0
    rw [hβ]
    have hz : S.f ≫ g ≫ f = 0 := by
      dsimp only [g]
      rw [← Category.assoc, ← Category.assoc, S.zero, zero_comp, zero_comp]
    rw [hz, map_zero]
  refine ⟨hzero, ?_⟩
  intro J hJ
  let := hJ
  let e₁ := (Linear.homCongr A c (Iso.refl J)).toModuleIso
  let e₂ := (rankOneSectionsEquiv A T J).toModuleIso
  let e := ShortComplex.isoMk (S₁ := CategoryTheory.linearHomShortComplex A S J)
    (S₂ := ShortComplex.mk (α.app J) (τ.app J) (hzero J))
    e₁ e₂ (e₃ J).toModuleIso (by
      ext f
      change rankOneSectionsEquiv A T J (g ≫ ((c.inv ≫ f) ≫ 𝟙 J)) =
        rankOneSectionsEquiv A T J (S.g ≫ f)
      simp [g]) (by
      ext f
      exact hβ J f)
  exact ShortComplex.shortExact_of_iso e
    (CategoryTheory.linearHomShortComplex_shortExact A S hS J)

/-- The canonical support map followed by restriction is zero.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence).

Take the zero-composite proof from the canonical short exact sequence. Its witness is a
proof, so this exposes no new choice of map or object. -/
theorem closedSupportHomToSections_comp (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∀ J, (closedSupportHomToSections A i).app J ≫ τ.app J = 0 :=
  (closedSupportHomSequenceNormalized A i v hcomp τ hτ).choose

/-- Exactness on injectives, using the named canonical zero-composite proof.
Source: Stacks, Tag 095L (blueprint: new-lem-amb-closed-support-hom-sequence).

Apply exactness of the normalized sequence. Proof irrelevance identifies its witness of
the zero composite with the named witness, without changing either map. -/
theorem closedSupportHomSequence_shortExact (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∀ J, Injective J →
      (ShortComplex.mk ((closedSupportHomToSections A i).app J) (τ.app J)
        (closedSupportHomToSections_comp A i v hcomp τ hτ J)).ShortExact :=
  (closedSupportHomSequenceNormalized A i v hcomp τ hτ).choose_spec

/-- The component formula for the fixed map of the support sequence.
Source: Stacks, Tags 095L, 0A45
(blueprint: new-lem-amb-closed-support-hom-sequence).

The map was constructed by precomposing with the closed constant unit and then applying
rank-one evaluation. The displayed equation is exactly that construction. -/
theorem closedSupportHomToSections_apply (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T)
    (J : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : (lowerStar (ModuleCat.{u + 1} A) i).obj
      ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A)) ⟶ J) :
    (closedSupportHomToSections A i).app J c = rankOneSectionsEquiv A T J
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
          (ModuleCat.of A A)).hom ≫ c) := rfl

/-- Maps out of the closed constant sheaf form the kernel of restriction on an
injective sheaf, naturally in the target sheaf.

Source: Stacks Project, Etale Cohomology Tag 095L (the open–closed exact sequence),
Modules on Sites Tag 03DI (extension by zero and its adjunction), and
literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-amb-closed-support-hom.md, proof steps 1 and 3.
(blueprint: new-lem-amb-closed-support-hom-sequence).

Proof: Apply the open–closed short exact sequence to the constant rank-one sheaf A_T.
The canonical inverse-image identifications give the sequence
0 → v_! A_V → A_T → i_* A_D → 0, whose maps are the counit and unit.
Precomposition with the last map, followed by the identification
Hom(A_T,J) ≅ Γ(T,J) sending a morphism to the image of 1, defines α.
Associativity of composition proves naturality in J. The extension-by-zero
adjunction identifies Hom(v_! A_V,J) with Γ(V,v^*J), and the counit formula
identifies precomposition with the first map with the prescribed τ.
The composite is zero because the open–closed sequence is a complex.
Precomposition with its epimorphism is injective; a map from A_T which vanishes
on v_! A_V factors uniquely through the cokernel i_* A_D. This is exactness
at Γ(T,J). When J is injective, every map v_! A_V → J extends across the
monomorphism v_! A_V → A_T, so τ is surjective. These arguments include the
empty open or closed scheme and the zero coefficient ring. -/
theorem closedSupportHomSequence (A : Type (u + 1)) [CommRing A]
    {D V T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (v : V ⟶ T) [IsOpenImmersion v]
    (hcomp : Set.range v.base = (Set.range i.base)ᶜ)
    (τ : Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) v ⋙
        Sheaf.Γ V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hτ : ∀ J, τ.app J = globalSectionsUpperStarMap (ModuleCat.{u + 1} A) v J) :
    ∃ (α : (linearCoyoneda A (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).obj
        (op ((lowerStar (ModuleCat.{u + 1} A) i).obj
          ((constantSheaf D.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A)))) ⟶ Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (hzero : ∀ J, α.app J ≫ τ.app J = 0),
      ∀ J, Injective J → (ShortComplex.mk (α.app J) (τ.app J) (hzero J)).ShortExact := by
  obtain ⟨hzero, hα⟩ := closedSupportHomSequenceNormalized A i v hcomp τ hτ
  exact ⟨closedSupportHomToSections A i, hzero, hα⟩

end AlgebraicGeometry.Etale
```

## Users

Direct importers and declaration users were checked with `tools/downstream.py` and text
searches. No original consumer uses the changed concrete record constructors or fields.
No consumer statement needs adaptation. The supporting modules retain all existing public
theorem signatures. All five original consumer files compile against the new compiled APIs. Four are
quarantined originals, preserved at their existing archive paths. Their temporary
compilation copies are not delivered. The assigned theorem and both original supporting
theorems have only `propext`, `Classical.choice` and `Quot.sound` as axioms.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | E1 | Proved; equivalent generic model and pullback interfaces. |
| Sheaf.AlgebraicGeometry.ClosedSupportHom | unclaimed | Expose existing proved helpers; public theorem unchanged. |
| Sheaf.AlgebraicGeometry.ClosedSupportHomSequence | unclaimed | Expose existing rank-one helpers and canonical sequence; original theorem unchanged. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 | Imports the item and ClosedSupportHom; no use of changed data constructors. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Imports ClosedSupportHom; original theorem unchanged. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Imports ClosedSupportHom; original theorem unchanged. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Imports ClosedSupportHom; original theorem unchanged. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Imports ClosedSupportHom; original theorem unchanged. |

## Status

landed 20261020T235554-L-1190593 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality)
