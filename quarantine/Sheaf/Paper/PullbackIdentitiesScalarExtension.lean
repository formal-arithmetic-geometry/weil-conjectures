/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
public import Sheaf.Paper.IsomorphismDerivedPullback
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IsomorphismComparisonScalarExtension
import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # Scalar extension and the normalized pullback identities

Source: blueprint main-20261015, sec-six-functors/sk-rem-sf-pf-done,
lem-fix-weil-operations.proof.md, first paragraph, pullback and inverse automorphism squares
(blueprint: lem-pod-pullback-identities-scalar-extension).

The compositor and scalar comparison are the whole-system realization maps. The inverse
identity uses the inverse of the specified quotient-cone kappa, followed by the
section-normalized inverse-image counit. No natural isomorphism is supplied arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The site identification of successive postcomposition by the inverse and by g.
Its arrows are identity on the underlying schemes. Source: Stacks 09A5 and 03D6;
blueprint inverse automorphism squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentitySiteUnit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    𝟭 Y.ProEt ≅ proEtaleIsoPostcompose (inv g) ⋙ proEtaleIsoPostcompose g :=
  (MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ Y (inv g ≫ g)
    (IsIso.inv_hom_id g)).symm ≪≫
      MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale (inv g)) (inferInstance : WeaklyEtale g)

/-- The inverse-image counit is uniquely fixed by its value on every section.
Source: Stacks 09A5, 03D6; blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof: postcompose structure maps first with inv g and then g. The displayed site
unit identifies the result with the original object by the identity on its scheme.
Constant-section maps respect this identification at every finite quotient; their
limit projection equations give the same fact for completed coefficients. Thus the
restriction in the formula is linear for the transported actions. Its inverse is
restriction along the inverse site arrow. Restrictions commute with module maps,
so these maps form a natural isomorphism. Sectionwise equality proves uniqueness. -/
theorem pullbackIdentityModuleCounit_existsUnique
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! e : inverseImageIntegralModules l E g ⋙ inverseImageIntegralModules l E (inv g) ≅
        𝟭 (integralTowerModules l E Y),
      ∀ (M : integralTowerModules l E Y) (U : Y.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj
          ((proEtaleIsoPostcompose (inv g)).obj U)))),
        (e.hom.app M).val.app (op U) x =
          M.val.map ((pullbackIdentitySiteUnit g).hom.app U).op x := by
  sorry

/-- The uniquely section-normalized module counit. Source: Stacks 09A5, 03D6;
blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityModuleCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :=
  (pullbackIdentityModuleCounit_existsUnique l E g).exists.choose

/-- Apply the section-normalized counit termwise and localize, including the exact
functor composition and identity comparisons. Source: Stacks 03D6, 05RU;
blueprint inverse automorphism identity
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityInverseImageCounit {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    inverseImageIntegralDerived l E g ⋙ inverseImageIntegralDerived l E (inv g) ≅
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E g)
    (inverseImageIntegralModules l E (inv g))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (pullbackIdentityModuleCounit l E g) ≪≫
        Functor.mapDerivedCategoryIdIso _

/-- Kappa is invertible on exactly the constructible complete inputs in the node.
Source: blueprint inverse squares; normalization of the specified cone map
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof: apply lem-weil-isomorphism-derived-pullback-comparison-normalization to the
canonical reduction/limit calculus of lem-coef-derived-system-evaluation-calculus.
The intrinsic constructible predicate includes derived completeness. The normalization
identifies kappa followed by theta with inverse image of the completion unit. That unit
is invertible on complete objects, so the displayed kappa has a two-sided inverse. -/
theorem pullbackIdentityKappa_isIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso (inverseImagePullbackComparisonDerived l E g hX hY K.obj) := by
  sorry

/-- Lambda is the inverse of the specified quotient-cone kappa, rather than an
unspecified isomorphism with the same endpoints. Source: blueprint inverse squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityLambda
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l E g).obj K.obj ≅
      (inverseImageIntegralDerived l E g).obj K.obj :=
  letI := pullbackIdentityKappa_isIso l E g hX hY K
  (asIso (inverseImagePullbackComparisonDerived l E g hX hY K.obj)).symm

/-- The inverse identity epsilon is lambda for inv g, inverse image of lambda for g,
then the canonical inverse-image counit, in that order. Source: blueprint inverse squares
(blueprint: lem-pod-pullback-identities-scalar-extension). -/
def pullbackIdentityEpsilon
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    (integralDerivedPullback l E (inv g)).obj
        ((integralDerivedPullback l E g).obj K.obj) ≅ K.obj :=
  let hX := fun x : X ↦ isUnit_of_map_unit (IsLocalRing.residue (X.presheaf.stalk x)) _
    ((map_natCast (IsLocalRing.residue (X.presheaf.stalk x)) l).symm ▸
      isUnit_of_invertible (l : X.residueField x))
  let hY := fun y : Y ↦ isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
    ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
      isUnit_of_invertible (l : Y.residueField y))
  pullbackIdentityLambda l E (inv g) hY hX
      ((constructibleIntegralPullback l E g).obj K) ≪≫
    (inverseImageIntegralDerived l E (inv g)).mapIso
      (pullbackIdentityLambda l E g hX hY K) ≪≫
    (pullbackIdentityInverseImageCounit l E g).app K.obj

/-- Composition and inverse identities commute with integral scalar extension, for the
specified whole-system comparison families. Source: blueprint main-20261015,
sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-pullback-identities-scalar-extension).

Proof, following the node:
1. Apply lem-trf-integral-pullback-comparison-realization to E into L, h, k and K.
Its entire quotient-diagram scalar/composition equation is the first conjunct.
The composition and scalar maps here are exactly its counit-built families.
2. For an isomorphism g write P=Lg*, Q=L(inv g)*, G=g-inverse and H=(inv g)-inverse.
The inverse images are exact site equivalences and preserve the required domains
(lem-weil-proetale-isomorphism-inverse-image, lem-weil-isomorphism-derived-pullback).
The normalization lemma inverts the specified kappa. Thus lambda=kappa inverse
and epsilon=u H(lambda) lambda, with u the section-normalized inverse-image counit.
3. Lem-weil-isomorphism-comparison-scalar-extension gives the kappa/scalar square.
Lem-pod-isomorphism-scalar-comparison-agreement identifies its tensor/completion alpha
with the whole-system alpha used here, for both g and inv g. Cancel the invertible
kappas to obtain lambda_L alpha = beta T(lambda_E), for both isomorphisms.
4. Write C for ordinary derived coefficient change and chi:C iso T for the specified
finite-free completed comparison. Beta=G(chi) b chi inverse. The sectionwise tensor
map b only reindexes x tensor a. Reindexing by g and inv g returns x and a unchanged.
Consequently u_L H(b_g) b_inv = C(u_E), already on complexes, and hence after
sheafification and localization. Substitution cancels the adjacent chi inverses;
naturality of u and chi gives u_L H(beta_g) beta_inv = T(u_E).
5. Expand epsilon_L. Naturality of lambda for inv g and step 3 replace the two lambdas
by beta T(lambda_E). Naturality of beta_inv moves T(lambda_g) past beta_inv.
Step 4 replaces the initial three factors by T(u_E). Functoriality of T combines
the remaining factors to T(epsilon_E). This is the second conjunct, as an equality
of whole derived arrows; no finite-reduction detection or Tor-amplitude bound is used. -/
theorem pullbackIdentities_scalarExtension
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : IntegralComparisonSystem.{u} l) :
    (∀ {V W Z : Scheme.{u}}
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)]
      [∀ z : Z, Invertible (l : Z.residueField z)]
      (h : Z ⟶ W) (k : W ⟶ V) (K : sfIntegralConstructibleCategory l E V),
      (integralScalarExtensionOfUniverses l E L ι Z).map
          (integralComparisonComposition l E D h k K).hom ≫
        (integralComparisonScalar l E L ι D h
          ((constructibleIntegralPullback l E k).obj K)).hom ≫
        (integralDerivedPullback l L h).map
          (integralComparisonScalar l E L ι D k K).hom =
      (integralComparisonScalar l E L ι D (h ≫ k) K).hom ≫
        (integralComparisonComposition l L D h k
          ((integralComparisonConstructibleScalar l E L ι V).obj K)).hom) ∧
    (∀ {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
      [∀ x : X, Invertible (l : X.residueField x)]
      [∀ y : Y, Invertible (l : Y.residueField y)]
      (K : sfIntegralConstructibleCategory l E Y),
      (integralComparisonScalar l E L ι D (inv g)
          ((constructibleIntegralPullback l E g).obj K)).hom ≫
        (integralDerivedPullback l L (inv g)).map
          (integralComparisonScalar l E L ι D g K).hom ≫
        (pullbackIdentityEpsilon l L g
          ((integralComparisonConstructibleScalar l E L ι Y).obj K)).hom =
      (integralScalarExtensionOfUniverses l E L ι Y).map
        (pullbackIdentityEpsilon l E g K).hom) := by
  sorry

end WeilConjectures
