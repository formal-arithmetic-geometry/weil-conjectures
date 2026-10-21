/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.AllContinuousScalarMate
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.Paper.DerivedExchangeExactNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.SubterminalDerivedImageCalculus
import Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel

/-!
# Transverse tame open shriek/star exchange

Source: blueprint main-20261015, direct-image stability proof, paragraph (3), additional
all-continuous tame-boundary input (blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

The comparison is the actual open-slice exchange followed by the inverse open unit,
then adjunction under c_! and c^*. Coefficients use all continuous functions into the
norm-topological algebraic closure.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.TransverseTame

open CondensedRing

/-- Internal modules with the coefficient pulled back from the point.
Source: explicit ambient categories in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
abbrev Modules (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The open adjunction unit is invertible, also on unbounded derived categories.
Source: the open-slice normalization in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof: the underived extension by zero is fully faithful, since restriction recovers
its sections. Its unit is therefore invertible. Exactness of both functors carries this
unit termwise to complexes, and localization preserves its inverse. -/
@[instance] theorem openUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Modules Λ U)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit.app K) := by
  sorry

variable {W V O Y : Scheme.{u}} {b : W ⟶ V} {a : W ⟶ O}
  {j : V ⟶ Y} {c : O ⟶ Y}
  [IsOpenImmersion b] [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c]

/-- The canonical slice restriction c^* Rj_* b_! K -> Ra_* K. The last factor removes
b^* b_! by the inverse of its actual open adjunction unit.
Source: canonical map paragraph of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def restrictionComparison (sq : CommSq b a j c) (K : DerivedCategory (Modules Λ W)) :
    (CondensedRing.upperStar Λ c).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ j).obj
          ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.obj K)) ⟶
      (moduleObjectDerivedPushforward Λ a).obj K :=
  (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ c).inv.app _ ≫
    (moduleObjectDerivedExchange Λ sq).app _ ≫
    (moduleObjectDerivedPushforward Λ a).map
      ((leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ b).hom.app _ ≫
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ b).unit.app K))

/-- Restriction to an open slice identifies the two direct images canonically.
Source: canonical map paragraph of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof: the site pullback square is the sectionwise fibre-product identity of
lem-sfb-proetale-open-restriction-counit. Its derived comparison is obtained on
K-injective representatives by lem-sfb-kinjective-direct-image-open-word-model.
The exchange is that comparison by its unit/counit normalization. The remaining
factor is the invertible open unit, giving the assertion. -/
@[instance] theorem restrictionComparison_isIso (sq : IsPullback b a j c)
    (K : DerivedCategory (Modules Λ W)) :
    IsIso (restrictionComparison Λ sq.toCommSq K) := by
  sorry

/-- The prescribed exchange, the adjunct of the inverse slice comparison.
Source: displayed definition of e_F in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def exchange (sq : IsPullback b a j c) (K : DerivedCategory (Modules Λ W)) :
    (CondensedRing.openImmersionLowerShriek Λ c).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ a).obj K) ⟶
      (moduleObjectDerivedPushforward Λ j).obj
        ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.obj K) :=
  letI := restrictionComparison_isIso Λ sq K
  (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c).homEquiv _ _ |>.symm
    (inv (restrictionComparison Λ sq.toCommSq K))

/-- Naturality is with respect to actual derived module morphisms.
Source: naturality clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof: exchange, both exact/derived comparison isomorphisms, and the open unit
are natural. Inverting their isomorphisms preserves naturality. The adjunction
bijection is natural in both arguments, yielding the equation below. -/
theorem exchange_naturality (sq : IsPullback b a j c)
    {K K' : DerivedCategory (Modules Λ W)} (f : K ⟶ K') :
    (CondensedRing.openImmersionLowerShriek Λ c).mapDerivedCategory.map
        ((moduleObjectDerivedPushforward Λ a).map f) ≫ exchange Λ sq K' =
      exchange Λ sq K ≫ (moduleObjectDerivedPushforward Λ j).map
        ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.map f) := by
  sorry

/-- A chosen presentation of the finite family in the recorded SNC definition, and a
partition of precisely that family. The equations are the witness fields of the definition,
not extra regularity assumptions.
Source: SNC family and partition in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
structure Boundary (Y : Scheme.{u}) where
  divisor : Y.IdealSheafData
  snc : IsStrictNormalCrossingsBoundary divisor
  n : ℕ
  component : Fin n → Y.IdealSheafData
  distinct : Function.Injective (fun i ↦ (component i).support)
  regular : ∀ i, IsIntegral (component i).subscheme ∧ IsRegularScheme (component i).subscheme
  union_eq : divisor.support = ⨆ i, (component i).support
  intersections : ∀ s : Finset (Fin n), ∀ z : (⨆ i ∈ s, component i).subscheme,
    IsRegularScheme ((⨆ i ∈ s, component i).subscheme) ∧
    ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ s, component i).subschemeι z)) =
      ringKrullDim ((⨆ i ∈ s, component i).subscheme.presheaf.stalk z) + (s.card : ℕ)
  outer : Finset (Fin n)

/-- Complement of the entire boundary.
Source: W in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def Boundary.complement {Y : Scheme.{u}} (B : Boundary Y) : Y.Opens := B.divisor.support.compl

/-- The outer complement.
Source: V in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def Boundary.outerOpen {Y : Scheme.{u}} (B : Boundary Y) : Y.Opens :=
  (⨆ i ∈ B.outer, (B.component i).support).compl

/-- The inner complement; membership in the inner part is complementary to outer membership.
Source: Y-circle in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def Boundary.innerOpen {Y : Scheme.{u}} (B : Boundary Y) : Y.Opens :=
  (⨆ i ∈ B.outerᶜ, (B.component i).support).compl

/-- The all-continuous coefficient object. At coefficient universe zero this is
definitionally the recorded universe-polymorphic continuous-map object.
Source: coefficient convention of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
abbrev continuousCoefficients (F : Type) [TopologicalSpace F] [CommRing F]
    [IsTopologicalRing F] : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  Profinite.continuousMapRingObj F

section Scalars

variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (α : Λ ⟶ Λ') [IsMonHom α]

/-- Exact restriction of scalars on the actual unbounded derived categories.
Source: scalar-restriction clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
abbrev scalarRestriction (X : Scheme.{u}) :
    DerivedCategory (Modules Λ' X) ⥤ DerivedCategory (Modules Λ X) :=
  (Mod.comap (coefficientMap α X)).mapDerivedCategory

/-- The canonical direct-image/scalar-restriction comparison. It is derived from the
ordinary identity on sections and normalized by the right-derived units; in particular
its construction does not require restriction to preserve K-injectives.
Source: scalar-restriction clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def directScalarMap {X T : Scheme.{u}} (f : X ⟶ T) :
    moduleObjectDerivedPushforward Λ' f ⋙ scalarRestriction Λ α T ⟶
      scalarRestriction Λ α X ⋙ moduleObjectDerivedPushforward Λ f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (CondensedRing.lowerStar Λ' f) (Mod.comap (coefficientMap α T))).inv ≫
  (Functor.rightDerivedFunctorNatIso (comapLowerStarIso α f)).hom ≫
  Functor.rightDerivedPullback (Mod.comap (coefficientMap α X))
    (𝟙 (Mod.comap (coefficientMap α X) ⋙ CondensedRing.lowerStar Λ f))

/-- The canonical comparison is invertible. This is ordinary scalar restriction,
not scalar extension past a direct image.
Source: scalar-restriction identifications of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof: apply lem-weil-pbc-ring-sheaf-change-adjunction to the section-ring sheaves
corresponding to the internal coefficient objects under
 def-weil-pbc-internal-abelian-sheaf-module-equivalence. Its canonical derived comparison
is invertible and preserves right-derived units. The ordinary comparison here is the
same identity on sections. Uniqueness of the right-derived transformation therefore
identifies it with directScalarMap. This uses no flatness or preservation of
K-injectives by scalar restriction. -/
@[instance] theorem directScalarMap_isIso {X T : Scheme.{u}} (f : X ⟶ T) :
    IsIso (directScalarMap Λ α f) := by
  sorry

/-- Extension by zero commutes with restriction of scalars, by the canonical
sectionwise linearization, followed by passage to exact derived functors.
Source: scalar-restriction clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def shriekScalarIso {X T : Scheme.{u}} (f : X ⟶ T) [IsOpenImmersion f] :
    (CondensedRing.openImmersionLowerShriek Λ' f).mapDerivedCategory ⋙
        scalarRestriction Λ α T ≅
      scalarRestriction Λ α X ⋙
        (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (CondensedRing.openImmersionLowerShriek Λ' f) (Mod.comap (coefficientMap α T))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comapOpenImmersionLowerShriekIso α f) ≪≫
    Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap α X))
      (CondensedRing.openImmersionLowerShriek Λ f)

/-- The ordinary identifications on the source of exchange.
Source: scalar-restriction clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def sourceScalarIso (a : W ⟶ O) (c : O ⟶ Y) [IsOpenImmersion c]
    (K : DerivedCategory (Modules Λ' W)) :
    (scalarRestriction Λ α Y).obj
        ((CondensedRing.openImmersionLowerShriek Λ' c).mapDerivedCategory.obj
          ((moduleObjectDerivedPushforward Λ' a).obj K)) ≅
      (CondensedRing.openImmersionLowerShriek Λ c).mapDerivedCategory.obj
        ((moduleObjectDerivedPushforward Λ a).obj ((scalarRestriction Λ α W).obj K)) :=
  (shriekScalarIso Λ α c).app _ ≪≫
    (CondensedRing.openImmersionLowerShriek Λ c).mapDerivedCategory.mapIso
      ((asIso (directScalarMap Λ α a)).app K)

/-- The ordinary identifications on the target of exchange.
Source: scalar-restriction clause of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def targetScalarIso (b : W ⟶ V) (j : V ⟶ Y) [IsOpenImmersion b]
    (K : DerivedCategory (Modules Λ' W)) :
    (scalarRestriction Λ α Y).obj
        ((moduleObjectDerivedPushforward Λ' j).obj
          ((CondensedRing.openImmersionLowerShriek Λ' b).mapDerivedCategory.obj K)) ≅
      (moduleObjectDerivedPushforward Λ j).obj
        ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.obj
          ((scalarRestriction Λ α W).obj K)) :=
  (asIso (directScalarMap Λ α j)).app _ ≪≫
    (moduleObjectDerivedPushforward Λ j).mapIso ((shriekScalarIso Λ α b).app K)

/-- The scalar unit is precisely x mapping to 1 tensor x, inserted in degree zero
and identified with exact restriction of scalars by its canonical single-functor iso.
Source: explicit scalar map in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def scalarUnit (L : Modules Λ W) :
    (DerivedCategory.singleFunctor _ 0).obj L ⟶
      (scalarRestriction Λ α W).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap α W)).obj L)) :=
  (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap α W)).unit.app L) ≫
    (Functor.mapDerivedCategorySingleFunctor
      (Mod.comap (coefficientMap α W) : Modules Λ' W ⥤ Modules Λ W) 0).inv.app _

/-- Scalar compatibility for the prescribed map, including its normalization under
restriction of scalars. It applies to the actual scalar unit, and more generally every
map K -> Res K'.
Source: naturality and coefficient square in the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof: ordinary restriction leaves extension-by-zero sections and their adjunction
units and counits unchanged. The open-slice comparison is the sectionwise fibre-product
identity. The derived right-unit normalization of directScalarMap transports this
identity to K-injective resolutions, by lem-sfb-kinjective-direct-image-open-word-model.
Consequently the inverse restriction comparison and its c_! adjunct commute with
scalar restriction. Compose with exchange_naturality for μ to obtain the equation.
For μ=scalarUnit this is exactly x mapping to 1 tensor x. -/
theorem exchange_scalar (sq : IsPullback b a j c)
    {K : DerivedCategory (Modules Λ W)} {K' : DerivedCategory (Modules Λ' W)}
    (μ : K ⟶ (scalarRestriction Λ α W).obj K') :
    (CondensedRing.openImmersionLowerShriek Λ c).mapDerivedCategory.map
        ((moduleObjectDerivedPushforward Λ a).map μ) ≫
      (sourceScalarIso Λ α a c K').inv ≫
      (scalarRestriction Λ α Y).map (exchange Λ' sq K') ≫
      (targetScalarIso Λ α b j K').hom =
    exchange Λ sq K ≫
      (moduleObjectDerivedPushforward Λ j).map
        ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.map μ) := by
  sorry

end Scalars

/-- The two geometric conclusions for one coefficient: the prescribed exchange is
invertible and its target has zero restriction to the whole reduced inner boundary.
Source: isomorphism and inner-boundary vanishing clauses of the tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange). -/
def ExchangeAt (sq : IsPullback b a j c) (L : Modules Λ W) : Prop :=
  IsIso (exchange Λ sq ((DerivedCategory.singleFunctor _ 0).obj L)) ∧
    IsZero ((CondensedRing.upperStar Λ c.closedComplement).mapDerivedCategory.obj
      ((moduleObjectDerivedPushforward Λ j).obj
        ((CondensedRing.openImmersionLowerShriek Λ b).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj L))))

/-- Transverse tame exchange for both all-continuous coefficient rings, with vanishing
on the inner boundary, including its intersections with outer components.
Source: blueprint main-20261015, direct-image proof (3), additional tame-boundary input
(blueprint: lem-sfb-transverse-tame-open-shriek-exchange).

Proof (the nine steps of the DAG):
1. Use the internal-module/section-ring equivalence to apply the published exact
open and closed inverse images, direct images and extension by zero. The coefficient
objects are pulled back from the point, including all continuous Omega-valued maps.
2. On V put K=Rb_*L_F[0]. The open/closed localization triangle is
b_!L_F[0] -> K -> h_*h^*K ->, with the actual closed unit as second arrow.
3. Apply Rj_* and restrict to the reduced inner boundary. Exactness of the derived
functors reduces vanishing to invertibility of the restriction of the closed-unit map.
4. On a stratum meeting the inner boundary, the partial Kummer boundary unit model
identifies that map, on a pro-etale covering, with derived invariants for Go times Gi
followed by successive Gi and Go invariants. Inflation is exact and its composite is
product inflation (lem-sfb-condensed-product-action-inflation). The normalized derived
composition adjunction identifies the specified comparison with an isomorphism.
5. The cover detects isomorphisms by lem-zl-condensed-cover-restriction-conservative.
6. Filter the inner boundary by closed unions of component intersections. The closure
of each stratum contains only strata with more branches. Finite induction using
lem-sfb-exact-open-closed-unbounded-calculus gives zero restriction on the entire
inner boundary for Rj_*b_!L_F[0]. This includes all inner/outer intersections.
7. Open-slice restriction is restrictionComparison. The c_! adjunct of its inverse
is exchange. Recollement says its counit is invertible because the closed restriction
vanishes. Thus exchange is invertible with the prescribed normalization.
8. Naturality and scalar compatibility are exchange_naturality and exchange_scalar,
with scalarUnit the actual x mapping to 1 tensor x. Scalar restriction leaves the
sectionwise comparisons unchanged; no scalar extension is moved past Rj_*.
9. Empty outer or inner sets, empty divisor and rank zero follow from the same
construction; there are no boundary strata when the inner boundary is empty.
-/
theorem transverse_tame_open_shriek_exchange
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (_hY : IsRegularScheme Y) (B : Boundary Y)
    (W V O : Scheme.{u})
    (b : W ⟶ V) (a : W ⟶ O) (j : V ⟶ Y) (c : O ⟶ Y)
    [IsOpenImmersion b] [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c]
    (_hW : Set.range (b ≫ j) = (B.complement : Set Y))
    (_hV : Set.range j = (B.outerOpen : Set Y))
    (_hO : Set.range c = (B.innerOpen : Set Y))
    (sq : IsPullback b a j c)
    (L : Modules (continuousCoefficients E) W)
    (_hL : IsLisseCoefficientModule (continuousCoefficients E) L)
    (_htame : IsStrictLocalKummerTameModule p (continuousCoefficients E)
      B.divisor (b ≫ j) L) :
    ExchangeAt (continuousCoefficients E) sq L ∧
      ExchangeAt (continuousCoefficients (PadicAlgCl ℓ)) sq
        ((Mod.extendScalars (coefficientMap (tameBoundaryScalarMap ℓ E) W)).obj L) := by
  sorry

end AlgebraicGeometry.ProEtale.TransverseTame
