/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.Paper.OrientedConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.Paper.OrientedProductPointsConservative
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Constructible
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.TraceFormula.FiniteCoverTubeComparison

/-!
# Extension of oriented nearby cycles from a closed base

Source: Orgogozo, Modifications et cycles proches sur une base générale, §§3.2, 9.2,
printed pp. 7--8, 21--22; ILO XI §§1.4, 2, 4.3; Stacks 08LY--08M1
(blueprint: lem-trf-oriented-closed-base-extension).

The auxiliary maps normalize identity base change, transport to the recorded
constructibility presentation, and specify the unit--counit comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AdicSites
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles.ClosedBase

/-- Identity base change, normalized by the first fibre-product projection.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension).
Proof: the first projection of the pullback along an identity is an isomorphism,
with inverse the diagonal pair. These isomorphisms commute with etale maps.
The faithful forgetful functor to schemes detects the displayed uniqueness. -/
theorem etaleIdentity_existsUnique (S : Scheme.{u}) :
    ∃! e : etaleBaseChange.{u, u + 1} (𝟙 S) ≅ 𝟭 (EtaleSite S),
      ∀ V : EtaleSite.{u, u + 1} S,
        (AsSmall.down.map (e.hom.app V)).left =
          pullback.fst (AsSmall.down.obj V).hom (𝟙 S) := by
  sorry

/-- The canonical identity comparison of etale site functors.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension). -/
def etaleIdentity (S : Scheme.{u}) := (etaleIdentity_existsUnique S).exists.choose

/-- Identity on the outer entries, and the canonical identity base change on the
second structural arrow of a triple. This only changes the site presentation.
Source: ILO XI §1.1 (blueprint: lem-trf-oriented-closed-base-extension). -/
def toProduct {X S : Scheme.{u}} (f : X ⟶ S) :
    VanishingSite.{u, u + 1} f ⥤ OrientedConstructibleSheaf.ProductSite f (𝟙 S) :=
  Comma.map (F₁ := 𝟭 _) (F₂ := 𝟭 _) (F := 𝟭 _)
    (𝟙 _)
    ((Functor.rightUnitor _).hom ≫
      NatTrans.prod' (𝟙 (etaleBaseChange f)) (etaleIdentity S).inv ≫
        (Functor.leftUnitor _).inv)

/-- Canonical scalar and site transport to the existing constructibility predicate.
The site functor is an equivalence induced by an isomorphism of the structural
functors; sheafified left Kan extension is its inverse-image functor.
Source: ILO XI §§1.1, 1.9; Stacks 03CY
(blueprint: lem-trf-oriented-closed-base-extension). -/
def constructiblePresentation {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] :
    (vanishingDatum.{u, u + 1} f).modules (Coeff Λ) ⥤
      OrientedConstructibleSheaf.Modules f (𝟙 S) Λ :=
  SheafOfModules.restrictScalars (realizationRingIso (vanishingTopology f) (Coeff Λ)).inv ⋙
    constantRingModuleRestriction (vanishingTopology f) (Coeff Λ) ⋙
    sheafToPresheaf (vanishingTopology f) (ModuleCat.{u + 1} (Coeff Λ)) ⋙
    (toProduct f).op.lan ⋙
    presheafToSheaf (OrientedConstructibleSheaf.productTopology f (𝟙 S))
      (ModuleCat.{u + 1} (Coeff Λ)) ⋙
    (constant_ring_module_sheaves (OrientedConstructibleSheaf.productTopology f (𝟙 S))
      (Coeff Λ)).1.choose.inverse

/-- The geometric morphism induced by the factorization square `(1_X, k)`.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension). -/
def embedding {X F S : Scheme.{u}} (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S)
    (hfac : fF ≫ k = f) :=
  squareMorphism.{u, u + 1} f fF (𝟙 X) k ((Category.id_comp f).trans hfac.symm)

/-- The same morphism with its canonical constant-module lift.
Source: ILO XI §4.1 (blueprint: lem-trf-oriented-closed-base-extension). -/
def modules {X F S : Scheme.{u}} (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S)
    (hfac : fF ≫ k = f) :=
  moduleMorphism (vanishingDatum.{u, u + 1} f) (vanishingDatum fF)
    (embedding f fF k hfac)

/-- The inverse image by p2 of the represented open complement of the closed base.
Source: Stacks 08LY--08M1 (blueprint: lem-trf-oriented-closed-base-extension). -/
def openComplement {X F S : Scheme.{u}} (f : X ⟶ S) (k : F ⟶ S)
    [IsClosedImmersion k] : VanishingTopos.{u, u + 1} f :=
  (p₂ f).inverse.obj ((OrientedProduct.associated (etaleTopology S)).obj
    (AsSmall.up.obj (Scheme.Etale.mk
      (Scheme.Opens.ι (⟨(Set.range k)ᶜ,
        k.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : S.Opens)))))

/-- The etale geometric identity comparison, obtained from the normalized site one.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension). -/
def etaleIdentityInverse (X : Scheme.{u}) :
    (etaleMorphism.{u, u + 1} (𝟙 X)).inverse ≅ 𝟭 _ :=
  (GeometricMorphism.inverseIso
    (a := etaleMorphism (𝟙 X)) (b := identity _)
    (Functor.sheafPushforwardContinuousIso (etaleIdentity X)
      (Type (u + 1)) (etaleTopology X) (etaleTopology X) ≪≫
        Functor.sheafPushforwardContinuousId (Type (u + 1)) (etaleTopology X))).symm

/-- The module identity is uniquely determined by scalar insertion and the
canonical set-sheaf identity, rather than an arbitrary automorphism of the identity.
Source: Stacks 03D2; ILO XI §4.1
(blueprint: lem-trf-oriented-closed-base-extension).
Proof: transport the normalized set-sheaf identity through the canonical module lift.
It respects addition and scalar operations. Tensor generators m tensor 1 generate
locally, so the displayed formula fixes a unique module isomorphism and its inverse. -/
theorem moduleIdentity_existsUnique (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :
    ∃! e : (etaleModules.{u, u + 1} (𝟙 X)).modulePull (Coeff Λ) ≅ 𝟭 _,
      ∀ M : (etaleDatum.{u, u + 1} X).modules (Coeff Λ),
        ConstantCompletion.pullInsertion (etaleModules (𝟙 X)).algebra
            (ConstantCompletion.constantMap (etaleModules (𝟙 X)).algebra (Coeff Λ)) M ≫
          (ConstantCompletion.underlying ((etaleDatum X).ring (Coeff Λ))).map
            (e.hom.app M) =
          (etaleIdentityInverse X).hom.app
            ((ConstantCompletion.underlying ((etaleDatum X).ring (Coeff Λ))).obj M) := by
  sorry

/-- Identity inverse image on the derived category, by exact localization.
Source: ILO XI §4.1 (blueprint: lem-trf-oriented-closed-base-extension). -/
def identityPull (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (etaleModules.{u, u + 1} (𝟙 X)).pull (Coeff Λ) ≅ 𝟭 (EtaleDerived X Λ) :=
  Functor.mapDerivedCategoryNatIso (moduleIdentity_existsUnique X Λ).exists.choose ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The ordinary closed-base comparison, with the identity pullback normalized.
Source: ILO XI §4.3 (blueprint: lem-trf-oriented-closed-base-extension). -/
def restrictionComparison {X F S : Scheme.{u}} (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S)
    (hfac : fF ≫ k = f) (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) :
    ((modules f fF k hfac).pull (Coeff Λ)).obj ((nearbyCycles f Λ).obj K) ⟶
      (nearbyCycles fF Λ).obj K :=
  baseChange f fF (𝟙 X) k ((Category.id_comp f).trans hfac.symm) Λ K ≫
    (nearbyCycles fF Λ).map ((identityPull X Λ).hom.app K)

/-- The closed-extension arrow is the adjoint transpose of the ordinary comparison.
Source: ILO XI §4.3 (blueprint: lem-trf-oriented-closed-base-extension). -/
def extensionComparison {X F S : Scheme.{u}} (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S)
    (hfac : fF ≫ k = f) (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived X Λ) :
    (nearbyCycles f Λ).obj K ⟶
      ((modules f fF k hfac).push (Coeff Λ)).obj ((nearbyCycles fF Λ).obj K) :=
  ((modules f fF k hfac).adj (Coeff Λ)).homEquiv _ _
    (restrictionComparison f fF k hfac Λ K)

/-- The first projection of a composite of two induced square morphisms,
identified with the projection of their composite scheme map.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension). -/
def compositeFirst {X₂ S₂ X₁ S₁ X₀ S₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (h₁ : X₁ ⟶ X₀) (g₁ : S₁ ⟶ S₀) (c₁ : h₁ ≫ f₀ = f₁ ≫ g₁)
    (h₂ : X₂ ⟶ X₁) (g₂ : S₂ ⟶ S₁) (c₂ : h₂ ≫ f₁ = f₂ ≫ g₂)
    (a : X₂ ⟶ X₀) (ha : h₂ ≫ h₁ = a) :
    (squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ c₂).direct ⋙
        (squareMorphism f₀ f₁ h₁ g₁ c₁).direct ⋙ (p₁ f₀).direct ≅
      (p₁ f₂).direct ⋙ (etaleMorphism a).direct :=
  Functor.isoWhiskerLeft _ (squareLift f₀ f₁ h₁ g₁ c₁).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift f₁ f₂ h₂ g₂ c₂).first _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition h₂ h₁ ≪≫
      eqToIso (congrArg (fun b ↦ (etaleMorphism.{u, u + 1} b).direct) ha))

/-- The second projection of a composite of two induced square morphisms,
identified with the projection of their composite scheme map.
Source: ILO XI §1.9 (blueprint: lem-trf-oriented-closed-base-extension). -/
def compositeSecond {X₂ S₂ X₁ S₁ X₀ S₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
    (h₁ : X₁ ⟶ X₀) (g₁ : S₁ ⟶ S₀) (c₁ : h₁ ≫ f₀ = f₁ ≫ g₁)
    (h₂ : X₂ ⟶ X₁) (g₂ : S₂ ⟶ S₁) (c₂ : h₂ ≫ f₁ = f₂ ≫ g₂)
    (a : S₂ ⟶ S₀) (ha : g₂ ≫ g₁ = a) :
    (squareMorphism.{u, u + 1} f₁ f₂ h₂ g₂ c₂).direct ⋙
        (squareMorphism f₀ f₁ h₁ g₁ c₁).direct ⋙ (p₂ f₀).direct ≅
      (p₂ f₂).direct ⋙ (etaleMorphism a).direct :=
  Functor.isoWhiskerLeft _ (squareLift f₀ f₁ h₁ g₁ c₁).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (squareLift f₁ f₂ h₂ g₂ c₂).second _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition g₂ g₁ ≪≫
      eqToIso (congrArg (fun b ↦ (etaleMorphism.{u, u + 1} b).direct) ha))

/-- Naturality of the specified transpose of the ordinary closed-base comparison.
Source: ILO XI §§1.9, 4.3 (blueprint: lem-trf-oriented-closed-base-extension).
Proof: baseChange is a counit mate, hence is natural in the coefficient complex.
The normalized identity pullback is a natural isomorphism. Naturality of the
adjunction hom equivalence then gives this equation for their transposes. -/
theorem extensionComparison_naturality {X F S : Scheme.{u}}
    (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S) (hfac : fF ≫ k = f)
    (Λ : Type (u + 1)) [CommRing Λ] {K L : EtaleDerived X Λ} (a : K ⟶ L) :
    (nearbyCycles f Λ).map a ≫ extensionComparison f fF k hfac Λ L =
      extensionComparison f fF k hfac Λ K ≫
        ((modules f fF k hfac).push (Coeff Λ)).map ((nearbyCycles fF Λ).map a) := by
  sorry

section BaseChange
variable {X F S X' F' S' : Scheme.{u}}
    (f : X ⟶ S) (fF : X ⟶ F) (k : F ⟶ S) (hfac : fF ≫ k = f)
    (f' : X' ⟶ S') (fF' : X' ⟶ F') (k' : F' ⟶ S') (hfac' : fF' ≫ k' = f')
    (h : X' ⟶ X) (g : S' ⟶ S) (c : h ≫ f = f' ≫ g)
    (gF : F' ⟶ F) (cF : h ≫ fF = fF' ≫ gF) (ck : gF ≫ k = k' ≫ g)

/-- The two paths of the base-changed factorization have a unique comparison
with the prescribed first and second projection identifications.
Source: ILO XI §1.4 (blueprint: lem-trf-oriented-closed-base-extension).
Proof: both paths give the triple with projections h p1 and g k' p2.
Their orientations are the two pastings of the same factorization square,
which agree by naturality and the equalities c, cF, ck, hfac and hfac'.
The universal property lem-trf-oriented-product-universal gives the unique
isomorphism preserving both projections, including its uniqueness on 2-morphisms. -/
theorem square_existsUnique :
    ∃! e : (embedding f' fF' k' hfac').direct ⋙
        (squareMorphism.{u, u + 1} f f' h g c).direct ≅
      (squareMorphism fF fF' h gF cF).direct ⋙ (embedding f fF k hfac).direct,
      (Functor.isoWhiskerRight e (p₁ f).direct) ≪≫
          compositeFirst f fF fF' (𝟙 X) k ((Category.id_comp f).trans hfac.symm)
            h gF cF h (Category.comp_id h) =
        compositeFirst f f' fF' h g c (𝟙 X') k'
          ((Category.id_comp f').trans hfac'.symm) h (Category.id_comp h) ∧
      (Functor.isoWhiskerRight e (p₂ f).direct) ≪≫
          compositeSecond f fF fF' (𝟙 X) k ((Category.id_comp f).trans hfac.symm)
            h gF cF (k' ≫ g) ck =
        compositeSecond f f' fF' h g c (𝟙 X') k'
          ((Category.id_comp f').trans hfac'.symm) (k' ≫ g) rfl := by
  sorry

/-- The uniquely normalized inverse-image square of the four vanishing topoi.
Source: ILO XI §1.4 (blueprint: lem-trf-oriented-closed-base-extension). -/
def square :
    (squareModules.{u, u + 1} f f' h g c).inverse ⋙
        (modules f' fF' k' hfac').inverse ≅
      (modules f fF k hfac).inverse ⋙ (squareModules fF fF' h gF cF).inverse :=
  (GeometricMorphism.inverseIso
    (a := (embedding f' fF' k' hfac').comp (squareMorphism f f' h g c))
    (b := (squareMorphism fF fF' h gF cF).comp (embedding f fF k hfac))
    (square_existsUnique f fF k hfac f' fF' k' hfac' h g c gF cF ck).exists.choose).symm

/-- The canonical closed-embedding base-change mate: the unit for v', followed
by the inverse-image square and the counit for v. Its definition uses the existing
ordinaryExchange, whose mate is exactly this unit--counit composite.
Source: Stacks 08M1; ILO XI §4.3
(blueprint: lem-trf-oriented-closed-base-extension). -/
def exchange (Λ : Type (u + 1)) [CommRing Λ] :
    (modules f fF k hfac).push (Coeff Λ) ⋙
        (squareModules.{u, u + 1} f f' h g c).pull (Coeff Λ) ⟶
      (squareModules fF fF' h gF cF).pull (Coeff Λ) ⋙
        (modules f' fF' k' hfac').push (Coeff Λ) :=
  ordinaryExchange (f := modules f fF k hfac) (g := squareModules f f' h g c)
    (h := squareModules fF fF' h gF cF) (k := modules f' fF' k' hfac')
    (square f fF k hfac f' fF' k' hfac' h g c gF cF ck) (Coeff Λ)

end BaseChange

/-- Closed-base extension for oriented nearby cycles, including its canonical
compatibility with every scheme base change. Exactness is preservation of finite
limits and finite colimits in the abelian module categories. The essential-image
condition identifies the set-sheaf direct image with the full subcategory defining
the closed complement of p2 inverse image of S minus F.

Source: Orgogozo §§3.2, 9.2; ILO XI §§1.4, 2, 4.3; Stacks 08LY--08M1
(blueprint: lem-trf-oriented-closed-base-extension).

Proof (the eight steps of the DAG node):
1. Apply lem-trf-oriented-closed-base-localization to the represented open S minus F.
By lem-trf-oriented-product-universal, a map to V_f is a triple (a,b,t:b to f a).
It lies in the closed complement exactly when b lifts through F_et. Full faithfulness
of k_* lifts t uniquely, so these triples are precisely maps to V_fF. This identifies
the actual induced morphism embedding with that closed subtopos, including 2-morphisms.
2. The module clause of the localization lemma gives exactness and full faithfulness.
For constructibility, extend the finitely many second-factor strata in F to S and
adjoin S minus F. They are constructible locally closed subsets since S is Noetherian
(def-weil-constructible-subset, def-constructible-stratification). On rectangles over
F the counit identifies restriction with the original sheaf; on the open complement
restriction is zero. Thus def-trf-oriented-constructible-sheaf applies.
3. At an oriented point whose second coordinate b is outside F, the inverse image
of S minus F in S_(b) contains the closed point, hence is all of S_(b), by
lem-weil-pbc-strict-henselization-functoriality(1). The tube is empty because X maps
through F (def-pc-fibre-product); lem-trf-oriented-point-cohomology gives zero.
4. At b in F, lem-trf-closed-immersion-strict-localization-cartesian identifies both
strict localizations over F with the ambient ones base changed to F. Uniqueness in
lem-weil-pbc-strict-henselization-functoriality(3) and reassociation of fibre products
identify the two tubes, including nilpotents and structural maps. The stalk formula
for the ordinary comparison in lem-trf-finite-cover-tube-comparison, with g=k and
X times_S F identified with X, is restriction along this tube isomorphism.
5. Transpose this ordinary comparison under v^* adjoint to Rv_*. Exactness of v_*
identifies its derived image with its termwise image. The resulting extensionComparison
is invertible at points over F by step 4 and the counit, and both sides vanish off F
by step 3. Apply lem-trf-oriented-product-points-conservative. Naturality follows from
naturality of the counit and the adjunction transpose, as recorded above.
6. For arbitrary g:S' to S, form F' and X' by fibre product. The base-changed immersion
is closed (lem-weil-pbc-closed-immersion-base-change). Universal triples identify the
two paths of the square of vanishing topoi, with exactly the normalized square above.
The inverse image of the closed complement is the new closed complement, without any
Noetherian hypothesis on S'. The mate exchange inserts the unit for v' and then the
counit for v. Its source is supported on the new closed complement, so its unit and
counit factors are invertible by lem-trf-oriented-closed-base-localization.
7. The two paths of scheme squares give the same composite square. Their ordinary
nearby-cycle comparisons therefore satisfy delta' after v'^* beta equals beta_F
after w_F^* delta. Indeed lem-weil-pbc-mate-pasting(1) identifies both transposes
with h^* of the original nearby-cycle counit, before taking any stalks.
8. Transpose the asserted equality under v'^* adjoint to Rv'_*. Substitute the
unit--counit expression for exchange; naturality and the triangle identity cancel
its inserted unit. The two transposes are precisely the maps of step 7, by
lem-weil-pbc-mate-pasting(2). This proves the displayed compatibility equation. -/
theorem orientedClosedBaseExtension
    {X F S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [IsProper f] (k : F ⟶ S) [IsClosedImmersion k]
    (fF : X ⟶ F) (hfac : fF ≫ k = f)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]
    (K : EtaleDerived X Λ)
    (_hKb : IsBounded (etaleDatum X) (Coeff Λ) K)
    (_hKc : ∀ q : ℤ,
      ∃ Fq : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ)),
        Scheme.IsConstructibleEtaleModuleSheaf Fq ∧
        Nonempty ((PresheafOfModules.forgetToPresheafModuleCat
            (op (⊤_ (EtaleSite.{u, u + 1} X))) terminalIsTerminal.op).obj
          ((PresheafOfModules.restrictScalars
            (Functor.whiskerRight
              (toSheafify (etaleTopology.{u, u + 1} X)
                ((Functor.const (EtaleSite.{u, u + 1} X)ᵒᵖ).obj
                  (CommRingCat.of (Coeff.{u, u + 1} Λ))))
              (forget₂ CommRingCat RingCat))).obj
            ((DerivedCategory.homologyFunctor
              ((etaleDatum.{u, u + 1} X).modules (Coeff Λ)) q).obj K).val) ≅
          (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙ Fq.obj)) :
    (embedding f fF k hfac).direct.Full ∧
    (embedding f fF k hfac).direct.Faithful ∧
    (∀ H : VanishingTopos.{u, u + 1} f,
      (embedding f fF k hfac).direct.essImage H ↔
        IsIso (Limits.prod.fst : openComplement f k ⨯ H ⟶ openComplement f k)) ∧
    PreservesFiniteLimits ((modules f fF k hfac).modulePush (Coeff Λ)) ∧
    PreservesFiniteColimits ((modules f fF k hfac).modulePush (Coeff Λ)) ∧
    ((modules f fF k hfac).modulePush (Coeff Λ)).Full ∧
    ((modules f fF k hfac).modulePush (Coeff Λ)).Faithful ∧
    (∀ G : (vanishingDatum.{u, u + 1} fF).modules (Coeff Λ),
      OrientedConstructibleSheaf.IsConstructible fF (𝟙 F) Λ
          ((constructiblePresentation fF Λ).obj G) →
        OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ
          ((constructiblePresentation f Λ).obj
            (((modules f fF k hfac).modulePush (Coeff Λ)).obj G))) ∧
    IsIso (extensionComparison f fF k hfac Λ K) ∧
    (∀ {X' F' S' : Scheme.{u}}
      (g : S' ⟶ S) (h : X' ⟶ X) (f' : X' ⟶ S')
      (hp : IsPullback h f' f g) (gF : F' ⟶ F) (k' : F' ⟶ S')
      (hk : IsPullback gF k' k g) (fF' : X' ⟶ F')
      (hfac' : fF' ≫ k' = f') (cF : h ≫ fF = fF' ≫ gF),
      (∀ A : VanishingDerived fF Λ,
        IsIso ((exchange f fF k hfac f' fF' k' hfac' h g hp.w gF cF hk.w Λ).app A)) ∧
      baseChange f f' h g hp.w Λ K ≫
          extensionComparison f' fF' k' hfac' Λ
            (((etaleModules h).pull (Coeff Λ)).obj K) =
        ((squareModules f f' h g hp.w).pull (Coeff Λ)).map
            (extensionComparison f fF k hfac Λ K) ≫
          (exchange f fF k hfac f' fF' k' hfac' h g hp.w gF cF hk.w Λ).app
            ((nearbyCycles fF Λ).obj K) ≫
          ((modules f' fF' k' hfac').push (Coeff Λ)).map
            (baseChange fF fF' h gF cF Λ K)) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.ClosedBase
