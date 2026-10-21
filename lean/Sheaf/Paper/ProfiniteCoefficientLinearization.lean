/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralContinuousPresentationMatrix
public import Sheaf.Paper.NormContinuousMonodromyData
public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedComap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Continuous profinite linearizations of internal coefficient modules

Source: blueprint main-20261015, ctf-stability direct-images proof (3), tame-boundary
expansion, continuous equivariant structures
(blueprint: def-sfb-profinite-coefficient-linearization).

Continuity means an isomorphism on the whole profinite parameter object. The laws are
identities on parameter objects, so pointwise actions without continuity do not qualify.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The canonical profinite parameter object. Source: tame-boundary expansion, X[P]
(blueprint: def-sfb-profinite-coefficient-linearization). -/
abbrev coefficientParameter (X : Scheme.{u}) (P : Profinite.{u}) :=
  ((profiniteToProEtOf X).obj P).left

/-- Its projection. Source: tame-boundary expansion, X[P]
(blueprint: def-sfb-profinite-coefficient-linearization). -/
abbrev coefficientParameterProjection (X : Scheme.{u}) (P : Profinite.{u}) :
    coefficientParameter X P ⟶ X :=
  ((profiniteToProEtOf X).obj P).hom

/-- Pull back a family action along a continuous profinite parameter map.
Source: tame-boundary expansion, continuous action
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientActionFamily {X : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (P : Profinite.{u}) (g : C(P, G)) :
    coefficientParameter X P ⟶ X :=
  ((profiniteToProEtOf X).map (CompHausLike.ofHom _ g)).left ≫ a

/-- Keep the profinite parameter while applying a family action.
Source: tame-boundary expansion, action groupoid
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientActionLift {X : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (P : Profinite.{u}) (g : C(P, G)) :
    coefficientParameter X P ⟶ coefficientParameter X P :=
  pullback.lift
    (pullback.fst (toSpecZ (profiniteToScheme.obj P)) (toSpecZ X))
    (coefficientActionFamily a P g)
    (specULiftZIsTerminal.hom_ext _ _)

/-- A continuous action, with identities on every profinite parameter object.
Source: tame-boundary expansion, continuous deck action
(blueprint: def-sfb-profinite-coefficient-linearization). -/
structure ProfiniteCoefficientAction (X : Scheme.{u}) (G : Profinite.{u})
    [Group G] [IsTopologicalGroup G] where
  act : coefficientParameter X G ⟶ X
  one : ∀ P, coefficientActionFamily act P (ContinuousMap.const P (1 : G)) =
    coefficientParameterProjection X P
  mul : ∀ (P : Profinite.{u}) (g h : C(P, G)),
    coefficientActionLift act P g ≫ coefficientActionFamily act P h =
      coefficientActionFamily act P (h * g)

/-- Pull an isomorphism along a map, retaining the canonical composition comparisons.
Source: tame-boundary expansion, restriction of equivariant structures
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientIsoPull
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {f g : Y ⟶ X} (e : (CondensedRing.upperStar Λ f).obj M ≅
      (CondensedRing.upperStar Λ g).obj M) (z : Z ⟶ Y) :
    (CondensedRing.upperStar Λ (z ≫ f)).obj M ≅
      (CondensedRing.upperStar Λ (z ≫ g)).obj M :=
  (CondensedRing.upperStarComp Λ z f).app M ≪≫
    (CondensedRing.upperStar Λ z).mapIso e ≪≫
      ((CondensedRing.upperStarComp Λ z g).app M).symm

/-- A continuous linearization on the whole parameter object. Its laws are tested after
arbitrary scheme maps into that object. Composable triples are the action groupoid:
the middle source equals the first target, and the third group label is the product.
Source: tame-boundary expansion, continuous equivariant lisse extension
(blueprint: def-sfb-profinite-coefficient-linearization). -/
structure ProfiniteCoefficientLinearization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {G : Profinite.{u}}
    [Group G] [IsTopologicalGroup G] (a : ProfiniteCoefficientAction X G)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) where
  iso : (CondensedRing.upperStar Λ a.act).obj M ≅
    (CondensedRing.upperStar Λ (coefficientParameterProjection X G)).obj M
  one : ∀ (Z : Scheme.{u}) (z : Z ⟶ coefficientParameter X G),
    (∀ x : Z, profiniteTestProjection X G (z x) = 1) →
    ∀ h : z ≫ a.act = z ≫ coefficientParameterProjection X G,
      (coefficientIsoPull Λ M iso z).hom =
        ((CondensedRing.upperStarCongr Λ h).app M).hom
  cocycle : ∀ (Z : Scheme.{u}) (z v w : Z ⟶ coefficientParameter X G),
    (∀ x : Z, profiniteTestProjection X G (w x) =
      profiniteTestProjection X G (v x) * profiniteTestProjection X G (z x)) →
    ∀ (hm : z ≫ coefficientParameterProjection X G = v ≫ a.act)
      (hs : w ≫ a.act = z ≫ a.act)
      (ht : v ≫ coefficientParameterProjection X G =
        w ≫ coefficientParameterProjection X G),
      (coefficientIsoPull Λ M iso w).hom =
        ((CondensedRing.upperStarCongr Λ hs).app M).hom ≫
        (coefficientIsoPull Λ M iso z).hom ≫
        ((CondensedRing.upperStarCongr Λ hm).app M).hom ≫
        (coefficientIsoPull Λ M iso v).hom ≫
        ((CondensedRing.upperStarCongr Λ ht).app M).hom

/-- Pullback of the regular module, using the actual Cartesian coefficient comparison.
Source: tame-boundary expansion, pullback of constant vector models
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientRegularPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj (Mod.regular (condensedRingObj Λ Y)) ≅
      Mod.regular (condensedRingObj Λ X) :=
  (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app _ ≪≫
    (Mod.comap (inv (condensedPullbackHom Λ f))).mapIso
      (Mod.isoMk
        (M := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj
          (Mod.regular (condensedRingObj Λ Y)))
        (N := Mod.regular ((upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)))
        (Iso.refl _) (by
          simp only [Iso.refl_hom, Category.comp_id,
            MonoidalCategory.whiskerLeft_id, Category.id_comp])) ≪≫
    Mod.regularIsoOfIsIso (condensedPullbackHom Λ f)

/-- The canonical comparison for finite constant free modules, including rank zero.
Source: tame-boundary expansion, finite vector models
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientFreePullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (CondensedRing.upperStar Λ f).obj (Mod.finiteFree (condensedRingObj Λ Y) d) ≅
      Mod.finiteFree (condensedRingObj Λ X) d :=
  (CondensedRing.upperStar Λ f).mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ ↦ coefficientRegularPullbackIso Λ f)

/-- Map on profinite parameter schemes induced by a scheme morphism.
Source: tame-boundary expansion, restriction along refinements
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientParameterMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Profinite.{u}) : coefficientParameter X P ⟶ coefficientParameter Y P :=
  pullback.lift
    (pullback.fst (toSpecZ (profiniteToScheme.obj P)) (toSpecZ X))
    (coefficientParameterProjection X P ≫ f) (specULiftZIsTerminal.hom_ext _ _)

/-- The defining projection equation of the canonical map on profinite parameters.
Source: tame-boundary expansion, canonical restriction maps
(blueprint: def-sfb-profinite-coefficient-linearization). -/
abbrev coefficientParameterProjectionCommutes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Profinite.{u}) : coefficientParameterMap f P ≫ coefficientParameterProjection Y P =
      coefficientParameterProjection X P ≫ f :=
  by
    unfold coefficientParameterMap coefficientParameterProjection
    exact pullback.lift_snd _ _ _

/-- Restrict the actual parameter isomorphism along an equivariant scheme map.
Source: tame-boundary expansion, deck-equivariant restriction
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientLinearizationRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {G : Profinite.{u}}
    (ax : coefficientParameter X G ⟶ X) (ay : coefficientParameter Y G ⟶ Y)
    (f : X ⟶ Y) (ha : ax ≫ f = coefficientParameterMap f G ≫ ay)
    (hp : coefficientParameterMap f G ≫ coefficientParameterProjection Y G =
      coefficientParameterProjection X G ≫ f)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (e : (CondensedRing.upperStar Λ ay).obj M ≅
      (CondensedRing.upperStar Λ (coefficientParameterProjection Y G)).obj M) :
    (CondensedRing.upperStar Λ ax).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      (CondensedRing.upperStar Λ (coefficientParameterProjection X G)).obj
        ((CondensedRing.upperStar Λ f).obj M) :=
  ((CondensedRing.upperStarComp Λ ax f).app M).symm ≪≫
    (CondensedRing.upperStarCongr Λ ha).app M ≪≫
    coefficientIsoPull Λ M e (coefficientParameterMap f G) ≪≫
    (CondensedRing.upperStarCongr Λ hp).app M ≪≫
    (CondensedRing.upperStarComp Λ (coefficientParameterProjection X G) f).app M

/-- Canonical deck descent on an actual pullback from the quotient.
Source: tame-boundary expansion, actual deck-equivariant pullback of L
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientDeckDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X W : Scheme.{u}} {G : Profinite.{u}}
    (a : coefficientParameter X G ⟶ X) (f : X ⟶ W)
    (h : a ≫ f = coefficientParameterProjection X G ≫ f)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    (CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj L) ≅
      (CondensedRing.upperStar Λ (coefficientParameterProjection X G)).obj
        ((CondensedRing.upperStar Λ f).obj L) :=
  ((CondensedRing.upperStarComp Λ a f).app L).symm ≪≫
    (CondensedRing.upperStarCongr Λ h).app L ≪≫
    (CondensedRing.upperStarComp Λ (coefficientParameterProjection X G) f).app L

/-- Transport an endomorphism to finite free coordinates using the canonical pullback basis.
Source: tame-boundary expansion, boundary matrix coordinates
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientConjugateFreeEnd
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (b : M ≅ Mod.finiteFree (condensedRingObj Λ Y) d)
    (e : (CondensedRing.upperStar Λ f).obj M ≅ (CondensedRing.upperStar Λ f).obj M) :
    Mod.finiteFree (condensedRingObj Λ X) d ⟶
      Mod.finiteFree (condensedRingObj Λ X) d :=
  (coefficientFreePullbackIso Λ f d).inv ≫
    ((CondensedRing.upperStar Λ f).mapIso b).inv ≫ e.hom ≫
    ((CondensedRing.upperStar Λ f).mapIso b).hom ≫
    (coefficientFreePullbackIso Λ f d).hom

/-- Continuous coordinates of an actual finite-free module endomorphism.
Source: HRS Example 3.1 and tame-boundary expansion, matrix coefficients
(blueprint: def-sfb-profinite-coefficient-linearization). -/
@[irreducible] def coefficientFreeMatrix
    (E : Type u) [NormedField E] (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
    (φ : R ≅ ContinuousRingUniverse.coeff E X) (d : ℕ)
    (f : Mod.finiteFree R d ⟶ Mod.finiteFree R d) : Matrix (Fin d) (Fin d) C(X, E) :=
  fun i j ↦ ContinuousRingUniverse.coeffEndFun
    (φ.inv ≫ (biproduct.ι (fun _ : Fin d ↦ Mod.regular R) j ≫ f ≫
      biproduct.π (fun _ : Fin d ↦ Mod.regular R) i).hom ≫ φ.hom)

end AlgebraicGeometry.ProEtale
