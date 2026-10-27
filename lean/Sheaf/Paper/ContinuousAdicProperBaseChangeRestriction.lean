/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.SixFunctors.ProEtale.Adic.Ring
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

import Mathlib.Algebra.Category.Ring.Limits
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import all Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit

/-! # Continuous adic proper base change under locally closed restriction

Source: Stacks Project, proetale.tex, Tag 09C9 (finite-stage input), and
Bhatt--Scholze, Section 6.8, ordinary module realization and restriction exchange
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).

All module categories are the sectionwise module categories on the original small
pro-etale sites. In particular restriction takes values over the actual inverse-image
ring; it does not extend scalars to a separately chosen coefficient sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.ContinuousAdicRestriction

variable (l : ℕ) [Fact l.Prime]

/-- The prescribed ring presheaf, with pointwise operations and precomposition.
Source: Bhatt--Scholze 6.8.1, finite-subextension convention
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def coefficientPresheaf (X : Scheme.{u}) : X.ProEtᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj U := CommRingCat.of (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l U.unop.left))
  map a := CommRingCat.ofHom (WeilCoefficients.uliftAlgHom
    (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l a.unop.left.base.hom)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The locally finite-span presheaf is already a sheaf.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: forgetting the ring operations gives the locally finite continuous function
presheaf underlying adicConstantSheaf. Its fpqc descent theorem proves the sheaf
condition; the forgetful functor creates limits and reflects isomorphisms. -/
theorem coefficientPresheaf_isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.ProEt.topology X) (coefficientPresheaf l X) := by
  have : ReflectsLimitsOfSize.{u, u + 1} (forget CommRingCat.{u + 1}) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology X)
    (coefficientPresheaf l X) (forget CommRingCat.{u + 1})
  exact (sheafCompose _ (forget (WeilCoefficients.{u} l))).obj
    (adicConstantSheaf l X) |>.property

/-- The coefficient ring, using the already-sheaf representative of its sheafification.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def coefficientRing (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  ⟨coefficientPresheaf l X, coefficientPresheaf_isSheaf l X⟩

/-- Precomposition with the first fibre-product projection is natural.
Source: Stacks Tag 09A5 and Bhatt--Scholze 6.8.2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: the two composites are precomposition with equal scheme morphisms by the
first projection equation for pullback.map; pointwise ring operations are preserved. -/
theorem coefficientMap_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U V : Y.ProEtᵒᵖ} (a : U ⟶ V) :
    (coefficientPresheaf l Y).map a ≫
        CommRingCat.ofHom (WeilCoefficients.uliftAlgHom
          (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l
            (pullback.fst V.unop.hom f).base.hom)).toRingHom =
      CommRingCat.ofHom (WeilCoefficients.uliftAlgHom
          (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l
            (pullback.fst U.unop.hom f).base.hom)).toRingHom ≫
        (coefficientPresheaf l X).map ((proEtaleBaseChange f).op.map a) := by
  ext s x
  change s.down.1 (a.unop.left (pullback.fst V.unop.hom f x)) =
    s.down.1 (pullback.fst U.unop.hom f (((proEtaleBaseChange f).map a.unop).left x))
  have key : ((proEtaleBaseChange f).map a.unop).left ≫ pullback.fst U.unop.hom f =
      pullback.fst V.unop.hom f ≫ a.unop.left := pullback.lift_fst _ _ _
  exact congrArg (fun g : pullback V.unop.hom f ⟶ U.unop.left =>
    s.down.1 (g x)) key.symm


/-- The coefficient map is the specified precomposition map, for every scheme morphism.
Source: Stacks Tag 09A5 and Bhatt--Scholze 6.8.2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientRing l Y ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (coefficientRing l X) :=
  ⟨{ app U := CommRingCat.ofHom (WeilCoefficients.uliftAlgHom
        (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l
          (pullback.fst U.unop.hom f).base.hom)).toRingHom
     naturality := fun _ _ a ↦ coefficientMap_naturality l f a }⟩

/-- Forget only commutativity, retaining the ring and its sections.
Source: Stacks Modules on Sites, 03D2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
abbrev ring {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

/-- The actual inverse-image ring.
Source: Stacks Tags 09A5 and 03D2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
abbrev inverseRing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- Direct image with action through the supplied, specified coefficient map.
Source: Stacks Modules on Sites, 03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def direct {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S) :
    proEtaleRingModules X S ⥤ proEtaleRingModules Y R :=
  SheafOfModules.pushforward (F := proEtaleBaseChange f)
    ⟨Functor.whiskerRight r.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- The right adjoint of pure inverse image, with action through the ring unit.
Source: Stacks Modules on Sites, 03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
abbrev inverseDirect {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :=
  direct f R (inverseRing f R) ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)

/-- The pure inverse-image adjunction with its Kan-extension unit, uniquely normalized.
Source: Stacks Modules on Sites, 03D2--03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: transport the module pullback/pushforward adjunction on the AsSmall site through
the sectionwise equivalences. These equivalences do not change sections. The displayed
unit is its module Kan-extension unit. An adjunction is determined by its unit, proving
uniqueness. This uses no extension of scalars. -/
theorem inverseAdjunction_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃! adj : proEtaleModuleInverseImage f R ⊣ inverseDirect f R,
      ∀ (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (op U)),
        (adj.unit.app M).val.app (op U) m =
          ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
            ((proEtaleModuleToModel (ring R)).obj M)).val.app (op (AsSmall.up.obj U)) m := by
  refine ⟨canonicalAdjunction f R, ?_, ?_⟩
  · intro M U m
    exact canonicalUnit_sections f R M (op U) m
  · intro adj hadj
    apply Adjunction.ext
    ext M U m
    exact (hadj M U.unop m).trans (canonicalUnit_sections f R M U m).symm

/-- The normalized adjunction for the exact topos inverse image on modules.
Source: Stacks Modules on Sites, 03D2--03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def inverseAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleModuleInverseImage f R ⊣ inverseDirect f R :=
  Classical.choose (inverseAdjunction_existsUnique f R)

/-- Pure inverse image is additive and exact, and direct image is additive.
Source: Stacks Modules on Sites, 03D2--03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: filtered module Kan extension followed by sheafification computes inverse image
of the underlying abelian sheaf. Topos inverse image preserves finite limits and all
colimits. Forgetful functors reflect exactness. Direct image is additive sectionwise. -/
theorem operations_properties {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S) :
    (proEtaleModuleInverseImage f R).Additive ∧
      PreservesFiniteLimits (proEtaleModuleInverseImage f R) ∧
      PreservesFiniteColimits (proEtaleModuleInverseImage f R) ∧ (direct f R S r).Additive := by
  let adj := canonicalAdjunction f R
  have : (AlgebraicGeometry.Scheme.T f R).Additive := by
    refine ⟨fun {_ _} _ _ ↦ ?_⟩
    rfl
  have : PreservesColimitsOfSize.{0, 0} (proEtaleModuleInverseImage f R) :=
    adj.leftAdjoint_preservesColimits
  refine ⟨adj.left_adjoint_additive,
    proEtaleModuleInverseImage_preservesFiniteLimits f R, inferInstance, ?_⟩
  refine ⟨fun {_ _} _ _ ↦ ?_⟩
  rfl

/-- Additivity of pure inverse image, from the preceding exactness statement.
Source: Stacks 03D2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
instance inverse_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage f R).Additive :=
  (operations_properties f R (inverseRing f R)
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)).1

/-- Left exactness of pure inverse image. Source: Stacks 03D2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
instance inverse_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (proEtaleModuleInverseImage f R) :=
  (operations_properties f R (inverseRing f R)
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)).2.1

/-- Right exactness of pure inverse image. Source: Stacks 03D2
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
instance inverse_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (proEtaleModuleInverseImage f R) :=
  (operations_properties f R (inverseRing f R)
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R)).2.2.1

/-- Additivity of the specified direct image. Source: Stacks 03D3
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
instance direct_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S) :
    (direct f R S r).Additive :=
  (operations_properties f R S r).2.2.2

/-- Ring-valued topos base change, the mate of fibre-product pasting on direct images.
Source: Stacks Tags 09A5 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def ringBaseChange {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T) :
    proEtaleSheafDirectImage p CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage h CommRingCat.{u + 1} ⟶
      proEtaleSheafInverseImage (pullback.fst p h) CommRingCat.{u + 1} ⋙
        proEtaleSheafDirectImage (pullback.snd p h) CommRingCat.{u + 1} :=
  ((mateEquiv (proEtaleSheafAdjunction (pullback.fst p h) CommRingCat.{u + 1})
    (proEtaleSheafAdjunction h CommRingCat.{u + 1})).symm
    (TwoSquare.mk _ _ _ _ (squareLowerStarIso CommRingCat.{u + 1}
      (IsPullback.of_hasPullback p h).toCommSq.flip).hom)).natTrans

/-- The induced map for p' on the actual two inverse-image coefficient rings.
Source: Stacks Tags 09A5 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def restrictedMap {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S) :
    inverseRing h R ⟶ (proEtaleSheafDirectImage (pullback.snd p h)
      CommRingCat.{u + 1}).obj (inverseRing (pullback.fst p h) S) :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map r ≫ (ringBaseChange p h).app S

/-- The type of the canonical module direct-image square.
Source: Stacks Tags 09A5, 03D3 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def DirectSquare {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S) : Type _ :=
  inverseDirect (pullback.fst p h) S ⋙ direct p R S r ≅
        direct (pullback.snd p h) (inverseRing h R) (inverseRing (pullback.fst p h) S)
          (restrictedMap p h R S r) ⋙ inverseDirect h R

/-- Sectionwise normalization of the direct-image square.
Source: Stacks Tags 09A5, 03D3 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def DirectSquareNormalized {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S)
    (d : DirectSquare p h R S r) : Prop :=
  ∀ N : proEtaleRingModules (pullback p h) (inverseRing (pullback.fst p h) S),
        (SheafOfModules.toSheaf (ring R)).map (d.hom.app N) =
          (squareLowerStarIso AddCommGrpCat.{u + 1}
            (IsPullback.of_hasPullback p h).toCommSq.flip).hom.app
              ((SheafOfModules.toSheaf (ring (inverseRing (pullback.fst p h) S))).obj N)

/-- The module direct-image square, fixed uniquely by its action on sections.
Source: Stacks Tags 09A5, 03D3 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: the underlying abelian direct images are identified by fibre-product pasting.
The definition of restrictedMap as the ring-valued mate makes that identification
linear over R. It is a natural isomorphism since the fibre-product comparison is an
isomorphism. The faithful underlying-abelian functor proves uniqueness. -/
theorem directSquare_existsUnique {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S) :
    ∃! d : DirectSquare p h R S r, DirectSquareNormalized p h R S r d := by
  sorry

/-- The specified direct-image square comparison, rather than an arbitrary isomorphism.
Source: Stacks Tags 09A5 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def directSquare {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S) :=
  Classical.choose (directSquare_existsUnique p h R S r)

/-- The ordinary exchange, as the canonical mate of the normalized direct-image square.
Equivalently its p'-adjunct is the inverse-image composition followed by h' inverse
image of the p-counit. Source: Stacks Tags 03D3 and 03D8
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def ordinaryExchange {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (R : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology P) CommRingCat.{u + 1})
    (r : R ⟶ (proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj S) :
    direct p R S r ⋙ proEtaleModuleInverseImage h R ⟶
      proEtaleModuleInverseImage (pullback.fst p h) S ⋙
        direct (pullback.snd p h) (inverseRing h R) (inverseRing (pullback.fst p h) S)
          (restrictedMap p h R S r) :=
  ((mateEquiv (inverseAdjunction (pullback.fst p h) S) (inverseAdjunction h R)).symm
    (TwoSquare.mk _ _ _ _ (directSquare p h R S r).hom)).natTrans

section Derivation

universe uC uD uC' uD' vC vD vC' vD' wC wD wC' wD'

variable {C : Type uC} {D : Type uD} {C' : Type uC'} {D' : Type uD'}
  [Category.{vC} C] [Category.{vD} D] [Category.{vC'} C'] [Category.{vD'} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [HasDerivedCategory.{wC'} C'] [HasDerivedCategory.{wD'} D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  (G : C ⥤ D) (G' : C' ⥤ D') (H : D ⥤ D') (H' : C ⥤ C')
  [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']

/-- The ordinary exchange on homotopy categories followed by the target derived unit.
Source: Stacks Derived Categories, 09T5, and the node's resolution formula, step 4
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def exchangeAux (b : G ⋙ H ⟶ H' ⋙ G') :
    (G ⋙ H).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ H'.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory b (ComplexShape.up ℤ))
      DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (H' ⋙ G')) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (H'.mapHomotopyCategory (ComplexShape.up ℤ)) G'.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight H'.mapDerivedCategoryFactorsh.inv G'.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- The canonical derived restriction map, defined by the universal right-derived pair.
On resolutions it is b_I followed by the pushforward of a resolution of H'I.
Source: Stacks Derived Categories, 09T5; node proof step 4
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def exchange (b : G ⋙ H ⟶ H' ⋙ G') :
    G.rightDerivedFunctor ⋙ H.mapDerivedCategory ⟶
      H'.mapDerivedCategory ⋙ G'.rightDerivedFunctor :=
  (G.rightDerivedFunctor ⋙ H.mapDerivedCategory).rightDerivedDesc
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit G H)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ (exchangeAux G G' H H' b)

private theorem exchange_homotopy_fac (b : G ⋙ H ⟶ H' ⋙ G')
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategory.map
        (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)) ≫
        (exchange G G' H H' b).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      H.mapDerivedCategoryFactorsh.hom.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory b (.up ℤ)).app
          ((HomotopyCategory.quotient _ _).obj K)) ≫
        G'.rightDerivedFunctorUnit.app
          ((H'.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
        G'.rightDerivedFunctor.map
          (H'.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj K)) := by
  have hf := (G.rightDerivedFunctor ⋙ H.mapDerivedCategory).rightDerived_fac_app
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit G H)
    (HomotopyCategory.quasiIso C (.up ℤ)) _ (exchangeAux G G' H H' b)
    ((HomotopyCategory.quotient _ _).obj K)
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H))
      (.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj K)),
      Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      Category.comp_id]
  have hi' : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H' ⋙ G')) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (H' ⋙ G'))
      (.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj K)),
      Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      Category.comp_id]
  dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, exchangeAux,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hf
  rw [hi, hi'] at hf
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at hf
  dsimp only [Functor.comp_obj, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as] at hf
  repeat first | erw [Category.id_comp] at hf | erw [Category.comp_id] at hf
  rw [← cancel_epi (H.mapDerivedCategoryFactorsh.inv.app
    ((G.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)))]
  simp only [Category.assoc] at hf
  convert hf using 1 <;>
    (try simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]) <;> rfl

private theorem exchange_complex_fac (b : G ⋙ H ⟶ H' ⋙ G')
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ K) ≫
        (exchange G G' H H' b).app (DerivedCategory.Q.obj K) ≫
        G'.rightDerivedFunctor.map (H'.mapDerivedCategoryFactors.hom.app K) =
      H.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app K) ≫
        G'.rightDerivedFunctorUnitQ ((H'.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hf := exchange_homotopy_fac G G' H H' b K
  have hh (A : CochainComplex D ℤ) :
      H.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj A) =
        H.mapDerivedCategoryFactors.hom.app A := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    have hq : (DerivedCategory.quotientCompQhIso D).hom.app A = 𝟙 _ := rfl
    have hq' : (DerivedCategory.quotientCompQhIso D').inv.app
        ((H.mapHomologicalComplex (.up ℤ)).obj A) = 𝟙 _ := rfl
    have hi : (H.mapHomotopyCategoryFactors (.up ℤ)).inv.app A = 𝟙 _ := rfl
    rw [hq, hq', hi]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    repeat first | erw [Category.id_comp] | erw [Category.comp_id]
  have hh' : H'.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ _).obj K) =
      H'.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_epi (H'.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj K))).mp
    rw [Iso.hom_inv_id_app, Functor.mapDerivedCategoryFactorsh_hom_app]
    have hq : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
    have hq' : (DerivedCategory.quotientCompQhIso C').inv.app
        ((H'.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
    have hi : (H'.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
    rw [hq, hq', hi]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    repeat first | erw [Category.id_comp] | erw [Category.comp_id]
    exact (H'.mapDerivedCategoryFactors.hom_inv_id_app K).symm
  have hfac := congrArg
    (fun a ↦ a ≫ G'.rightDerivedFunctor.map (H'.mapDerivedCategoryFactors.hom.app K)) hf
  erw [hh, hh'] at hfac
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hfac
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hfac
  have hu (A : CochainComplex C ℤ) : G.rightDerivedFunctorUnitQ A =
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj A) := by
    unfold Functor.rightDerivedFunctorUnitQ
    have hq : (DerivedCategory.quotientCompQhIso C).hom.app A = 𝟙 _ := rfl
    have hq' : (DerivedCategory.quotientCompQhIso D).inv.app
        ((G.mapHomologicalComplex (.up ℤ)).obj A) = 𝟙 _ := rfl
    rw [hq, hq']
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have hu' (A : CochainComplex C' ℤ) : G'.rightDerivedFunctorUnitQ A =
      G'.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj A) := by
    unfold Functor.rightDerivedFunctorUnitQ
    have hq : (DerivedCategory.quotientCompQhIso C').hom.app A = 𝟙 _ := rfl
    have hq' : (DerivedCategory.quotientCompQhIso D').inv.app
        ((G'.mapHomologicalComplex (.up ℤ)).obj A) = 𝟙 _ := rfl
    rw [hq, hq']
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rw [hu, hu']
  have hq {A B : CochainComplex D' ℤ} (t : A ⟶ B) :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) =
        DerivedCategory.Q.map t := by
    have hnat := DerivedCategory.quotientCompQhIso_hom_naturality t
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map t) ≫
      𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map t at hnat
    simpa only [Category.id_comp, Category.comp_id] using hnat
  simp only [Functor.mapHomotopyCategory_obj, NatTrans.mapHomotopyCategory_app,
    HomotopyCategory.quotient_obj_as, hq] at hfac
  convert hfac using 1 <;> rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C']
  [HasDerivedCategory D'] [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions C'] [PreservesFiniteLimits H]
  [PreservesFiniteColimits H] [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] in
private theorem exchange_single (b : G ⋙ H ⟶ H' ⋙ G') (M : C) :
    (H.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M) ≫
      (NatTrans.mapHomologicalComplex b (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (G'.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H' (.up ℤ) 0).hom.app M) =
    (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app (G.obj M) ≫
      (HomologicalComplex.single D' (.up ℤ) 0).map (b.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).inv.app (H'.obj M) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    repeat first | erw [CategoryTheory.Functor.map_id] | erw [Category.id_comp] |
      erw [Category.comp_id]
    try rfl
  · simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ hn,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_ne _ _ hn,
      Functor.map_zero]
    repeat first | erw [zero_comp] | erw [comp_zero]

/-- The comparison (G M)[0] to RG(M[0]), induced by the right-derived unit.
Source: Stacks Derived Categories, 09T5; node proof step 4
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def degreeZeroUnit {A : Type uC} {B : Type uD} [Category.{vC} A] [Category.{vD} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wC} A] [HasDerivedCategory.{wD} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] (M : A) :
    (DerivedCategory.singleFunctor B 0).obj (F.obj M) ⟶
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor A 0).obj M) :=
  (DerivedCategory.singleFunctorIsoCompQ B 0).hom.app (F.obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnitQ ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.singleFunctorIsoCompQ A 0).inv.app M)

/-- The derived exchange on M[0], with the target identified with (H'M)[0].
Source: Stacks Derived Categories, 09T5; node proof step 4
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def degreeZeroExchange (b : G ⋙ H ⟶ H' ⋙ G') (M : C) :
    H.mapDerivedCategory.obj
        (G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ⟶
      G'.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C' 0).obj (H'.obj M)) :=
  (exchange G G' H H' b).app ((DerivedCategory.singleFunctor C 0).obj M) ≫
    G'.rightDerivedFunctor.map ((H'.mapDerivedCategorySingleFunctor 0).hom.app M)

/-- Compatibility with the two degree-zero derived-unit comparisons.
Source: Stacks Derived Categories, 09T5; node proof step 4
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction).
Proof: the universal rightDerivedDesc factorization is exactly compatibility with
units on every homotopy object. Evaluate it on M[0]. The quotient, single-complex
and exact-functor comparison isomorphisms give precisely the displayed equality.
Equivalently, naturality of b on M[0] to I, followed by a resolution of H'I, gives
b_I H(Ga) = G'(H'a) b_M[0]. The two resolution arrows are the two derived units. -/
theorem degreeZeroExchange_normalization (b : G ⋙ H ⟶ H' ⋙ G') (M : C) :
    H.mapDerivedCategory.map (degreeZeroUnit G M) ≫
        degreeZeroExchange G G' H H' b M =
      (H.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) ≫
        (DerivedCategory.singleFunctor D' 0).map (b.app M) ≫
        degreeZeroUnit G' (H'.obj M) := by
  let K := (HomologicalComplex.single C (.up ℤ) 0).obj M
  let g := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M
  let h := (HomologicalComplex.singleMapHomologicalComplex H' (.up ℤ) 0).hom.app M
  have hs : (H.mapDerivedCategorySingleFunctor 0).hom.app (G.obj M) =
      H.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single D (.up ℤ) 0).obj (G.obj M)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app
            (G.obj M)) := by
    apply (cancel_epi (H.mapDerivedCategoryFactors.inv.app
      ((HomologicalComplex.single D (.up ℤ) 0).obj (G.obj M)))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact H.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (G.obj M)
  have hs' : (H'.mapDerivedCategorySingleFunctor 0).hom.app M =
      H'.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map h := by
    apply (cancel_epi (H'.mapDerivedCategoryFactors.inv.app K)).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact H'.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M
  have hu : degreeZeroUnit G M = DerivedCategory.Q.map g ≫
      G.rightDerivedFunctorUnitQ K := by
    simp [degreeZeroUnit, DerivedCategory.singleFunctorIsoCompQ, g, K]
  have hu' : degreeZeroUnit G' (H'.obj M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).inv.app
          (H'.obj M)) ≫
        G'.rightDerivedFunctorUnitQ
          ((HomologicalComplex.single C' (.up ℤ) 0).obj (H'.obj M)) := by
    simp [degreeZeroUnit, DerivedCategory.singleFunctorIsoCompQ]
  rw [hu, hu', hs]
  dsimp only [degreeZeroExchange]
  rw [hs', Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% exchange_complex_fac G G' H H' b K]
  erw [← G'.rightDerivedFunctorUnitQ_naturality h]
  erw [H.mapDerivedCategoryFactors_hom_naturality_assoc g]
  simp only [← DerivedCategory.Q.map_comp_assoc]
  erw [exchange_single G G' H H' b M]
  simp only [DerivedCategory.Q.map_comp, Category.assoc]
  rfl

end Derivation

/-- The canonical exchange for the coefficient rings and actions in the statement.
Its target uses h' inverse image of M, placed in degree zero, over h' inverse image
of the coefficient ring. Source: Stacks Tag 09C9, ordinary-module realization
(blueprint: lem-sf-continuous-adic-proper-base-change-restriction). -/
def properExchange {P T T' : Scheme.{u}} (p : P ⟶ T) (h : T' ⟶ T)
    (M : proEtaleRingModules P (coefficientRing l P)) :=
  degreeZeroExchange
    (direct p (coefficientRing l T) (coefficientRing l P) (coefficientMap l p))
    (direct (pullback.snd p h) (inverseRing h (coefficientRing l T))
      (inverseRing (pullback.fst p h) (coefficientRing l P))
      (restrictedMap p h (coefficientRing l T) (coefficientRing l P) (coefficientMap l p)))
    (proEtaleModuleInverseImage h (coefficientRing l T))
    (proEtaleModuleInverseImage (pullback.fst p h) (coefficientRing l P))
    (ordinaryExchange p h (coefficientRing l T) (coefficientRing l P) (coefficientMap l p)) M

/-- Proper base change under quasi-compact locally closed restriction, in the actual
ordinary derived categories of continuous adic module sheaves, with normalization.

Source: Stacks proetale.tex, Tag 09C9 (finite-stage input); Bhatt--Scholze 6.8.1,
6.8.3, 6.8.6, 6.8.8 and Remark 6.8.15; blueprint ordinary rational proper base change,
clause 3 (blueprint: lem-sf-continuous-adic-proper-base-change-restriction).

Proof plan, following the node:
1. Identify the finite-span ring with finite-subextension condensed coefficients:
   a finite basis generates a finite extension, and conversely. Sheafification
   identifies the locally finite-span and bounded-function presentations
   (sk-def-sfb-qlbar-condensed; def-weil-pbc-condensed-qbar-coefficient-construction).
2. Finite-stage chart naturality and the coefficient colimit identify the actual
   coefficient maps, hence their inverse-image identifications are cartesian
   (lem-weil-pbc-continuous-chart-scheme-naturality; sk-prop-sfb-qlbar-colimit-x;
   sk-prop-sfb-cartesian-coefficients).
3. The internal/sectionwise module equivalence and coefficient transport are exact
   and compare ordinary direct images, inverse images, units and counits. They
   preserve K-injectives because their inverse equivalences are exact
   (def-weil-pbc-internal-abelian-sheaf-module-equivalence;
   lem-weil-pbc-right-adjoint-preserves-kinjective;
   lem-pd-module-ringed-topos-derived-comparison).
4. On a K-injective resolution I of M[0], followed by a resolution of h' inverse
   image of I, the defined exchange is bc_I followed by p' pushforward of the latter
   resolution. Naturality gives the displayed derived-unit equation
   (prop-pur-kinjective-resolutions-exist;
   lem-sfb-resolving-derived-adjunction-normalization).
5. Open restriction is slice restriction and preserves K-injectives. Therefore the
   ordinary open counit comparison derives without any separatedness assumption
   (lem-sfb-proetale-open-restriction-counit;
   lem-weil-proetale-weakly-etale-localization;
   lem-weil-pbc-proetale-ringed-open-comparison; lem-pur-kinjective-restrict-localized).
6. Localize T on affine opens. All four corners there are separated and finite
   type over k, by proper base change, Noetherianity and finite-type permanence
   (lem-weil-pbc-finite-type-over-noetherian; lem-weil-pbc-proper-fp-permanence;
   lem-sfb-finite-type-composition-base-change; lem-weil-pbc-affine-source-morphism-separated).
7. Refine the local finite partitions on the Noetherian source to a finite global
   stratification. Finite free modules are finitely presented, so M[0] is bounded
   constructible (lem-weil-pbc-etale-stratification-local-gluing-core;
   sk-def-sfb-bounded-constructible; lem-weil-pbc-locally-noetherian-quasi-separated).
8. Apply det-thm-sfb-proper-base-change-rational, clause 3. Its exchange is the
   ambient counit mate by lem-sfb-derived-exchange-exact-normalization, and the
   adjunction-normalized module comparison carries it to this exact exchange.
9. Restrict the chosen resolutions to the affine pieces. The site composition
   comparison and the open counit equation identify the restricted ordinary mates,
   hence the restricted derived maps (lem-weil-pbc-site-morphism-composition).
10. The cone is zero on this open cover. Its cohomology sheaves vanish globally by
    lem-sfb-sheaf-cover-local-isomorphism, proving invertibility. Step 4 supplies
    normalization. Empty schemes, rank zero and the identity restriction are included. -/
theorem proper_base_change_restriction
    {k : Type u} [Field k] [IsAlgClosed k] (hc : ringChar k ≠ 0)
    (hl : l ≠ ringChar k) {P T T' : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k))]
    (p : P ⟶ T) [IsProper p] (h : T' ⟶ T) [IsImmersion h] [QuasiCompact h]
    (M : proEtaleRingModules P (coefficientRing l P))
    (hM : ∀ x : P, ∃ (U : Scheme.{u}) (j : U ⟶ P),
      IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
        ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (i : (a : Fin n) → Z a ⟶ U),
          (∀ a, IsImmersion (i a)) ∧ (∀ y : U, ∃! a, y ∈ Set.range (i a).base) ∧
          ∀ a, ∃ q : ((proEtaleModuleInverseImage (i a ≫ j)
            (coefficientRing l P)).obj M).LocalGeneratorsData.{u + 1},
            q.IsLocallyFreeData ∧ q.IsFiniteType) :
    IsIso (properExchange l p h M) ∧
      (proEtaleModuleInverseImage h (coefficientRing l T)).mapDerivedCategory.map
          (degreeZeroUnit (direct p (coefficientRing l T) (coefficientRing l P)
            (coefficientMap l p)) M) ≫ properExchange l p h M =
        ((proEtaleModuleInverseImage h (coefficientRing l T)).mapDerivedCategorySingleFunctor
          0).hom.app ((direct p (coefficientRing l T) (coefficientRing l P)
            (coefficientMap l p)).obj M) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((ordinaryExchange p h (coefficientRing l T) (coefficientRing l P)
              (coefficientMap l p)).app M) ≫
          degreeZeroUnit
            (direct (pullback.snd p h) (inverseRing h (coefficientRing l T))
              (inverseRing (pullback.fst p h) (coefficientRing l P))
              (restrictedMap p h (coefficientRing l T) (coefficientRing l P)
                (coefficientMap l p)))
            ((proEtaleModuleInverseImage (pullback.fst p h) (coefficientRing l P)).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.ContinuousAdicRestriction
