/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.KummerCoefficientModels
public import Sheaf.Paper.KummerLocalSource
public import Sheaf.Paper.VectorPurityScalarSingle
public import Sheaf.CategoryTheory.CondensedDerivedInvariants
public import Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity

/-! # Canonical maps used in Kummer stratum scalar detection

Source: main-20261015 direct-images proof (3), normalized scalar adjunction maps.
(blueprint: def-sfb-kummer-stratum-scalar-maps).

## Main definitions

* `kummerScalarSingle` and `kummerScalarTheta`: the normalized geometric maps.
* `kummerPointScalarComparison`: the scalar-unit-preserving point comparison.
* `kummerStratumInvariantUnit` and `kummerStratumSigma`: the actual invariant maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar

variable {R R' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj R'] [IsCommMonObj R']
  (t : R ⟶ R') [IsMonHom t]

/-- The canonical degree-zero scalar comparison is the adjunct of the ordinary
coefficient unit, followed by exact restriction's single-degree comparison.
Source: direct-image proof (3), scalar-unit-normalized iota
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerScalarSingle (W : Scheme.{u})
    (L : KummerModules R W) :
    ((Mod.extendScalars (coefficientMap t W)).leftDerivedFunctor).obj
        ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((Mod.extendScalars (coefficientMap t W)).obj L) :=
  WeilConjectures.PurityFiniteSetting.purityAdjunctionSingleMap
    (Mod.extendScalars (coefficientMap t W))
    (Mod.comap (coefficientMap t W))
    ((Mod.extendScalars (coefficientMap t W)).leftDerivedFunctor)
    ((Mod.comap (coefficientMap t W)).mapDerivedCategory)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (Mod.extendRestrictAdjunction (coefficientMap t W))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap t W))
    ((Mod.comap (coefficientMap t W)).mapDerivedCategorySingleFunctor
      0) L

/-- Compose the specified scalar mate with direct image of the actual scalar-single map.
Source: direct-image proof (3), Theta
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerScalarTheta {W Y : Scheme.{u}} (a : W ⟶ Y)
    (L : KummerModules R W)
    (beta : ((Mod.extendScalars (coefficientMap t Y)).leftDerivedFunctor).obj
        ((moduleObjectDerivedPushforward R a).obj ((DerivedCategory.singleFunctor _ 0).obj L)) ⟶
      (moduleObjectDerivedPushforward R' a).obj
        (((Mod.extendScalars (coefficientMap t W)).leftDerivedFunctor).obj
          ((DerivedCategory.singleFunctor _ 0).obj L))) :
    ((Mod.extendScalars (coefficientMap t Y)).leftDerivedFunctor).obj
        ((moduleObjectDerivedPushforward R a).obj ((DerivedCategory.singleFunctor _ 0).obj L)) ⟶
      (moduleObjectDerivedPushforward R' a).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (coefficientMap t W)).obj L)) :=
  beta ≫ (moduleObjectDerivedPushforward R' a).map (kummerScalarSingle t W L)

/-- Ordinary unbounded scalar extension at the condensed point.
Source: direct-image proof (3), source of sigma
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
abbrev kummerPointScalarExtension :
    DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R) ⥤
      DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R') :=
  (Mod.extendScalars t).leftDerivedFunctor

/-- The scalar adjunct at the condensed point, using the canonical derived adjunction.
Source: direct-image proof (3), scalar adjunct of the invariant unit
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerPointAdjunct
    {N : DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)}
    {N' : DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R')}
    (b : N ⟶ (Mod.comap t).mapDerivedCategory.obj N') :
    (kummerPointScalarExtension t).obj N ⟶ N' :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction t).homEquiv N N').symm b

/-- The exact restriction/point-pullback comparison, obtained by deriving the actual
strong monoidal module comparison, with its canonical composition comparisons.
Source: direct-image proof (3), scalar-unit-preserving point comparisons
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerPointRestriction (S : Scheme.{u}) :
    derivedFromCondensed R' S ⋙
        (Mod.comap (coefficientMap t S)).mapDerivedCategory ≅
      (Mod.comap t).mapDerivedCategory ⋙
        derivedFromCondensed R S :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarFromPoint S).mapModComapIso t).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The scalar/pullback comparison from the point, specified as the scalar adjunct
of pullback of the actual scalar unit. No arbitrary map or comparison is supplied.
Source: direct-image proof (3), unit-preserving pullback/tensor comparison
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerPointScalarComparison (S : Scheme.{u})
    (N : DerivedCategory (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R)) :
    ((Mod.extendScalars (coefficientMap t S)).leftDerivedFunctor).obj
        ((derivedFromCondensed R S).obj N) ⟶
      (derivedFromCondensed R' S).obj
        ((kummerPointScalarExtension t).obj N) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap t S)).homEquiv _ _).symm
    ((derivedFromCondensed R S).map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        t).unit.app N) ≫
      (kummerPointRestriction t S).inv.app _)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (p : ℕ) {A : Type u} (I : Finset A)

/-- The full tame inertia group, including the trivial group for the empty subset.
Source: direct-image proof (3), G_I
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
abbrev kummerStratumInertia := ParameterRootDeckGroup p {i : A // i ∈ I}

/-- Ordinary derived internal continuous invariants of the actual condensed action.
Source: direct-image proof (3), R Gamma of M_(alpha,F)
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerStratumInvariants (B : Ring.{u})
    (N : Equivariant B (kummerStratumInertia p I)) :
    DerivedCategory (Modules B) :=
  (CondensedDerivedRestriction.derived B
    (kummerStratumInertia p I)).obj ((DerivedCategory.singleFunctor _ 0).obj N)

/-- Point inverse image of the actual derived invariant object, keeping the bundled
coefficient ring in its declared endpoints.
Source: direct-image proof (3), whole-stratum invariant model
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerStratumPointObject (B : Ring.{u}) (S : Scheme.{u})
    (N : Equivariant B (kummerStratumInertia p I)) :
    DerivedCategory (KummerModules B.X S) :=
  (derivedFromCondensed B.X S).obj (kummerStratumInvariants p I B N)

/-- The actual invariant coefficient map induced by the representation's unit.
Source: direct-image proof (3), rho_alpha
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerStratumInvariantUnit
    (M : PartialKummer.FiniteRepresentation E.1 (kummerStratumInertia p I))
    (c : KummerCoefficientModels ℓ E (kummerStratumInertia p I) M
      (CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E))) :
    kummerStratumInvariants p I (kummerCoefficientRing.{u} E.1) c.finite.object ⟶
      (Mod.comap (tameBoundaryScalarMap ℓ E)).mapDerivedCategory.obj
        (kummerStratumInvariants p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) c.closureForRing) :=
  CondensedDerivedRestriction.coefficientMap (kummerCoefficientMap ℓ E)
    ((DerivedCategory.singleFunctor _ 0).map c.unit ≫
      ((CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E)).functor
        |>.mapDerivedCategorySingleFunctor 0).inv.app c.closureForRing)

/-- Sigma is the scalar adjunct of the actual invariant coefficient map.
Source: direct-image proof (3), sigma_alpha
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerStratumSigma
    (M : PartialKummer.FiniteRepresentation E.1 (kummerStratumInertia p I))
    (c : KummerCoefficientModels ℓ E (kummerStratumInertia p I) M
      (CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E))) :
    (kummerPointScalarExtension (tameBoundaryScalarMap ℓ E)).obj
        (kummerStratumInvariants p I (kummerCoefficientRing.{u} E.1) c.finite.object) ⟶
      kummerStratumInvariants p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) c.closureForRing :=
  kummerPointAdjunct (tameBoundaryScalarMap ℓ E)
    (kummerStratumInvariantUnit ℓ E p I M c)


/-- The existing exact scalar restriction with bundled coefficient endpoints.
Source: direct-image proof (3), scalar restriction
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerRestrictionForRing (S : Scheme.{u}) :
    DerivedCategory (KummerModules (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X S) ⥤
      DerivedCategory (KummerModules (kummerCoefficientRing.{u} E.1).X S) :=
  kummerDerivedRestriction ℓ E S

/-- The existing coefficient-unit direct-image map with its bundled endpoints fixed.
Source: direct-image proof (3), normalized coefficient square
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerSourceScalarMapForRing {W Y S : Scheme.{u}} (a : W ⟶ Y) (v : S ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W) :
    kummerOpenImage (kummerCoefficientRing.{u} E.1).X a v L ⟶
      (kummerRestrictionForRing ℓ E S).obj
        (kummerOpenImage (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X a v
          (kummerOmegaModuleForRing ℓ E W L)) :=
  kummerSourceScalarMap ℓ E a v L

/-- The actual point-pulled invariant-unit arrow with the scalar restriction comparison.
Source: direct-image proof (3), right-hand side of the normalized coefficient square
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerStratumPointUnit (S : Scheme.{u})
    (M : PartialKummer.FiniteRepresentation E.1 (kummerStratumInertia p I))
    (c : KummerCoefficientModels ℓ E (kummerStratumInertia p I) M
      (CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E))) :
    kummerStratumPointObject p I (kummerCoefficientRing.{u} E.1) S c.finite.object ⟶
      (kummerRestrictionForRing ℓ E S).obj
        (kummerStratumPointObject p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) S
          c.closureForRing) :=
  (derivedFromCondensed (kummerCoefficientRing.{u} E.1).X S).map
      (kummerStratumInvariantUnit ℓ E p I M c) ≫
    (kummerPointRestriction (tameBoundaryScalarMap ℓ E) S).inv.app _

/-- The prescribed geometric beta on a degree-zero module, with bundled endpoints.
Source: direct-image proof (3), beta at L[0]
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerGeometricBeta {W Y : Scheme.{u}} (a : W ⟶ Y)
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W) :
    (tameBoundaryScalarExtension ℓ E Y).obj
        ((moduleObjectDerivedPushforward (kummerCoefficientRing.{u} E.1).X a).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)) ⟶
      (moduleObjectDerivedPushforward (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X a).obj
        ((tameBoundaryScalarExtension ℓ E W).obj
          ((DerivedCategory.singleFunctor _ 0).obj L)) :=
  tameBoundaryScalarComparison ℓ E a ((DerivedCategory.singleFunctor _ 0).obj L)

/-- The prescribed ordinary scalar functor with bundled coefficient endpoints.
Source: direct-image proof (3), T_S
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerScalarForRing (S : Scheme.{u}) :
    DerivedCategory (KummerModules (kummerCoefficientRing.{u} E.1).X S) ⥤
      DerivedCategory (KummerModules (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X S) :=
  tameBoundaryScalarExtension ℓ E S

/-- Component of the specified geometric scalar/pullback comparison, with its
bundled coefficient endpoints fixed before composing model maps.
Source: direct-image proof (3), unit-preserving comparison on v
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerScalarOpenPull {Y S : Scheme.{u}} (v : S ⟶ Y)
    (K : DerivedCategory (KummerModules (kummerCoefficientRing.{u} E.1).X Y)) :
    (upperStar (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X v).mapDerivedCategory.obj
        ((kummerScalarForRing ℓ E Y).obj K) ⟶
      (kummerScalarForRing ℓ E S).obj
        ((upperStar (kummerCoefficientRing.{u} E.1).X v).mapDerivedCategory.obj K) :=
  (tameBoundaryScalarPullIso ℓ E v).hom.app K

/-- Point scalar comparison with the two bundled coefficient endpoints fixed.
Source: direct-image proof (3), point scalar comparison
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
def kummerPointScalarForRing (S : Scheme.{u})
    (N : DerivedCategory (Modules (kummerCoefficientRing.{u} E.1))) :
    (kummerScalarForRing ℓ E S).obj
        ((derivedFromCondensed (kummerCoefficientRing.{u} E.1).X S).obj N) ⟶
      (derivedFromCondensed (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X S).obj
        ((kummerPointScalarExtension (R := (kummerCoefficientRing.{u} E.1).X)
          (R' := (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X)
          (tameBoundaryScalarMap ℓ E)).obj N) :=
  kummerPointScalarComparison (R := (kummerCoefficientRing.{u} E.1).X)
    (R' := (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X) (tameBoundaryScalarMap ℓ E) S N

/-- Point pullback of the prescribed sigma with the normalized scalar comparison.
Source: direct-image proof (3), p_S^* sigma
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerPointSigma (S : Scheme.{u})
    (M : PartialKummer.FiniteRepresentation E.1 (kummerStratumInertia p I))
    (c : KummerCoefficientModels ℓ E (kummerStratumInertia p I) M
      (CondensedDerivedRestriction.scalarAction (kummerCoefficientMap ℓ E))) :
    (kummerScalarForRing ℓ E S).obj
        (kummerStratumPointObject p I (kummerCoefficientRing.{u} E.1) S c.finite.object) ⟶
      kummerStratumPointObject p I (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) S
        c.closureForRing :=
  kummerPointScalarForRing ℓ E S
      (kummerStratumInvariants p I (kummerCoefficientRing.{u} E.1) c.finite.object) ≫
    (derivedFromCondensed (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X S).map
      (kummerStratumSigma ℓ E p I M c)

/-- The scalar-unit-normalized degree-zero arrow with its actual ordinary
Omega module as declared target.
Source: direct-image proof (3), iota
(blueprint: def-sfb-kummer-stratum-scalar-maps). -/
@[irreducible] def kummerSingleForRing (W : Scheme.{u})
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W) :
    (kummerScalarForRing ℓ E W).obj ((DerivedCategory.singleFunctor _ 0).obj L) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (kummerOmegaModuleForRing ℓ E W L) :=
  kummerScalarSingle (R := (kummerCoefficientRing.{u} E.1).X)
    (R' := (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X) (tameBoundaryScalarMap ℓ E) W L

end AlgebraicGeometry.ProEtale.CondensedRing
