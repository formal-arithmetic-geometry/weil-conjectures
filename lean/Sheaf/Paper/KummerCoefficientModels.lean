/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.KummerScalarRestriction
public import Sheaf.Paper.KummerStratumGeometry
public import Sheaf.Paper.KummerBarResolution

/-! # The two actual continuous coefficient models
Source: direct-image proof (3), E and Omega and the insertion-of-one map.
(blueprint: def-sfb-kummer-coefficient-models).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.CondensedBar

/-- Bundle the given all-continuous commutative ring object, retaining its structure.
Source: direct-image proof (3), coefficient convention
(blueprint: def-sfb-kummer-coefficient-models). -/
def kummerCoefficientRing (F : Type) [NormedField F] : Ring.{u} :=
  { X := Profinite.continuousMapRingObj F }

/-- Ordinary Omega extension with its bundled coefficient ring fixed explicitly.
The data is exactly the actual extension of scalars, with no choice of module.
Source: direct-image proof (3), ordinary scalar extension
(blueprint: def-sfb-kummer-coefficient-models). -/
def kummerOmegaModuleForRing (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (W : Scheme.{u})
    (L : KummerModules (kummerCoefficientRing.{u} E.1).X W) :
    KummerModules (kummerCoefficientRing.{u} (PadicAlgCl ℓ)).X W :=
  kummerOmegaModule ℓ E W L

/-- The continuous field inclusion as a bundled commutative ring-object morphism.
Source: direct-image proof (3), E to Omega
(blueprint: def-sfb-kummer-coefficient-models). -/
def kummerCoefficientMap (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    kummerCoefficientRing.{u} E.1 ⟶ kummerCoefficientRing (PadicAlgCl ℓ) :=
  ⟨⟨tameBoundaryScalarMap ℓ E⟩⟩

/-- The two condensations and the insertion-of-one map, normalized on every profinite
section by the actual continuous coordinate inclusion. This definition is dependent
only on the two already constructed condensations.
Source: direct-image proof (3), finite basis scalar extension
(blueprint: def-sfb-kummer-coefficient-models). -/
def KummerUnitCoordinates (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M : PartialKummer.FiniteRepresentation E.1 G)
    (r : ScalarAction (kummerCoefficientMap ℓ E) G)
    (ME : PartialKummer.Condensation M E.1 (RingHom.id E.1))
    (MO : PartialKummer.Condensation M (PadicAlgCl ℓ) E.1.subtype)
    (f : ME.object ⟶ r.functor.obj MO.object) : Prop :=
  ∀ (P : Profinite.{u}) (x : ME.object.module.X.obj.obj (op P)) (t : P) (i : Fin M.rank),
    (ULift.down ((MO.coordinates.hom.hom.hom.app (op P)).hom
      (((r.underlying.hom.app MO.object).hom.hom.app (op P)).hom
        ((f.val.hom.hom.app (op P)).hom x)))) t i =
      E.1.subtype ((ULift.down ((ME.coordinates.hom.hom.hom.app (op P)).hom x)) t i)

/-- The existing Omega condensation with its bundled action-category type fixed.
No action or coefficient data is replaced: this is the supplied condensation object.
Source: direct-image proof (3), all-continuous Omega representation
(blueprint: def-sfb-kummer-coefficient-models). -/
def kummerClosureActionForRing (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M : PartialKummer.FiniteRepresentation E.1 G)
    (MO : PartialKummer.Condensation M (PadicAlgCl ℓ) E.1.subtype) :
    Equivariant (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) G := MO.object

/-- Both coefficient modules are the existing all-continuous condensations of one
finite continuous representation, with the actual scalar insertion map.
Source: direct-image proof (3), M_(alpha,F)
(blueprint: def-sfb-kummer-coefficient-models). -/
structure KummerCoefficientModels (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (M : PartialKummer.FiniteRepresentation E.1 G)
    (r : ScalarAction (kummerCoefficientMap ℓ E) G) where
  finite : PartialKummer.Condensation M E.1 (RingHom.id E.1)
  closure : PartialKummer.Condensation M (PadicAlgCl ℓ) E.1.subtype
  closureForRing : Equivariant (kummerCoefficientRing.{u} (PadicAlgCl ℓ)) G
  closureForRing_eq : closureForRing = closure.object
  unit : finite.object ⟶ r.functor.obj closureForRing
  unit_coordinates : KummerUnitCoordinates ℓ E G M r finite closure
    (unit ≫ r.functor.map (eqToHom closureForRing_eq))

end AlgebraicGeometry.ProEtale.CondensedRing
