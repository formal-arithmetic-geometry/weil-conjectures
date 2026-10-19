/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Relative equidimensionality from a flat associated point

Source: Stacks Project, More on Morphisms, Tag 0GSJ (lemma-flat-associated-equidimensional),
with Tag 0GSI (lemma-associated-point-specializes) as the pointwise input
(blueprint: lem-trf-flat-associated-equidimensional).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The reduced closed subscheme carried by the closure of a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureSubscheme {X : Scheme.{u}} (x : X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme

/-- Inclusion of the reduced closure subscheme of a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureInclusion {X : Scheme.{u}} (x : X) : closureSubscheme x ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι

/-- The morphism between reduced point-closure subschemes induced by a scheme morphism.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def closureMap {X S : Scheme.{u}} (f : X ⟶ S) (y : X) :
    closureSubscheme y ⟶ closureSubscheme (f y) :=
  Scheme.IdealSheafData.subschemeMap
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩)
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {f y}, isClosed_closure⟩) f (by
      rw [Scheme.IdealSheafData.map_vanishingIdeal]
      apply (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal
        (I := Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {f y}, isClosed_closure⟩)
        (Z := TopologicalSpace.Closeds.closure (f '' (closure {y} : Set X)))).mp
      change closure (f '' (closure {y} : Set X)) ≤ (closure {f y} : Set S)
      apply closure_minimal
      · exact (image_closure_subset_closure_image f.continuous).trans (by simp)
      · exact isClosed_closure)

/-- The pullback module on a scheme-theoretic fibre.
Source: Stacks Project, More on Morphisms, Tag 0GSJ.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def fibreModule {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) :
    (f.fiber s).Modules :=
  (Scheme.Modules.tensorPullback (f.fiberι s)).obj F

/-- A point of a scheme-theoretic fibre is associated to the pulled-back module when the
maximal ideal of its local ring is an annihilator associated prime of its stalk.
Source: Stacks Project, Divisors, Tags 02OJ and 05AT.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def fibreAssociated {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    (x : f.fiber s) : Prop :=
  IsLocalRing.maximalIdeal ((f.fiber s).presheaf.stalk x) ∈
    RingTheory.annihilatorAssociatedPrimes
      ((f.fiber s).presheaf.stalk x)
      (((RingedSpace.moduleStalkFunctor (f.fiber s).toRingedSpace x).obj
        (fibreModule f F s)))

/-- The relative assassin of a finite-type quasi-coherent module, represented using the
associated point of the corresponding scheme-theoretic fibre.
Source: Stacks Project, Divisors, Tag 05AT.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def relativeAssassin {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Set X :=
  {x | ∃ z : f.fiber (f x), f.fiberι (f x) z = x ∧ fibreAssociated f F (f x) z}

/-- Stalkwise flatness of a module over the base at a point.
Source: Stacks Project, More on Morphisms, Tag 0GSJ; flatness convention Tag 01U4.
(blueprint: lem-trf-flat-associated-equidimensional). -/
def moduleFlatAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) : Prop :=
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F
  letI : Module (S.presheaf.stalk (f x)) M :=
    Module.compHom _ (f.stalkMap x).hom
  Module.Flat (S.presheaf.stalk (f x)) M

/-- A relative associated point whose fibre-closure has flat stalks at all fibre-component
 generic points yields relative association of those points and one common fibre dimension.
Source: Stacks Project, More on Morphisms, Tag 0GSJ (lemma-flat-associated-equidimensional),
parts (1) and (2), using Tag 0GSI pointwise.

Proof (deferred): identify the fibre of the reduced closure over the closure of `f y` with
its fibre over `S`, and use locally finite type fibre dimension to obtain a finite nonnegative
integer from the fibre at `f y`.  For each component, sobriety supplies its generic point;
the pointwise specialization theorem of Tag 0GSI gives relative association and equality
with this fixed dimension.  This proves both the association clause and equidimensionality.
(blueprint: lem-trf-flat-associated-equidimensional). -/
theorem flat_associated_equidimensional
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ relativeAssassin f F)
    (hflat : ∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        ∀ x : (closureMap f y).fiber s,
          IsGenericPoint x C →
            moduleFlatAt f F (closureInclusion y ((closureMap f y).fiberι s x))) :
    (∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        ∀ x : (closureMap f y).fiber s,
          IsGenericPoint x C →
            closureInclusion y ((closureMap f y).fiberι s x) ∈ relativeAssassin f F) ∧
    (∃ d : ℕ, ∀ (s : closureSubscheme (f y)),
      ∀ C ∈ irreducibleComponents ((closureMap f y).fiber s),
        topologicalKrullDim C = (d : WithBot ℕ∞)) := by
  sorry

end AlgebraicGeometry
