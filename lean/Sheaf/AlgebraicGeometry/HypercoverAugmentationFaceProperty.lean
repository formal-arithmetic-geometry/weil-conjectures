/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.CategoryTheory.MorphismPropertyHypercover
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.FlatEtaleRingedMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial
import Sheaf.AlgebraicTopology.GlueSimplex
import Sheaf.Paper.SimplicialSetAddSimplices
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact

/-! # Covering properties of hypercover augmentations and faces

Source: Stacks Project, Hypercoverings, Tag 0DER; Morphisms of Spaces, Tag 073C;
Modules on Sites, Tag 04JC (blueprint: lem-sfb-hypercover-augmentation-face-property).

Matching cones are taken in the slice, including its terminal object in degree zero.
The ringed flatness clause uses exact scalar extension along the adjoint of the
canonical structural ring map. Its left adjoint is precisely tensoring with the
structure sheaf over the inverse-image ring. Thus no extra choice of ring map or
geometric morphism enters the statement.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

/-- Augmentations, faces and all injective simplicial operators of a P-hypercover lie in P.
Source: Stacks, Tag 0DER (blueprint: lem-sfb-hypercover-augmentation-face-property).
Proof: work in C/X. Compatible families on finite simplicial sets are represented by
finite limits, using [lem-weil-pbc-simplicial-index-finite-initial]; the empty family is
represented by X. The simplex represents U_n, and its boundary represents the matching
object by [lem-weil-pbc-matching-object-proper-faces]. Attaching one nondegenerate simplex
is a pushout [lem-weil-pbc-simplicial-set-glue-simplex]; applying Hom into U gives a
pullback of its matching arrow. Its restriction map lies in P by base-change stability.
Filter each face inclusion into a simplex by finitely many such attachments using
[lem-weil-pbc-simplicial-set-add-simplices]. Composition gives every face in P.
Compose faces with the zero augmentation to obtain all augmentations. Factor every
injective order map into elementary faces to obtain the final clause; the equal-degree
case is an identity. No degeneracy is asserted to lie in P. -/
theorem hypercover_augmentation_face_property {C : Type u} [Category.{v} C]
    [HasFiniteLimits C] (P : MorphismProperty C)
    (hiso : ∀ {A B : C} (f : A ⟶ B), IsIso f → P f)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {X : C} (U : SimplicialObject (Over X)) (hU : IsMorphismPropertyHypercover P U) :
    (∀ n : ℕ, P (U.obj (op ⦋n⦌)).hom) ∧
    (∀ (n : ℕ) (i : Fin (n + 2)), P (U.δ i).left) ∧
    (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌), Function.Injective φ.toOrderHom →
      P (U.map φ.op).left) := by
  sorry

end CategoryTheory.SimplicialObject

namespace AlgebraicGeometry.AlgebraicSpace

/-- Fppf hypercovers of arbitrary algebraic spaces have fppf augmentation and face maps;
their canonical ringed étale maps are flat and their module tensor pullbacks are exact.
The same holds for every injective simplicial operator.
Source: Stacks, Tags 0DER, 0DHF, 073C and 04JC
(blueprint: lem-sfb-hypercover-augmentation-face-property).
Proof: algebraic-space fibre products [lem-trf-space-fibre-products-etale-covers] give
finite limits in the slice. The conjunction flat, locally finitely presented and
surjective contains isomorphisms and is stable under composition and base change by
[lem-sfb-stack-chartwise-smooth-etale-calculus]. Apply the general attachment argument
above. For each resulting flat map, [lem-sfb-space-flat-etale-ringed-comparison], Tag
073C, identifies chartwise flatness with flatness of O over the inverse-image ring.
This is exact scalar extension, as in [def-pc-flat-sheaf-modules]. The geometric inverse
image is exact [lem-trf-geometric-inverse-image-exact]. Its composite with scalar
extension is the canonical tensor pullback of [def-trf-space-etale-module-functors],
so it is exact by Tag 04JC. This applies equally to every augmentation and injective
operator. No separation, Noetherian or finite-type assumption and no degeneracy
flatness enters the argument. -/
theorem fppf_hypercover_augmentation_face_property {S : Scheme.{u}}
    {X : AlgebraicSpace S} (U : SimplicialObject (Over X))
    (hU : U.IsMorphismPropertyHypercover
      (fun _ _ f ↦ MapIsFlat f ∧ MapIsLocallyOfFinitePresentation f ∧
        Function.Surjective (mapPoint f.hom.hom))) :
    (∀ n : ℕ, MapIsFlat (U.obj (op ⦋n⦌)).hom ∧
      MapIsLocallyOfFinitePresentation (U.obj (op ⦋n⦌)).hom ∧
      Function.Surjective (mapPoint (U.obj (op ⦋n⦌)).hom.hom.hom) ∧
      IsFlatEtaleRingedMap (U.obj (op ⦋n⦌)).hom ∧
      exactFunctor _ _ (moduleTensorPullback (U.obj (op ⦋n⦌)).hom)) ∧
    (∀ (n : ℕ) (i : Fin (n + 2)), MapIsFlat (U.δ i).left ∧
      MapIsLocallyOfFinitePresentation (U.δ i).left ∧
      Function.Surjective (mapPoint (U.δ i).left.hom.hom) ∧
      IsFlatEtaleRingedMap (U.δ i).left ∧
      exactFunctor _ _ (moduleTensorPullback (U.δ i).left)) ∧
    (∀ (m n : ℕ) (φ : ⦋m⦌ ⟶ ⦋n⦌), Function.Injective φ.toOrderHom →
      MapIsFlat (U.map φ.op).left ∧
      MapIsLocallyOfFinitePresentation (U.map φ.op).left ∧
      Function.Surjective (mapPoint (U.map φ.op).left.hom.hom) ∧
      IsFlatEtaleRingedMap (U.map φ.op).left ∧
      exactFunctor _ _ (moduleTensorPullback (U.map φ.op).left)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
