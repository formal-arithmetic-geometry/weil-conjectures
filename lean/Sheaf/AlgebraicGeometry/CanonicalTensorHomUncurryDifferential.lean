/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHomModel
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.HomComplex

/-! # Differential compatibility of componentwise uncurrying

Source: Stacks Project, sites-cohomology.tex, Tag 0A90, and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-differential).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The actual coproduct extension of the uncurried components in total degree `n`.
Source: Stacks Project, Tag 0A90 (degreewise evaluation).
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
def schemeTensorHomUncurryGraded (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) (n : ℤ) :
    (pullbackTensorTotal X P L).X n ⟶ ((schemeHomKInjectiveResolution X).obj M).X n := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  exact HomologicalComplex.mapBifunctorDesc
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
    (fun p q h ↦ schemeTensorHomUncurryComponent X P L M φ p q n (by
      change p + q = n at h
      omega))

/-- The coproduct evaluation commutes with the total tensor differential.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90, differential calculation,
and cohomology.tex, Tag 08DJ.
(blueprint: lem-pc-tensor-hom-uncurry-differential).

Proof: Test equality on every coproduct summand P^p tensor L^q, p+q=n.
For m=n+1 the total differential is d_P tensor 1 plus (-1)^p times 1 tensor d_L.
Project the chain-map equation for φ to Hom(L^q,I(M)^m). The Hom differential
projection formula gives d_I φ_p minus (-1)^p φ_p d_L, while the other side is
φ_(p+1) d_P. Apply the sheaf tensor-Hom adjunction and its symmetry to this
identity. Naturality and additivity of the adjunction identify its three terms
with evaluation followed by d_I and the two total differential summands.
Move the signed L term to the other side. The coproduct universal property
then gives the displayed equality. For m different from n+1 both complex
differentials vanish by the shape axiom. This argument applies in all integer
degrees, to unbounded complexes, and also to zero complexes and zero φ. -/
theorem schemeTensorHomUncurryGraded_comm (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) (n m : ℤ) :
    schemeTensorHomUncurryGraded X P L M φ n ≫
        ((schemeHomKInjectiveResolution X).obj M).d n m =
      (pullbackTensorTotal X P L).d n m ≫
        schemeTensorHomUncurryGraded X P L M φ m := by sorry

/-- The chain map obtained by extending evaluation over the tensor coproducts.
Its data are explicit; only differential compatibility uses the preceding theorem.
Source: Stacks Project, Tag 0A90.
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
def schemeTensorHomUncurry (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M)) :
    pullbackTensorTotal X P L ⟶ (schemeHomKInjectiveResolution X).obj M where
  f := schemeTensorHomUncurryGraded X P L M φ
  comm' n m _ := schemeTensorHomUncurryGraded_comm X P L M φ n m

/-- Restricting coproduct evaluation to a summand recovers exactly the specified component.
Source: Stacks Project, Tag 0A90, coproduct universal property.
(blueprint: lem-pc-tensor-hom-uncurry-differential). -/
theorem schemeTensorHomUncurry_component (X : Scheme.{u})
    (P L M : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (φ : P ⟶ homComplex (R := X.sheaf) L
      ((schemeHomKInjectiveResolution X).obj M))
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    HomologicalComplex.ιMapBifunctor P L (curriedTensor _) (.up ℤ) p q n h ≫
        (schemeTensorHomUncurry X P L M φ).f n =
      schemeTensorHomUncurryComponent X P L M φ p q n h' := by
  let _ := SheafOfModules.monoidalCategory X.sheaf
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := P) (K₂ := L) (F := curriedTensor _) (c := .up ℤ)
    (fun p q h ↦ schemeTensorHomUncurryComponent X P L M φ p q n (by
      change p + q = n at h
      omega)) p q h

end AlgebraicGeometry
