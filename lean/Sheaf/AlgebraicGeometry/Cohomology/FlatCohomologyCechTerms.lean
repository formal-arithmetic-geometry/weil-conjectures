/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Canonical degree maps for affine Cech base change

Source: Stacks Project, Tags 02KH and 02KG, the separated-case Cech argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- Canonical scalar extension gives isomorphisms of the individual Cech terms.
This assertion concerns only the objects in each degree, not the differentials.

Source: Stacks Project, Tags 02KH (separated-case proof) and 02KG.
(blueprint: lem-pc-flat-cech-base-change-terms)

Proof: A tuple of length k+1 has at least one entry. Induction on its length and
separatedness over the affine base show that its intersection is affine. Its
inverse image is the base change of this affine, hence affine. Apply the affine
pullback section formula to the quasi-coherent module. Transfer from tensorPullback
to the library pullback using uniqueness of left adjoints with their units. The
cartesian affine ring formula and tensor associativity give S tensor_R Gamma(M,W).
These identifications send b tensor s to b times the restricted adjunction unit.
There are finitely many tuples in each degree, so extension of scalars commutes
with their product. Take the product of the section isomorphisms and transport
through the categorical product-open identifications. This gives the displayed
isomorphisms and coordinate equation. With no indices the products are zero;
with an empty intersection its sections are zero. Neither case needs an extra
hypothesis. No flatness or assumption that the family covers X is used. -/
theorem exists_cechBaseChange_term_isos (f : X ⟶ Spec (.of R)) [IsSeparated f]
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent]
    (hI : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, baseChangeFst (S := S) f ⁻¹ᵁ U (y l)) ≤
        baseChangeFst (S := S) f ⁻¹ᵁ (⨅ l, U (y l))) :
    let g := baseChangeFst (S := S) f
    let V : ι → (baseChangedScheme (S := S) f).Opens := fun i ↦ g ⁻¹ᵁ U i
    let N := baseChangedModule (S := S) f M
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let Q := N.presheafModuleCat ⋙ ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    let C := (cechComplexFunctor U).obj P
    let A := ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).obj C
    let B := (cechComplexFunctor V).obj Q
    let a := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : C.X k) ↦
      M.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
        (TopCat.Presheaf.cechComplexFunctorπ U P k y x)
    let z := fun (k : ℕ) (y : Fin (k + 1) → ι) (x : B.X k) ↦
      N.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj V y)).op
        (TopCat.Presheaf.cechComplexFunctorπ V Q k y x)
    ∃ e : ∀ k, A.X k ≅ B.X k,
      let c := fun k ↦ (e k).hom
      ∀ (k : ℕ) (y : Fin (k + 1) → ι) (b : S) (x : C.X k),
      z k y (c k (b ⊗ₜ[R] x)) =
        ((baseChangedScheme (S := S) f).presheaf.map
          (homOfLE (le_top : (⨅ l, V (y l)) ≤ ⊤)).op).hom
          (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
          N.presheaf.map (homOfLE (hI k y)).op
            ((baseChangeUnit (S := S) f M).val.app (op (⨅ l, U (y l))) (a k y x)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
