/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechTerms
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechDifferential

/-! # The termwise scalar extension of a finite affine Cech complex

Source: Stacks Project, Tags 02KH and 02KG, the separated-case Cech argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- The presheaf of R-modules obtained from the displayed map to Spec R.
Source: Stacks Project, Tag 02KH, the Cech complex over the affine base. -/
noncomputable def presheafOver (f : X ⟶ Spec (.of R)) (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  M.presheafModuleCat ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)

/-- The ordered Cech complex, with scalars restricted to the affine base.
Source: Stacks Project, Tag 02KH, the separated-case paragraph. -/
noncomputable def cechOver (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (cechComplexFunctor U).obj (presheafOver f M)

/-- The cover obtained by inverse image under the base-change projection.
Source: Stacks Project, Tag 02KH. -/
noncomputable def baseChangeCover (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) :
    ι → (baseChangedScheme (S := S) f).Opens :=
  fun i ↦ baseChangeFst (S := S) f ⁻¹ᵁ U i

/-- Scalar extension on the ordered Cech complex.
Source: Stacks Project, Tag 02KH. -/
noncomputable abbrev tensorCech (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules) :=
  ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℕ)).obj
    (cechOver f U M)

/-- Inverse images of tuple intersections are contained in the inverse image intersection.
Source: elementary inverse-image calculus in the Cech argument of Stacks Tag 02KH. -/
lemma baseChangeCover_intersection_le (f : X ⟶ Spec (.of R)) (U : ι → X.Opens)
    (k : ℕ) (y : Fin (k + 1) → ι) :
    (⨅ l, baseChangeCover (S := S) f U (y l)) ≤
      baseChangeFst (S := S) f ⁻¹ᵁ (⨅ l, U (y l)) := by
  intro x hx
  change x ∈ (↑(⨅ l, baseChangeCover (S := S) f U (y l)) : Set _) at hx
  rw [TopologicalSpace.Opens.coe_iInf] at hx
  change (baseChangeFst (S := S) f).base x ∈ (↑(⨅ l, U (y l)) : Set _)
  rw [TopologicalSpace.Opens.coe_iInf]
  simpa [baseChangeCover, Set.mem_iInter] using hx

/-- The coordinate of an ordered Cech cochain on a tuple intersection.
Source: the coordinate description of ordered Cech complexes, Stacks Tag 02KH. -/
noncomputable def cechCoordinate (f : X ⟶ Spec (.of R)) (U : ι → X.Opens)
    (M : X.Modules) (k : ℕ) (y : Fin (k + 1) → ι) :
    (cechOver f U M).X k → Γ(M, ⨅ l, U (y l)) :=
  fun x ↦ M.presheaf.map (homOfLE (TopCat.Presheaf.iInf_le_piObj U y)).op
    (TopCat.Presheaf.cechComplexFunctorπ U (presheafOver f M) k y x)

/-- A Cech comparison is canonical when its coordinates send b tensor x to b times
pullback of the corresponding section via the module adjunction unit. This predicate
specifies a chain map without assuming it is invertible.
Source: Stacks Project, Tags 02KG and 02KH, canonical affine-section comparison. -/
def IsCechBaseChange (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) : Prop :=
  ∀ (k : ℕ) (y : Fin (k + 1) → ι) (b : S) (x : (cechOver f U M).X k),
    cechCoordinate (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M) k y (c.f k (b ⊗ₜ[R] x)) =
      ((baseChangedScheme (S := S) f).presheaf.map
        (homOfLE (le_top : (⨅ l, baseChangeCover (S := S) f U (y l)) ≤ ⊤)).op).hom
        (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom b) •
        (baseChangedModule (S := S) f M).presheaf.map
          (homOfLE (baseChangeCover_intersection_le (S := S) f U k y)).op
          ((baseChangeUnit (S := S) f M).val.app (op (⨅ l, U (y l)))
            (cechCoordinate f U M k y x))

/-- On a finite affine cover of a scheme separated over Spec R the canonical Cech
comparison is a chain isomorphism. Flatness is not needed at the chain level.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), separated-case paragraph, and
Lemma 30.5.1 (Tag 02KG). -/
theorem exists_cechBaseChange_iso (f : X ⟶ Spec (.of R)) [IsSeparated f]
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] :
    ∃ c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M), IsCechBaseChange f U M c ∧ IsIso c := by
  obtain ⟨e, he⟩ := exists_cechBaseChange_term_isos (S := S) f U hU M
    (baseChangeCover_intersection_le (S := S) f U)
  have hd := cechBaseChange_components_comm (S := S) f U M
    (baseChangeCover_intersection_le (S := S) f U) (fun k ↦ (e k).hom) he
  let c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M) :=
    CochainComplex.ofHom (fun k ↦ (e k).hom) hd
  refine ⟨c, ?_, ?_⟩
  · exact he
  · have : ∀ k, IsIso (c.f k) := fun k ↦ (e k).isIso_hom
    exact HomologicalComplex.Hom.isIso_of_components c

end AlgebraicGeometry.Scheme.Modules
