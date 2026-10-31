/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra

/-! # Symmetric graded algebras preserve module isomorphisms

Source: Stacks Project, Constructions, Tag 01OB.
(blueprint: def-pur-symmetric-graded-algebra-iso).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The symmetric-algebra equivalence induced by a linear equivalence.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
def symmetricSectionAlgebraCongr {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp e.toLinearMap))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp e.symm.toLinearMap))
    (by ext m; simp) (by ext m; simp)

/-- The symmetric-algebra equivalence sends an inclusion generator to its image.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
theorem symmetricSectionAlgebraCongr_ι {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (m : M) :
    symmetricSectionAlgebraCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- The symmetric-algebra equivalence on one affine section module.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
def symmetricSectionCongr {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (U : X.affineOpens) :
    sections F (op U.1) ≃ₐ[Γ(X, U.1)] sections G (op U.1) :=
  symmetricSectionAlgebraCongr
    ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).mapIso e).toLinearEquiv

/-- The affine section equivalence sends generators by the module isomorphism.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
theorem symmetricSectionCongr_ι {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (U : X.affineOpens) (m : F.val.obj (op U.1)) :
    symmetricSectionCongr e U (SymmetricAlgebra.ι _ _ m) =
      SymmetricAlgebra.ι _ _ (e.hom.val.app (op U.1) m) := by
  exact symmetricSectionAlgebraCongr_ι _ _

/-- The affine section equivalence preserves each symmetric degree.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
theorem symmetricSectionCongr_mem {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (U : X.affineOpens) (n : ℕ) (x : sections F (op U.1))
    (hx : x ∈ (SymmetricAlgebra.ι Γ(X, U.1) (F.val.obj (op U.1))).range ^ n) :
    symmetricSectionCongr e U x ∈
      (SymmetricAlgebra.ι Γ(X, U.1) (G.val.obj (op U.1))).range ^ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgEquiv.commutes]
    exact Submodule.algebraMap_mem _
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, symmetricSectionCongr_ι, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

/-- The degree-preserving affine section maps commute with restriction.
Source: Stacks Project, Tag 01OB
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
def symmetricGradedCongr {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G) :
    gradedAlgebraData F ⟶ gradedAlgebraData G where
  app U :=
    { toRingHom := (symmetricSectionCongr e U).toRingHom
      map_mem := fun {n} {x} hx ↦ symmetricSectionCongr_mem e U n x hx }
  app_algebraMap U r := (symmetricSectionCongr e U).commutes r
  naturality := by
    intro U V h x
    change symmetricSectionCongr e U (restriction F (homOfLE h).op x) =
      restriction G (homOfLE h).op (symmetricSectionCongr e V x)
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => simp only [restriction_algebraMap, AlgEquiv.commutes]
    | ι m =>
      let i := (homOfLE (X := X.Opens) h).op
      calc
        _ = SymmetricAlgebra.ι _ _ (e.hom.val.app (op U.1) (F.val.map i m)) :=
          (congrArg (symmetricSectionCongr e U) (restriction_ι F i m)).trans
            (symmetricSectionCongr_ι e U _)
        _ = SymmetricAlgebra.ι _ _ (G.val.map i (e.hom.val.app (op V.1) m)) :=
          congrArg (SymmetricAlgebra.ι _ _) (congrArg (fun q ↦ q m) (e.hom.val.naturality i))
        _ = restriction G i (SymmetricAlgebra.ι _ _ (e.hom.val.app (op V.1) m)) :=
          (restriction_ι G i _).symm
        _ = _ := congrArg (restriction G i) (symmetricSectionCongr_ι e V m).symm
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- A module isomorphism induces the degree-preserving symmetric-algebra isomorphism.
Its affine component is the symmetric algebra of the isomorphism on module sections.
Source: Stacks Project, Tag 01OB.
(blueprint: def-pur-symmetric-graded-algebra-iso). -/
noncomputable def gradedAlgebraIso {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G) :
    gradedAlgebraData F ≅ gradedAlgebraData G where
  hom := symmetricGradedCongr e
  inv := symmetricGradedCongr e.symm
  hom_inv_id := by
    apply Scheme.GradedAlgebraData.hom_ext
    intro U
    apply GradedRingHom.ext
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r =>
      change symmetricSectionCongr e.symm U
        (symmetricSectionCongr e U (algebraMap Γ(X, U.1) _ r)) = _
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
      rfl
    | ι m =>
      change symmetricSectionCongr e.symm U
        (symmetricSectionCongr e U (SymmetricAlgebra.ι _ _ m)) = _
      rw [symmetricSectionCongr_ι, symmetricSectionCongr_ι]
      change SymmetricAlgebra.ι _ _ (e.inv.val.app (op U.1)
        (e.hom.val.app (op U.1) m)) = SymmetricAlgebra.ι _ _ m
      exact congrArg (SymmetricAlgebra.ι _ _)
        (congrArg (fun f : F ⟶ F ↦ f.val.app (op U.1) m) e.hom_inv_id)
    | mul x y hx hy => simp_all only [map_mul]
    | add x y hx hy => simp_all only [map_add]
  inv_hom_id := by
    apply Scheme.GradedAlgebraData.hom_ext
    intro U
    apply GradedRingHom.ext
    intro x
    induction x using SymmetricAlgebra.induction with
    | algebraMap r =>
      change symmetricSectionCongr e U
        (symmetricSectionCongr e.symm U (algebraMap Γ(X, U.1) _ r)) = _
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
      rfl
    | ι m =>
      change symmetricSectionCongr e U
        (symmetricSectionCongr e.symm U (SymmetricAlgebra.ι _ _ m)) = _
      rw [symmetricSectionCongr_ι, symmetricSectionCongr_ι]
      change SymmetricAlgebra.ι _ _ (e.hom.val.app (op U.1)
        (e.inv.val.app (op U.1) m)) = SymmetricAlgebra.ι _ _ m
      exact congrArg (SymmetricAlgebra.ι _ _)
        (congrArg (fun f : G ⟶ G ↦ f.val.app (op U.1) m) e.inv_hom_id)
    | mul x y hx hy => simp_all only [map_mul]
    | add x y hx hy => simp_all only [map_add]

/-- The induced graded-algebra isomorphism acts on degree-one generators by the module map.
Source: Stacks Project, Tag 01OB (blueprint: def-pur-symmetric-graded-algebra-iso). -/
theorem gradedAlgebraIso_hom_app_ι {X : Scheme.{u}} {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (e : F ≅ G)
    (U : X.affineOpens) (m : F.val.obj (op U.1)) :
    (gradedAlgebraIso e).hom.app U (SymmetricAlgebra.ι _ _ m) =
      SymmetricAlgebra.ι _ _ (e.hom.val.app (op U.1) m) :=
  symmetricSectionCongr_ι e U m

end AlgebraicGeometry.SymmetricAlgebraSheaf
