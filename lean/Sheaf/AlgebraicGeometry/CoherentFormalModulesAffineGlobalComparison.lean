/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # The affine formal equivalence with its two natural comparisons

Source: Stacks Project, Tags 087W, 01IB and 00MA.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On any affine Noetherian scheme, the finite completed-module equivalence has
its prescribed quotient-system realization and its natural section-limit realization.

Source: Stacks Project, Tag 087W, with the canonical affine chart of Tag 01IB and
finite-module completeness of Tag 00MA.
(blueprint: lem-weil-pbc-affine-global-formal-comparison).

Proof: Let A be the top section ring and I the top ideal. Pull back formal systems
along X.isoSpec.inv. The top ring map is GammaSpecIso.inv, so the transported ideal
is ofIdealTop (I.map GammaSpecIso.inv). Apply the equivalence of 087W over A and I
and compose its inverse with transport back to X. This gives E. The inverse
comparison of 087W identifies its underlying system with the completion of tilde
of the restricted finite module. Pullback along the affine chart commutes with
ideal products, powers, cokernels and the transition projections; uniqueness of
left adjoints identifies tensor pullback with Scheme.Modules.pullback. Thus these
comparisons give the first natural isomorphism. The cones in 087W identify the
restricted completed module with the inverse limit of its sections. Transporting
the cones across the chart gives cones on top sections of X: GammaSpecIso.inv
followed by the chart's top ring map is the identity on A. Their universal limit
isomorphisms give the second comparison. Naturality follows by composing with
each limit projection and using naturality of the transported cones. These
projections jointly distinguish maps. For I=0 the systems are constant; for I=A
both the completed ring and systems are zero. The argument also covers the empty
scheme and zero modules, without any nonzero-ring or proper-ideal assumption.
-/
theorem coherentFormalModules_affine_global_comparison
    (X : Scheme.{u}) [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let S := AdicCompletion I A
    let F := ObjectProperty.FullSubcategory
      (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q)
    let R := ObjectProperty.ι (fun Q : ModuleCat.{u} S ↦ Module.Finite S Q) ⋙
      ModuleCat.restrictScalars (algebraMap A S)
    let C := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom ⋙
      formalCompletionFunctor J
    let W := (Functor.whiskeringRight ℕᵒᵖ X.Modules (ModuleCat A)).obj
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))
    ∃ E : F ≌ CoherentFormalModule X J,
      Nonempty (E.functor ⋙ (IsCoherentFormalModule J).ι ≅ R ⋙ C) ∧
      Nonempty (R ≅ E.functor ⋙ (IsCoherentFormalModule J).ι ⋙ W ⋙ lim) := by sorry

end AlgebraicGeometry
