/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.AlgebraicGeometry.AffineSectionsComplexCounit
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import Sheaf.AlgebraicGeometry.SchemeIsoPerfectTransport

/-! # Bounded projective models of ordinary affine sections

Source: Stacks Project, Tags 08EB, 0656, 06Z0 and 01IB.
(blueprint: lem-pc-affine-perfect-sections-projective-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary sections of a bounded-above quasi-coherent perfect complex on an affine
scheme have a bounded finite-projective representative in the ring derived category.
Source: Stacks Project, Tags 08EB (perfect-lemma-perfect-affine), 0656, 06Z0 and 01IB.
(blueprint: lem-pc-affine-perfect-sections-projective-model).

Proof: Transport D along the canonical affine chart Y.isoSpec to Spec Gamma(Y,O).
The affine quasi-coherent counits, natural in the differentials, identify this
transported complex with the termwise associated sheaf of the ordinary section
complex. Its homology sheaves are quasi-coherent because associated sheaves are
exact, so its derived image is an object of D_QCoh. Perfectness transports across
the scheme isomorphism. Apply the affine bounded-projective characterization to
obtain P with integer bounds and finite projective terms, and a derived isomorphism
between tilde(P) and the transported D. Compose with the termwise counit comparison.
Full faithfulness of the affine derived equivalence then lifts that isomorphism
and its inverse to the ring derived category, yielding the displayed isomorphism
between Q(P) and Q of ordinary sections of D. This argument avoids choosing an
injective resolution of D. For the empty affine scheme the section ring is the
zero ring and the zero complex is a representative. The result is existential;
no construction chooses an arbitrary witness of this unproved theorem. -/
theorem exists_affine_perfect_sections_projective_model
    (Y : Scheme.{u}) (hY : IsAffine Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    [HasDerivedCategory.{v} (ModuleCat.{u} (Γ(Y, ⊤) : Type u))]
    (D : CochainComplex Y.Modules ℤ) (d : ℕ)
    (hDle : D.IsStrictlyLE d)
    (hDqc : ∀ n : ℤ, (D.X n).IsQuasicoherent)
    (hperfect : Y.IsPerfect ((DerivedCategory.Q
      (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).obj D)) :
    ∃ (P : CochainComplex (ModuleCat.{u} (Γ(Y, ⊤) : Type u)) ℤ) (a b : ℤ),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
      (∀ n : ℤ, Module.Finite (Γ(Y, ⊤) : Type u) (P.X n)) ∧
      (∀ n : ℤ, Module.Projective (Γ(Y, ⊤) : Type u) (P.X n)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj
        (((SheafOfModules.evaluation.{u}
          (moduleRings Y.toRingedSpace) (op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D)) := by
  have _ := hDle
  let : IsAffine Y := hY
  let A := (Γ(Y, ⊤) : Type u)
  let S := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let : HasDerivedCategory.{u + 1} S := HasDerivedCategory.standard S
  let : ∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{u + 1}
        (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let G := @Functor.mapHomologicalComplex ℤ Y.Modules (ModuleCat.{u} A) _ _ _ _
    (SheafOfModules.evaluation.{u} (moduleRings Y.toRingedSpace) (op ⊤))
    ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)
  let M := G.obj D
  let T := @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A) S _ _ _ _
    (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)
  obtain ⟨e, ⟨cmp⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  let incl := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let E := e.functor.obj (DerivedCategory.Q.obj M)
  let hEM : E.obj ≅ DerivedCategory.Q.obj (T.obj M) := cmp.app M
  obtain ⟨s, ⟨scmp⟩⟩ := exists_scheme_iso_derived_equivalence Y.isoSpec.symm
  obtain ⟨c⟩ := affine_sections_complex_counit Y D hDqc
  let hs : s.functor.obj (DerivedCategory.Q.obj (T.obj M)) ≅ DerivedCategory.Q.obj D :=
    scmp.app (T.obj M) ≪≫ DerivedCategory.Q.mapIso c
  let hback : s.inverse.obj (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj (T.obj M) :=
    (s.inverse.mapIso hs).symm ≪≫ (s.unitIso.app _).symm
  have hTM : Scheme.IsPerfect (Spec (.of A)) (DerivedCategory.Q.obj (T.obj M)) := by
    have hp := scheme_iso_derived_inverse_preserves_perfect
      Y.isoSpec.symm s scmp (DerivedCategory.Q.obj D) hperfect
    intro x
    obtain ⟨U, hx, K, hK, ⟨hk⟩⟩ := hp x
    exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.mapIso
        hback.symm ≪≫ hk⟩⟩
  have hE : Scheme.IsPerfect (Spec (.of A)) E.obj := by
    intro x
    obtain ⟨U, hx, K, hK, ⟨hk⟩⟩ := hTM x
    exact ⟨U, hx, K, hK, ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.mapIso hEM ≪≫ hk⟩⟩
  obtain ⟨P, ⟨a, b, hb⟩, hf, hp, ⟨hEP⟩⟩ :=
    (perfect_iff_affine_bounded_projective A E).mp hE
  refine ⟨P, a, b, hb, hf, hp, ?_⟩
  let F := e.functor ⋙ incl
  let hPM : F.obj (DerivedCategory.Q.obj P) ≅ F.obj (DerivedCategory.Q.obj M) :=
    cmp.app P ≪≫ hEP.symm
  exact ⟨F.preimageIso hPM⟩

end AlgebraicGeometry.Scheme.Modules
