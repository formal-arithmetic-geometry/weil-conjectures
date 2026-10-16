/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.Paper.CondensedQbarCoefficientConstruction

import Sheaf.Paper.CondensedQbarFieldEvaluationLinearity

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Algebraically closed field extension preserves the constructed module evaluation.

Source: Bhatt--Scholze, Example 4.1.10; RefactorInstruction, Section 4, geometric
fiber comparison in the finite-matrix refinement, steps 1--3
(blueprint: lem-weil-pbc-condensed-qbar-field-fiber-extension).

Proof: use the concrete scalar-linearity theorem for the canonical abelian
comparison. The comparison is invertible by geometric field evaluation under
extension. ModuleCat.isoMk lifts it to module isomorphisms; its sheaf naturality
proves naturality on modules. Finally, extendScalarsIsoComapInv identifies the
restriction-along-inverse formula with the actual module inverse image.
-/
theorem condensedQbar_fieldFiber_extension (ℓ : ℕ) [Fact ℓ.Prime]
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') : Nonempty
    (CondensedQbarGeometricEvaluation.fieldFiber K ℓ ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
        (Spec.map (CommRingCat.ofHom i)) ⋙
          CondensedQbarGeometricEvaluation.fieldFiber K' ℓ) := by
  let f := Spec.map (CommRingCat.ofHom i)
  let A := condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of K))
  let H := upperStar Ab.{u + 1} f
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f
  let R := H.mapMod A ⋙ Mod.comap (inv α)
  let E := CondensedQbarGeometricEvaluation.fieldFiber K' ℓ
  have : IsIso (geometricFieldEvaluationComparison f Ab.{u + 1}) :=
    (geometric_field_proetale_evaluation_extension K K' i).2.2.2.2.1
  let τ := asIso (geometricFieldEvaluationComparison f Ab.{u + 1})
  let e : CondensedQbarGeometricEvaluation.fieldFiber K ℓ ≅ R ⋙ E := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · refine ModuleCat.isoMk (τ.app M.X) ?_
      intro r
      exact condensedQbar_field_evaluation_linear ℓ K K' i M r
    · intro M N g
      apply (forget₂ (ModuleCat (PadicAlgCl ℓ)) Ab).map_injective
      change g.hom.hom.app _ ≫ (geometricFieldEvaluationComparison f Ab).app N.X =
        (geometricFieldEvaluationComparison f Ab).app M.X ≫
          ((Scheme.proEtaleSheafInverseImage f Ab).map g.hom).hom.app _
      exact (geometricFieldEvaluationComparison f Ab).naturality g.hom
  refine ⟨e ≪≫ ?_⟩
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (H.mapMod A) (Mod.extendScalarsIsoComapInv α).symm) E

end AlgebraicGeometry.ProEtale
