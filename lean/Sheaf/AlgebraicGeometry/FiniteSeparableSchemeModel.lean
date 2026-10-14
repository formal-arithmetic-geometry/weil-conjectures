/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# A finite separable model of a finitely presented scheme

Source: Stacks Project, Tag 01ZM (1).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Every finitely presented scheme over a separable closure has a finitely presented model
 over a finite separable intermediate field. Write the separable closure as the filtered
 colimit of finitely generated subalgebras; these are fields because the extension is
 algebraic, finite because they are finitely generated, and separable because they lie in a
 separable extension. Apply finite-presentation descent to the spectra of that system.

Source: Stacks Project, Tag 01ZM (1).
(blueprint: lem-pd-finite-separable-scheme-model) -/
theorem exists_finiteSeparable_schemeModel {k ks : Type u} [Field k] [Field ks]
    [Algebra k ks] [IsSepClosure k ks] (Js : Over (Spec (.of ks)))
    [LocallyOfFinitePresentation Js.hom] [QuasiCompact Js.hom] [QuasiSeparated Js.hom] :
    ∃ K : IntermediateField k ks, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ (JK : Over (Spec (.of K))) (q : Js.left ⟶ JK.left),
        IsPullback q Js.hom JK.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K ks))) ∧
        LocallyOfFinitePresentation JK.hom ∧ QuasiCompact JK.hom ∧ QuasiSeparated JK.hom := by
  classical
  have : Algebra.IsSeparable k ks := IsSepClosure.separable
  have : Algebra.IsAlgebraic k ks := Algebra.IsSeparable.isAlgebraic k ks
  let I := {A : Subalgebra k ks // A.FG}
  have : Nonempty I := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩
  have : IsDirectedOrder I := ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩,
    show A.1 ≤ A.1 ⊔ B.1 from le_sup_left, show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩
  let D : Iᵒᵖ ⥤ Scheme.{u} := (CommRingCat.fgSubalgebraDiagramOf k ks).op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (CommRingCat.fgSubalgebraCoconeOf k ks).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (CommRingCat.isColimitFGSubalgebraCocone k ks).op
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Scheme.Spec.map _))
  have hDc (i : Iᵒᵖ) : CompactSpace (D.obj i) :=
    inferInstanceAs (CompactSpace (Spec _))
  have hDq (i : Iᵒᵖ) : QuasiSeparatedSpace (D.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec _))
  obtain ⟨i, Y, p, hp, hqc, hqs, q, hq⟩ :=
    Scheme.exists_isPullback_of_finitePresentation hc Js.hom
  have : Algebra.IsIntegral k i.unop.1 :=
    Algebra.IsIntegral.of_injective i.unop.1.val Subtype.val_injective
  let K : IntermediateField k ks := Algebra.IsAlgebraic.toIntermediateField i.unop.1
  have hK : FiniteDimensional k K := by
    have : Algebra.FiniteType k i.unop.1 :=
      (Subalgebra.fg_iff_finiteType i.unop.1).mp i.unop.2
    exact Algebra.IsIntegral.finite (R := k) (A := i.unop.1)
  have hKs : Algebra.IsSeparable k K := inferInstance
  refine ⟨K, hK, hKs, Over.mk p, q, ?_, hp, hqc, hqs⟩
  exact hq

end AlgebraicGeometry
