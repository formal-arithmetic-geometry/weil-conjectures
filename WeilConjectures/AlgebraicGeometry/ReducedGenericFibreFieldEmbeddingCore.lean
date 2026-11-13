/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreMapCore

/-!
# Field embedding for the reduced generic fibre: affine core

The affine core construction of a scheme-theoretically dominant map from `Spec E` into the
generic fibre of the reduced base change `(Z ×_S S')_red → S'`, where `E` is a common extension
of `L` and of a finite purely inseparable extension `k'` of the residue field.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry
/-- Core affine construction of the dominant map, omitting separable generation. -/
theorem exists_reduced_generic_fibre_field_embedding_core
    {Z S S' : Scheme.{u}} [IsAffine Z] [IsAffine S] [IsAffine S'] [IsIntegral S']
    (g : Z ⟶ S) (q : S' ⟶ S) (η : S) (η' : S') (hq : q η' = η)
    (hη' : IsGenericPoint η' Set.univ)
    (L k' E : Type u) [Field L] [Field k'] [Field E]
    [Algebra (S.residueField η) L] [Algebra (S.residueField η) k']
    [Algebra L E] [Algebra k' E]
    [Module.Finite (S.residueField η) k'] [IsPurelyInseparable (S.residueField η) k']
    (j : Spec (.of L) ⟶ g.fiber η) (hj : IsSchemeTheoreticallyDominant j)
    (hjbase : j ≫ g.fiberToSpecResidueField η =
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)))
    (e : S'.residueField η' ≃+* k')
    (he : e.toRingHom.comp
      (((S.residueFieldCongr hq).inv ≫ q.residueFieldMap η').hom) =
        algebraMap (S.residueField η) k')
    (hsquare : (algebraMap k' E).comp (algebraMap (S.residueField η) k') =
      (algebraMap L E).comp (algebraMap (S.residueField η) L)) :
    ∃ aE : Algebra (S'.residueField η') E,
      letI := aE
      ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) ∧
        ∀ x : S'.residueField η',
          algebraMap (S'.residueField η') E x = algebraMap k' E (e x) := by
  let aE : Algebra (S'.residueField η') E :=
    ((algebraMap k' E).comp e.toRingHom).toAlgebra
  obtain ⟨h, hh, hb⟩ := exists_reduced_generic_fibre_map_core
    g q η η' hq hη' L k' E j hj hjbase e he hsquare aE rfl
  refine ⟨aE, ?_⟩
  let _ := aE
  refine ⟨h, hh, hb, ?_⟩
  intro x
  rfl
end AlgebraicGeometry
