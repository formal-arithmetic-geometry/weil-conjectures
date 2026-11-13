/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.FieldTheory.SeparableExtension

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingCore
import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreFieldEmbeddingTransport

/-! # Affine steps in the radicial generic field construction

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- A dominant generic field map and a compatible finite purely inseparable base
extension induce a dominant field map on the reduced generic pullback. -/
theorem exists_reduced_generic_fibre_field_embedding
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
      (algebraMap L E).comp (algebraMap (S.residueField η) L))
    (hsep : Algebra.IsSeparablyGenerated k' E) :
    ∃ aE : Algebra (S'.residueField η') E,
      letI := aE
      ∃ h : Spec (.of E) ⟶
          ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
        IsSchemeTheoreticallyDominant h ∧
        Algebra.IsSeparablyGenerated (S'.residueField η') E ∧
        h ≫ ((pullback g q).nilradical.subschemeι ≫
          pullback.snd g q).fiberToSpecResidueField η' =
            Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') E)) := by
  obtain ⟨aE, h, hdom, hbase, hcompat⟩ :=
    exists_reduced_generic_fibre_field_embedding_core g q η η' hq hη' L k' E
      j hj hjbase e he hsquare
  let := aE
  have hsep' := separablyGenerated_of_residueField_equiv
    (K := S'.residueField η') (K' := k') (E := E) e hcompat hsep
  exact ⟨aE, h, hdom, hsep', hbase⟩

end AlgebraicGeometry
