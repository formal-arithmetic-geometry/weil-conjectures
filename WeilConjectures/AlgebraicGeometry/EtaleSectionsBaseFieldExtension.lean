/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime

/-!
# Étale sections after extension of a separably closed base field

## References

* Stacks Project, Tag 0A3I
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- Let `k` be separably closed, `K/k` a field extension, and `S` a `k`-scheme.
Pullback induces a bijection on sections of every sheaf of sets on `S`'s small étale site
(Stacks, Tag 0A3I). -/
theorem etale_sections_base_field_extension
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosed k]
    (S : Scheme.{u}) [S.Over (Spec (.of k))]
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤
          (pullback.fst (S ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
        (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        ((pullback (S ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).smallGrothendieckTopology
            @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S)))) := by
  refine etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres
    (pullback.fst (S ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ?_ F
  intro s
  let L := AlgebraicClosure (S.residueField s)
  let g : Spec (.of L) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) L)) ≫
      S.fromSpecResidueField s
  let a := S ↘ Spec (.of k)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let φ := (Spec.preimage (g ≫ a)).hom
  let : Algebra k L := φ.toAlgebra
  have hg : g ≫ a = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    exact (Spec.map_preimage (g ≫ a)).symm
  let e := pullbackSymmetry (pullback.fst a b) g ≪≫
    pullbackRightPullbackFstIso a b g ≪≫
    pullback.congrHom hg rfl ≪≫ pullbackSpecIso k L K
  exact e.schemeIsoToHomeo.connectedSpace_iff.mpr
    (IsSepClosed.field_tensor_unique_minimalPrime k L K).2.2

end AlgebraicGeometry
