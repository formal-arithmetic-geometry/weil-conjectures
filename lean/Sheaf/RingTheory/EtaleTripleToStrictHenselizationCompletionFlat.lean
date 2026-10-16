/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.Finite
import Sheaf.RingTheory.EtaleResidueTriplesStrictHenselization
import Sheaf.RingTheory.StrictHenselizationCompletionFlatOverBase

/-!
# Flatness of etale triple maps to the completed strict henselization

Source: Stacks Project, More on Algebra, Tag 06LJ, proof of (c)
(blueprint: lem-sc-etale-triple-to-sh-completion-flat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every pointed etale algebra maps flatly to the completion of the strict henselization.
Source: Stacks Project, Tag 06LJ, proof of (c), paragraph beginning
“To finish the proof of (c)” (blueprint: lem-sc-etale-triple-to-sh-completion-flat).

Proof:
1. Transport the separable-closure structure from the scheme residue field to
`IsLocalRing.ResidueField R` using `stalkClosedPointIso`. The transported structural
map to `K` agrees with evaluation followed by the prescribed residue embedding.
2. Apply `lem-sc-etale-triples-colimit-is-strict-henselization` to the given ring
colimit, with its `R`-algebra structure induced by `ρ`. By
`lem-sc-strict-henselization-completion-flat-over-base`, its maximal-ideal completion
is flat over `R`.
3. The triple algebra is étale over `R`, hence formally unramified and essentially
of finite type. Its map to the completion respects `R` by `hρ`. Apply Mathlib's
`Algebra.FormallyUnramified.flat_of_restrictScalars`
(`lem-sc-unramified-flat-of-base-flat`) to obtain flatness over the triple algebra.
-/
theorem etaleTriple_to_strictHenselization_completion_flat
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (K : Type u) [Field K]
    [Algebra ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K]
    [IsSepClosure ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K]
    (c : Cocone (etaleResidueTriplesRingDiagram R
      ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K))))
    (hc : IsColimit c) (ρ : R ⟶ c.pt)
    (hρ : ∀ t, t.α ≫ c.ι.app t = ρ)
    (t : EtaleResidueTriples R ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ K
      (CommRingCat.ofHom (algebraMap
        ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K))) :
    ((algebraMap c.pt
      (AdicCompletion ((IsLocalRing.maximalIdeal R).map ρ.hom) c.pt)).comp
        (c.ι.app t).hom).Flat := by
  -- Use base flatness and the unramified scalar-restriction lemma directly.
  -- This avoids the localization and completion comparison of the original plan.
  classical
  let : Algebra ((Spec R).residueField (IsLocalRing.closedPoint R)) K :=
    inferInstanceAs (Algebra ((Spec R).residueField
      ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K)
  have : IsSepClosure ((Spec R).residueField (IsLocalRing.closedPoint R)) K :=
    inferInstanceAs (IsSepClosure ((Spec R).residueField
      ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K)
  let e : IsLocalRing.ResidueField R ≃+*
      ((Spec R).residueField (IsLocalRing.closedPoint R)) := (IsLocalRing.ResidueField.mapEquiv
    (AlgebraicGeometry.stalkClosedPointIso R).symm.commRingCatIsoToRingEquiv)
  let : Algebra (IsLocalRing.ResidueField R) K :=
    ((algebraMap ((Spec R).residueField (IsLocalRing.closedPoint R)) K).comp
      e.toRingHom).toAlgebra
  have : IsSepClosure (IsLocalRing.ResidueField R) K := by
    refine ⟨IsSepClosure.sep_closed ((Spec R).residueField (IsLocalRing.closedPoint R)), ?_⟩
    exact Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl K)
      (by ext x; exact congrArg _ (e.apply_symm_apply x))
  let : Algebra R K :=
    ((algebraMap (IsLocalRing.ResidueField R) K).comp
      (algebraMap R (IsLocalRing.ResidueField R))).toAlgebra
  have : IsScalarTower R (IsLocalRing.ResidueField R) K :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R c.pt := ρ.hom.toAlgebra
  have hχ : (ΓSpecIso R).inv ≫
      (Spec R).Γevaluation ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ ≫
      CommRingCat.ofHom (algebraMap
        ((Spec R).residueField ⟨IsLocalRing.maximalIdeal R, inferInstance⟩) K) =
      CommRingCat.ofHom (algebraMap R K) := by
    ext x
    change algebraMap ((Spec R).residueField (IsLocalRing.closedPoint R)) K
      (((ΓSpecIso R).inv ≫ (Spec R).Γevaluation (IsLocalRing.closedPoint R)).hom x) =
      algebraMap ((Spec R).residueField (IsLocalRing.closedPoint R)) K
        (e (algebraMap R (IsLocalRing.ResidueField R) x))
    congr 1
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    simp only [e]
    change _ = ((AlgebraicGeometry.stalkClosedPointIso R).inv ≫
      (Spec R).residue (IsLocalRing.closedPoint R)).hom x
    rw [Γevaluation, evaluation, ← AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hC : Algebra.IsStrictHenselization R K c.pt :=
    etaleResidueTriples_colimit_isStrictHenselization R _ K _ hχ c hc hρ
  let C := AdicCompletion ((IsLocalRing.maximalIdeal R).map ρ.hom) c.pt
  have hflat : (algebraMap R C).Flat :=
    Algebra.strictHenselization_completion_flat_over_base R K c.pt hC
  let : Algebra R t.B := t.α.hom.toAlgebra
  let : Algebra t.B c.pt := (c.ι.app t).hom.toAlgebra
  have : IsScalarTower R t.B c.pt := IsScalarTower.of_algebraMap_eq' (by
    exact (congrArg CommRingCat.Hom.hom (hρ t)).symm)
  let : Algebra t.B C := ((algebraMap c.pt C).comp (c.ι.app t).hom).toAlgebra
  have : IsScalarTower t.B c.pt C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R t.B C := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R c.pt C]
    change _ = (algebraMap c.pt C).comp ((c.ι.app t).hom.comp t.α.hom)
    rw [← CommRingCat.hom_comp, hρ t]
    rfl)
  have ht : Algebra.Etale R t.B := by
    have := t.etale
    exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp inferInstance
  have : Module.Flat R C := (RingHom.flat_algebraMap_iff).mp hflat
  have : Module.Flat t.B C :=
    Algebra.FormallyUnramified.flat_of_restrictScalars R t.B C
  exact (RingHom.flat_algebraMap_iff).mpr this

end AlgebraicGeometry.Scheme
