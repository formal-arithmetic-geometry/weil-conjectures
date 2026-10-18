/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion
import Sheaf.AlgebraicGeometry.NormalizationGeonormalInsep

/-!
# Projective and geometrically normal core of the curve completion

Source: Stacks Project, Varieties, Tags 0BXV and 0BXT.
(blueprint: lem-weil-pbc-field-curve-completion-core)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A separated finite type scheme of dimension at most one admits a projective completion whose
normalization becomes geometrically normal after a finite purely inseparable extension.
Source: Stacks Project, Varieties, Tags 0BXV and 0BXT.
(blueprint: lem-weil-pbc-field-curve-completion-core)

Proof: apply `exists_projective_dense_completion_of_dim_le_one` to obtain `T`, its projective
structure morphism and dense open immersion from `X`. Apply
`exists_finite_purelyInseparable_geometricallyNormal_normalization` to `T`; its hypotheses
follow from projectivity, which supplies finite type and quasi-compactness over the field.
The resulting extension and component family are returned unchanged. This theorem deliberately
stops before the constant-field refinements and restriction to `X`, which are separate steps
of Tag 0GK5.
-/
theorem exists_projective_geonormal_core
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (T : Scheme.{u}) (g : T ⟶ Spec (.of k)) (a : X ⟶ T),
      IsHProjective g ∧ topologicalKrullDim T ≤ 1 ∧ IsOpenImmersion a ∧
      a ≫ g = X ↘ Spec (.of k) ∧ DenseRange a ∧
      ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
        Module.Finite k K ∧ IsPurelyInseparable k K ∧
        ∃ (n : ℕ) (C : Fin n → Scheme.{u}) (hC : ∀ i, IsIntegral (C i))
          (c : ∀ i, C i ⟶ pullback g
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
          (∀ i, IsClosedImmersion (c i)) ∧
          Function.Injective (fun i ↦ Set.range (c i)) ∧
          (∀ Z : Set (pullback g
              (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
            Z ∈ irreducibleComponents
                (pullback g (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) ↔
              ∃ i, Set.range (c i) = Z) ∧
          ∀ (L : Type u) [Field L] [Algebra K L],
            ∀ z : ↥(pullback
              (Sigma.desc (fun i ↦ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ≫
                pullback.snd g
                  (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
              IsDomain ((pullback
                (Sigma.desc (fun i ↦ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ≫
                  pullback.snd g
                    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
                (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk z) ∧
              IsIntegrallyClosed ((pullback
                (Sigma.desc (fun i ↦ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ≫
                  pullback.snd g
                    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
                (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.stalk z) := by
  obtain ⟨T, g, a, hg, hd, ha, hag, hda, _⟩ :=
    exists_projective_dense_completion_of_dim_le_one (k := k) (X := X) hdim
  have : IsHProjective g := hg
  let : T.Over (Spec (.of k)) := ⟨g⟩
  have : IsProper g := IsHProjective.isProper g
  have : LocallyOfFiniteType (T ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType g)
  have : QuasiCompact (T ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact g)
  obtain ⟨K, hK, hAlgebra, hfinite, hinsep, n, C, hC, c, hc, hi, hcover, hn⟩ :=
    exists_finite_purelyInseparable_geometricallyNormal_normalization k T
  exact ⟨T, g, a, hg, hd, ha, hag, hda, K, hK, hAlgebra, hfinite, hinsep,
    n, C, hC, c, hc, hi, hcover, hn⟩

end AlgebraicGeometry
