/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Geometry of affine etale pullbacks over a field

Source: Stacks Project, Morphisms, Tags 01T3, 01T4, 01T8; Descent, Tag 04N4,
first-inequality specialization-chain argument
(blueprint: lem-sf-affine-etale-pullback-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine etale test scheme over a separated finite-type field scheme pulls back to
a finite-type field scheme, etale over the source, with no increase in dimension.
Source: Stacks Project, Tags 01T3, 01T4, 01T8, and the first inequality in Tag 04N4
(blueprint: lem-sf-affine-etale-pullback-dimension).

Proof:
1. The spectrum of the field is locally Noetherian (`pqf-def-locnoeth`,
   `def-weil-pbc-noetherian-ring`); finite type makes T locally Noetherian and hence
   quasi-separated (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-weil-pbc-locally-noetherian-quasi-separated`).
2. W is affine, so its space is compact and w is quasi-compact
   (`lem-weil-pbc-qcqs-morphism-permanence`, affine-source clause).
3. Etale morphisms are locally of finite type and stable under base change; composition
   with aS makes the pullback quasi-compact and locally of finite type over k
   (`def-weil-etale-morphism`, `def-weil-finite-type-morphism`,
   `lem-weil-pbc-etale-scheme-base-change`, `lem-sfb-finite-type-composition-base-change`).
4. The etale second projection is locally quasi-finite, so its fibres have no proper
   specialization and strict chains of irreducible closed subsets map to strict chains:
   `Scheme.Hom.topologicalKrullDim_le_of_etale` gives dim V <= dim S
   (`def-kun-topological-krull-dimension`), and hd gives dim S <= d. Empty schemes have
   dimension bottom and are included; no quasi-compactness is assumed for arbitrary
   objects of the small etale site. -/
theorem affine_etale_pullback_dimension
    {k : Type u} [Field k] {S T : Scheme.{u}}
    (aS : S ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (f : S ⟶ T) (hf : f ≫ aT = aS) (d : ℕ)
    (hd : topologicalKrullDim S ≤ (d : WithBot ℕ∞))
    {W : Scheme.{u}} [IsAffine W] (w : W ⟶ T) [Etale w] :
    (LocallyOfFiniteType (pullback.snd w f ≫ aS) ∧
      QuasiCompact (pullback.snd w f ≫ aS)) ∧
    Etale (pullback.snd w f) ∧
    topologicalKrullDim (pullback w f : Scheme.{u}) ≤ topologicalKrullDim S ∧
    topologicalKrullDim S ≤ (d : WithBot ℕ∞) := by
  have _ := hf
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian aT
  have : QuasiSeparatedSpace T := inferInstance
  have : QuasiCompact w := quasiCompact_of_compactSpace w
  have hq : QuasiCompact (pullback.snd w f ≫ aS) := by infer_instance
  have hlf : LocallyOfFiniteType (pullback.snd w f ≫ aS) := by infer_instance
  have he : Etale (pullback.snd w f) := by infer_instance
  have hdim : topologicalKrullDim (pullback w f : Scheme.{u}) ≤ topologicalKrullDim S :=
    (pullback.snd w f).topologicalKrullDim_le_of_etale
  exact ⟨⟨hlf, hq⟩, he, hdim, hd⟩

end AlgebraicGeometry
