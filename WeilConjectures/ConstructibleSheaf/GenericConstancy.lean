/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Local
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.Topology.Stratification.Dense

/-!
# Generic constancy of constructible sheaves

A constructible sheaf `F` on a scheme `X` is finite locally constant on a dense open
subscheme
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.exists_dense_open_isFiniteLocallyConstantSheaf`).
The open subscheme is the union `U = ⋃ᵢ interior Xᵢ` of the interiors of the strata of a
witnessing stratification, which is dense by
`Topology.Stratification.dense_iSupInteriorStratum`. That `F|_U` is finite locally constant
is `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.upperStar_iSupInteriorStratum`: the
`interior Xᵢ` form an open cover of `U`, finite local constancy is Zariski local, and on
`interior Xᵢ` the sheaf `F|_U` is the pullback of `F` along an immersion with image inside
`Xᵢ`, hence finite locally constant by the independence of the scheme structure. No
Noetherian hypothesis is needed. (blueprint: `prop:constructible-generic-constancy`)
-/

@[expose] public section

universe u u'

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
  {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- **Generic constancy, explicit form**: if the pullbacks of `F` to the strata of a
stratification `S` of `X` are finite locally constant, then so is the pullback of `F` to the
union `U = ⋃ᵢ interior Xᵢ` of the interiors of the strata.

The `interior Xᵢ` form an open cover of `U`, and for each `i` the two ways of mapping
`interior Xᵢ` into `X` agree:

```
   interior Xᵢ ──homOfLE──→ U
        ╲                   │
         ╲ (interior Xᵢ).ι  │ U.ι
          ╲                 ↓
           ────────────────→ X
```

so `(interior Xᵢ)^* F` is a pullback of `F|_U` by `Etale.upperStarComp`, and it is finite
locally constant since `interior Xᵢ ⊆ Xᵢ`. -/
theorem IsFiniteLocallyConstantSheaf.upperStar_iSupInteriorStratum (S : Stratification X)
    (F : Sheaf X.smallEtaleTopology A)
    (hS : ∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (S.immersion i)).obj F)) :
    IsFiniteLocallyConstantSheaf
      ((Etale.upperStar A (Scheme.Opens.ι S.iSupInteriorStratum)).obj F) := by
  have h (i : Fin S.n) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar A ((Scheme.Opens.iSupOpenCover S.interiorStratum).f i)).obj
        ((Etale.upperStar A (Scheme.Opens.ι S.iSupInteriorStratum)).obj F)) := by
    have := hS i
    have h' : IsFiniteLocallyConstantSheaf
        ((Etale.upperStar A (Scheme.Opens.ι (S.interiorStratum i))).obj F) := by
      refine IsFiniteLocallyConstantSheaf.upperStar_of_range_subset _ (S.immersion i) ?_ F
      rw [Scheme.Opens.range_ι, S.range_immersion]
      exact interior_subset
    exact IsFiniteLocallyConstantSheaf.of_iso
      (F := (Etale.upperStar A (Scheme.Opens.ι (S.interiorStratum i))).obj F)
      (Etale.upperStarCongr A (Scheme.homOfLE_ι X (le_iSup S.interiorStratum i)).symm F ≪≫
        (Etale.upperStarComp A ((Scheme.Opens.iSupOpenCover S.interiorStratum).f i)
          (Scheme.Opens.ι S.iSupInteriorStratum)).app F)
  exact IsFiniteLocallyConstantSheaf.of_openCover
    (Scheme.Opens.iSupOpenCover S.interiorStratum) _

/-- **Generic constancy**: a constructible sheaf is finite locally constant on a dense open
subscheme, the union of the interiors of the strata of a witnessing stratification.
(blueprint: `prop:constructible-generic-constancy`) -/
theorem IsConstructibleSheaf.exists_dense_open_isFiniteLocallyConstantSheaf
    (F : Sheaf X.smallEtaleTopology A) [IsConstructibleSheaf F] :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsFiniteLocallyConstantSheaf ((Etale.upperStar A U.ι).obj F) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification (FA := FA) (CA := CA) (F := F)
  exact ⟨S.iSupInteriorStratum, S.dense_iSupInteriorStratum,
    IsFiniteLocallyConstantSheaf.upperStar_iSupInteriorStratum S F hS⟩

end AlgebraicGeometry.Scheme

end
