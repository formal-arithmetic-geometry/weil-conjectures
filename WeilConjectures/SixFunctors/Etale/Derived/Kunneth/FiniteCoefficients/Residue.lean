/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Residue scalar extension

Let `ρ : Λ ⟶ Λ ⧸ I` be the reduction modulo an ideal (for instance `𝒪_E/ϖⁿ ⟶ 𝒪_E/ϖ`).
Extension of scalars `M ↦ (Λ ⧸ I) ⊗_Λ M` is right exact but not exact; its total left derived
functors, computed on K-flat resolutions, are

- `AlgebraicGeometry.Etale.residueScalarExtension`:
  `D(W_ét, Λ) ⥤ D(W_ét, Λ ⧸ I)`, deriving `M ↦ (Λ ⧸ I)_W ⊗_{Λ_W} M`
  (`CategoryTheory.Sheaf.quotSMulTop`);
- `AlgebraicGeometry.Etale.residueScalarExtensionModule`: `D(Mod_Λ) ⥤ D(Mod_{Λ ⧸ I})`,
  deriving `M ↦ M / I M` (`ModuleCat.quotSMulTop`).

## Implementation details

The only input is that these functors send quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ)

/-- Reduction modulo `I` of étale sheaves of `Λ`-modules sends quasi-isomorphisms between
K-flat complexes to quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_sheafQuotSMulTop (W : Scheme.{u}) :
    (Sheaf.quotSMulTop W.smallEtaleTopology I).PreservesKFlatQuasiIso := by
  let ι := Sheaf.restrictScalars W.smallEtaleTopology (Ideal.Quotient.mk I)
  have : ι.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels _
  refine Functor.PreservesKFlatQuasiIso.mk' _ fun K hK hK' n ↦ ?_
  have h : (((Sheaf.quotSMulTop W.smallEtaleTopology I ⋙ ι).mapHomologicalComplex _).obj
      K).Acyclic :=
    (CochainComplex.acyclic_tensorRight_of_kFlat K hK hK'
      ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ I)))).of_iso
      ((NatIso.mapHomologicalComplex (Sheaf.quotSMulTopCompRestrictScalarsIso I) _).app K).symm
  exact (ShortComplex.exact_map_iff_of_faithful _ ι).1 (h n)

/-- Residue scalar extension of sheaf complexes: for a scheme `W` and the reduction
`ρ : Λ ⟶ Λ ⧸ I`, the functor `- ⊗ᴸ_Λ Λ ⧸ I : D(W_ét, Λ) ⥤ D(W_ét, Λ ⧸ I)`, the total left
derived functor of the sheaf functor `M ↦ (Λ ⧸ I)_W ⊗_{Λ_W} M`. -/
noncomputable def residueScalarExtension (W : Scheme.{u}) :
    DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I))) :=
  L(Sheaf.quotSMulTop W.smallEtaleTopology I)

/-- Reduction modulo `I` of `Λ`-modules sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms. -/
instance preservesKFlatQuasiIso_moduleCatQuotSMulTop :
    (ModuleCat.quotSMulTop.{u + 1} I).PreservesKFlatQuasiIso := by
  let ι := ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk I)
  refine Functor.PreservesKFlatQuasiIso.mk' _ fun K hK hK' n ↦ ?_
  have h : (((ModuleCat.quotSMulTop.{u + 1} I ⋙ ι).mapHomologicalComplex _).obj K).Acyclic :=
    (CochainComplex.acyclic_tensorRight_of_kFlat K hK hK' (ModuleCat.of Λ (Λ ⧸ I))).of_iso
      ((NatIso.mapHomologicalComplex (ModuleCat.quotSMulTopCompRestrictScalarsIso I) _).app
        K).symm
  exact (ShortComplex.exact_map_iff_of_faithful _ ι).1 (h n)

/-- Residue scalar extension of module complexes: the functor
`- ⊗ᴸ_Λ Λ ⧸ I : D(Mod_Λ) ⥤ D(Mod_{Λ ⧸ I})`, the total left derived functor of
`M ↦ Λ ⧸ I ⊗_Λ M = M / I M`. -/
noncomputable def residueScalarExtensionModule :
    DerivedCategory (ModuleCat.{u + 1} Λ) ⥤ DerivedCategory (ModuleCat.{u + 1} (Λ ⧸ I)) :=
  L(ModuleCat.quotSMulTop.{u + 1} I)

end Etale

end AlgebraicGeometry
