/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelScalar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix
public import WeilConjectures.TraceFormula.UnitBasis

/-!
# Categorical traces at a separably closed point in the two models

Let `Ω` be a separably closed field and `N` a finite free `ℓ`-adic sheaf on `Spec Ω`, that is
`N ≅ ℚ̄_ℓʳ`. For an endomorphism `ψ` of `N`, the categorical trace of its image `E ψ` under the
equivalence `E : AdicSheaf ℓ (Spec Ω) ≌ Mod_{ℚ̲̄_ℓ,Spec Ω}`
(`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`), read in `ℚ̄_ℓ` through
`End (𝟙_ Mod_{Spec Ω}) ≅ ℚ̄_ℓ`, is the trace of the linear map induced by `ψ` on the global
sections `Γ(Spec Ω, N)`
(`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_traceOrZero_map_of_iso_biproduct`).

Both are the sum of the diagonal entries of the matrix of `ψ`, an endomorphism of `ℚ̄_ℓ` on
`Spec Ω` being the multiplication by a scalar
(`AlgebraicGeometry.ProEtale.AdicSheaf.exists_eq_smul_unit`), and `E` being `ℚ̄_ℓ`-linear on the
unit (`AlgebraicGeometry.ProEtale.endTensorUnitRingEquiv_adicSheafEquivCondensedMod_map_smul`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace LinearMap

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
  {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, FiniteDimensional R (N i)]

end LinearMap

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

variable (l) in
/-- The unit basis of the image of `ℚ̄_ℓʳ` in `Mod_{ℚ̲̄_ℓ,X}`: the images of the inclusions and
projections of the summands, through `E ℚ̄_ℓ,X ≅ ℚ̲̄_ℓ,X`. -/
noncomputable def adicSheafEquivCondensedModUnitBasis (X : Scheme.{u}) (r : ℕ) :
    UnitBasis ((adicSheafEquivCondensedMod l X).functor.obj
      (⨁ fun _ : Fin r ↦ AdicSheaf.unit l X)) (Fin r) where
  incl i := (adicSheafEquivCondensedModUnitIso l X).inv ≫
    (adicSheafEquivCondensedMod l X).functor.map
      (biproduct.ι (fun _ : Fin r ↦ AdicSheaf.unit l X) i)
  proj i := (adicSheafEquivCondensedMod l X).functor.map
      (biproduct.π (fun _ : Fin r ↦ AdicSheaf.unit l X) i) ≫
    (adicSheafEquivCondensedModUnitIso l X).hom
  incl_proj i j := by
    rw [Category.assoc, ← Functor.map_comp_assoc]
    split_ifs with h
    · subst h
      rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
    · rw [biproduct.ι_π_ne _ h, Functor.map_zero, zero_comp, comp_zero]
  total := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_sum,
      biproduct.total, CategoryTheory.Functor.map_id]

variable (l) in
/-- The global sections of an `ℓ`-adic sheaf, as a `ℚ̄_ℓ`-vector space. -/
noncomputable abbrev adicGlobalSectionsModule (X : Scheme.{u}) :
    AdicSheaf l X ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  AdicSheaf.forget X ⋙ Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l

instance (X : Scheme.{u}) : (adicGlobalSectionsModule l X).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  dsimp only [adicGlobalSectionsModule]
  infer_instance

/-- On global sections, the multiplication by a scalar `c` is the multiplication by `c`. -/
lemma adicGlobalSections_map_smul (X : Scheme.{u}) (c : PadicAlgCl l) (M : AdicSheaf l X) :
    ((adicGlobalSectionsModule l X).map (AdicSheaf.smul (ULift.up c) M)).hom = c • LinearMap.id :=
  LinearMap.ext fun x ↦ Sheaf.Γ_map_smulEnd (Scheme.ProEt.isTerminalMkId X) M.X (ULift.up c) x

end AlgebraicGeometry.ProEtale
