/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapComplex
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryModelComparison
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorSymmetryRepresentatives

/-! # The signed native chain swap represents the transported derived braiding

Source: Stacks 06YU and 0FPT, the K-flat symmetry model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

@[instance_reducible]
private def transportedSymmetric
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    (E : C ≌ D) : @SymmetricCategory C _ (Monoidal.transport E.symm) :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported E.symm))

private theorem transported_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    (E : C ≌ D) (X Y : C) :
    letI := Monoidal.transport E.symm
    letI := transportedSymmetric E
    let μ := transportedTensorComparison E
    E.functor.map (β_ X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (β_ (E.functor.obj X) (E.functor.obj Y)).hom := by
  letI := Monoidal.transport E.symm
  letI := transportedSymmetric E
  letI : E.functor.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Monoidal
  letI : E.functor.Braided :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Braided
  change E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X =
    Functor.OplaxMonoidal.δ E.functor X Y ≫
      (β_ (E.functor.obj X) (E.functor.obj Y)).hom
  rw [Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

variable [HasDerivedCategory.{u + 2}
    (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

end AlgebraicGeometry.ProEtaleWeilSheaf
