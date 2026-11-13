/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionDualizing
import WeilConjectures.AlgebraicGeometry.SmoothDiagonalRegularGenerators
import WeilConjectures.RingTheory.RegularSequenceKoszulRegular
import WeilConjectures.AlgebraicGeometry.SmoothDiagonalIdealConormalRank
import WeilConjectures.AlgebraicGeometry.ConstantRankExteriorDerivedComparison

/-! # The dualizing object of a smooth diagonal in constant rank

## References

* [Stacks Project, Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT)
-/

@[expose] public section

set_option autoImplicit false

universe u wX wP

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem singleton_one_isKoszulRegular (R : Type u) [CommRing R] :
    RingTheory.Sequence.IsKoszulRegular (fun _ : Fin 1 ↦ (1 : R)) := by
  let e : ExteriorAlgebra.koszulComplexTensor R 1 (fun _ ↦ 1) R ≅
      ExteriorAlgebra.koszulComplex R 1 (fun _ ↦ 1) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (TensorProduct.rid R (⋀[R]^n (Fin 1 →₀ R))).toModuleIso)
      (by
        intro i j hij
        have he : i = j + 1 := by simpa using hij.symm
        subst i
        simp only [ExteriorAlgebra.koszulComplexTensor, ExteriorAlgebra.koszulComplex,
          ChainComplex.of_d]
        ext1
        apply TensorProduct.ext
        ext x
        simp)
  have h : RingTheory.Sequence.IsWeaklyRegular R
      (List.ofFn (fun _ : Fin 1 ↦ (1 : R))) := by
    rw [List.ofFn_succ, List.ofFn_zero]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
      (isUnit_one.isSMulRegular _)
  intro n hn
  exact (RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular R _ h n hn).of_iso
    ((HomologicalComplex.homologyFunctor _ _ n).mapIso e.symm)

/-- The diagonal right adjoint takes the structure object to the shifted determinant
of the dual of relative differentials. This does not involve the right adjoint of f. -/
theorem smoothDiagonal_dualizing_determinant
    (X S : Scheme.{u}) [IsNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wP}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace))]
    (hRΔ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (pullback f f)
        ((schemeDerivedDirectImage (pullback.diagonal f)).obj E.obj))
    (c : schemeDerivedQCohCategory (pullback f f) ⥤ schemeDerivedQCohCategory X)
    (adjC : (schemeDerivedQCohProperty (pullback f f)).lift
      ((schemeDerivedQCohProperty X).ι ⋙
        schemeDerivedDirectImage (pullback.diagonal f)) hRΔ ⊣ c)
    (OP : schemeDerivedQCohCategory (pullback f f))
    (hOP : OP.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj
          (SheafOfModules.unit (pullback f f).ringCatSheaf)) :
    Nonempty ((c.obj OP).obj ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorPower
            (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
              (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧) := by
  classical
  let i := pullback.diagonal f
  have : IsNoetherian X := by
    have := LocallyOfFiniteType.isLocallyNoetherian f
    have := QuasiCompact.compactSpace_of_compactSpace f
    exact {}
  have : IsNoetherian (pullback f f) := by
    have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
    have := QuasiCompact.compactSpace_of_compactSpace (pullback.fst f f)
    exact {}
  have hregular : ∀ x : X, ∃ U : (pullback f f).affineOpens, i x ∈ U.1 ∧
      ∃ (n : ℕ) (g : Fin n → Γ(pullback f f, U.1)),
        Ideal.span (Set.range g) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular g := by
    intro x
    obtain ⟨U, hx, hgen⟩ := exists_isRegular_smooth_diagonal_generators d f (i x)
    refine ⟨U, hx, ?_⟩
    rcases hgen with htop | ⟨l, _, hreg, hspan⟩
    · refine ⟨1, fun _ ↦ 1, ?_, singleton_one_isKoszulRegular _⟩
      rw [Scheme.Hom.ker_apply, htop]
      simp
    · refine ⟨l.length, l.get, ?_, ?_⟩
      · rw [Scheme.Hom.ker_apply, ← hspan]
        ext a
        simp
      · apply RingTheory.Sequence.IsRegular.isKoszulRegular
        simpa only [List.ofFn_get] using hreg
  obtain ⟨⟨eΩ⟩, hrank⟩ := smoothDiagonal_idealConormal_iso_and_rank f d
  let O : schemeDerivedCategory (pullback f f) :=
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) 0).obj
        (SheafOfModules.unit (pullback f f).ringCatSheaf)
  have hO : schemeDerivedQCohProperty (pullback f f) O := by
    intro n
    exact (SheafOfModules.isQuasicoherent (pullback f f).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso hOP) (OP.property n)
  let OQ : schemeDerivedQCohCategory (pullback f f) := ⟨O, hO⟩
  let eOP : OP ≅ OQ := (schemeDerivedQCohProperty (pullback f f)).isoMk hOP
  have hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty (pullback f f) ((schemeDerivedDirectImage i).obj E) := by
    intro E hE
    exact hRΔ ⟨E, hE⟩
  obtain ⟨hdet, ⟨eK⟩⟩ := koszulRegularImmersion_dualizing i hregular
    (LocallyConstant.const X d) (fun x ↦ (hrank x).symm) hpres c adjC OQ rfl
  let eDual : SheafOfModules.homObj (R := X.sheaf)
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
      (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
        (SheafOfModules.unit X.ringCatSheaf) :=
    ((SheafOfModules.homFunctor X.sheaf).mapIso eΩ.symm.op).app
      (SheafOfModules.unit X.ringCatSheaf)
  obtain ⟨eExt⟩ := Scheme.Modules.constantRankExterior_derived_iso _ _ d eDual
  exact ⟨(schemeDerivedQCohProperty X).ι.mapIso (c.mapIso eOP) ≪≫
    ((schemeDerivedQCohProperty X).ι.mapIso eK).symm ≪≫ eExt⟩

end AlgebraicGeometry
