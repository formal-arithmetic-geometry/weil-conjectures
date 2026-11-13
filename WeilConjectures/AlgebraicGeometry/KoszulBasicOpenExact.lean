/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.RingTheory.KoszulGeneratorHomotopy
import WeilConjectures.AlgebraicGeometry.BasicOpenTildeScalarIso
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! # Local exactness of the sheafified Koszul complex

## References

* Stacks Project, More on Algebra, Tag 0663.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- The sheafified Koszul complex is exact on each generator's basic open.
(Stacks, More on Algebra, Tag 0663.) -/
theorem koszul_basicOpen_exact
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (i : Fin r) (n : ℤ) :
    (((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)
      (PrimeSpectrum.basicOpen (f i))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend
          ComplexShape.embeddingDownNat))).ExactAt n := by
  let K := ExteriorAlgebra.koszulComplex A r f
  let e := ComplexShape.embeddingDownNat
  let T : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  have : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let R := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) (PrimeSpectrum.basicOpen (f i))
  let L := (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend e))
  let s : K.extend e ⟶ K.extend e := (f i) • 𝟙 (K.extend e)
  have hs : HomologicalComplex.extendMap ((f i) • 𝟙 K) e = s := by
    apply HomologicalComplex.hom_ext
    intro j
    by_cases hj : ∃ q, e.f q = j
    · obtain ⟨q, hq⟩ := hj
      simp [HomologicalComplex.extendMap_f _ e hq, s,
        Linear.comp_smul, Linear.smul_comp]
    · exact (K.isZero_extend_X e j (fun q hq ↦ hj ⟨q, hq⟩)).eq_of_src _ _
  obtain ⟨h⟩ := ExteriorAlgebra.koszul_generator_homotopy A r f i
  change Homotopy ((f i) • 𝟙 K) 0 at h
  have h' : Homotopy s 0 := by
    simpa only [hs, HomologicalComplex.extendMap_zero] using h.extend e
  have h'' := R.mapHomotopy (T.mapHomotopy h')
  let t : L ⟶ L := (R.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map s)
  have ht : IsIso t := basicOpen_tilde_scalar_isIso A (f i) (K.extend e)
  have hz : HomologicalComplex.homologyMap t n = 0 := by
    simpa only [Functor.map_zero, HomologicalComplex.homologyMap_zero] using
      h''.homologyMap_eq n
  have : IsIso (0 : L.homology n ⟶ L.homology n) := by
    rw [← hz]
    infer_instance
  change L.ExactAt n
  exact (L.exactAt_iff_isZero_homology n).mpr
    ((isIsoZero_iff_source_target_isZero (L.homology n) (L.homology n)).mp
      inferInstance).1

end AlgebraicGeometry
