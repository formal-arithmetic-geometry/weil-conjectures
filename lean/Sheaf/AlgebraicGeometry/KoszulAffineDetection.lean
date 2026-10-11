/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Paper.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Koszul powers detect supported objects on an affine scheme

Source: Stacks Project, Derived Categories of Schemes, Tag 09IR, proof via
Lemma 36.9.6 and Tag 06Z0 (blueprint: lem-pc-koszul-affine-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Koszul powers detect an object of `D_QCoh` supported on the common zero locus.
The Koszul complexes are sheafified termwise and placed in nonpositive cochain degrees;
they are the bounded finite-free, hence perfect, complexes of Stacks Tag 09IR.
Source: Stacks Project, Tag 09IR (blueprint: lem-pc-koszul-affine-detection).

Proof:
1. Use the diagonal exponent tuple `(e, ..., e)`. The triangles of
   `lem-sc-affine-perfect-open-represent-cohomology` identify `H^n(X,E)` with
   `Hom(I_e,E[n])`: the outer Koszul Hom groups in the exact sequence vanish.
   These identifications commute with the transition maps because the maps
   `I_e → O_X` are compatible.
2. Pass to the filtered colimit. The represent-cohomology lemma identifies this
   colimit with `H^n(U,E|_U)`, which is zero by the restriction hypothesis.
   Thus `H^n(X,E)` is zero for every integer `n`.
3. The affine quasi-coherent derived equivalence
   `lem-pc-affine-qcoh-derived-equivalence` identifies `E` with the complex
   `RΓ(X,E)` of modules. All its cohomology modules vanish, so it and `E` are zero. -/
theorem isZero_of_koszul_powers_orthogonal
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A)))
    (hres : IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj E.obj))
    (horth : ∀ (e : Fin r → ℕ), (∀ i, 0 < e i) → ∀ n : ℤ,
      Subsingleton
        (((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)).extend
              ComplexShape.embeddingDownNat)))⟦n⟧) ⟶ E.obj)) :
    IsZero E.obj := by
  sorry

end AlgebraicGeometry
