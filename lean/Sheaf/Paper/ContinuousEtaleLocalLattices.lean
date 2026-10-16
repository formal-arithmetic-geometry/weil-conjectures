/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.Paper.ContinuousAffineEtaleLattice
import Sheaf.Paper.ContinuousLatticeFiniteCoproduct

/-! # Etale local integral lattices

Source: Bhatt--Scholze, Proposition 6.8.4(6) and Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-etale-local-lattice)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Integral lattices exist on a quasi-compact quasi-separated etale cover.
Source: Bhatt--Scholze, Proposition 6.8.4(6), and the first paragraph of Lemma 6.8.13.
(blueprint: lem-weil-pbc-continuous-etale-local-lattice)

Proof in words. Apply continuousLisse_affine_etale_lattice at every point x of X.
It encodes the rational module explicitly, applies the existing sectionwise
etale-local lattice theorem, transports the specified lattice back, and refines
to an affine neighborhood. The images of these neighborhoods are open because
the maps are etale, and they cover X because each contains its indexing point.
Noetherianity implies compactness, so choose a finite subfamily. Its scheme
coproduct U is affine, hence compact and quasi-separated. The coproduct map to X
is etale since that is Zariski local at the source, and it is surjective by the
finite covering property. Apply continuousLattice_finite_coproduct to construct
the internal integral module on U as a finite biproduct of component extensions
by zero, with its bound pro-etale free cover and rationalization isomorphism.
No compatibility among the component lattices is required. The same argument
includes zero ranks and the empty base. Only a cover and a lattice on it are
asserted; descent and stratification are separate steps. -/
theorem continuousLisse_etale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P)) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X), Etale p ∧ Surjective p ∧
      CompactSpace U ∧ QuasiSeparatedSpace U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) U),
      (∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ s : D.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (D.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) U))
          (((ProEtale.upperStar Ab.{u + 1} (D.f s)).mapMod _).obj M)) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P) := by
  classical
  choose Y p hY hp hcover M hM e using continuousLisse_affine_etale_lattice ℓ E X P hP
  let (x : X) : IsAffine (Y x) := hY x
  let (x : X) : Etale (p x) := hp x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ Set.range (p x))
    (fun x ↦ (p x).isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hcover x⟩)
  let Z : s → Scheme.{u} := fun i ↦ Y i.val
  let q : ∀ i : s, Z i ⟶ X := fun i ↦ p i.val
  let U : Scheme.{u} := ∐ Z
  let f : U ⟶ X := Limits.Sigma.desc q
  have hf : Etale f := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (sigmaOpenCover Z)]
    intro i
    simpa [f] using hp i.val
  have hsurj : Surjective f := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    refine ⟨Limits.Sigma.ι Z ⟨i, hi⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]
    exact hy
  have hU : IsAffine U := by dsimp [U, Z]; infer_instance
  let : IsAffine U := hU
  obtain ⟨N, hN, eN⟩ := continuousLattice_finite_coproduct ℓ E X P Z q
    (fun i ↦ M i.val) (fun i ↦ hM i.val) (fun i ↦ e i.val)
  exact ⟨U, f, hf, hsurj, inferInstance, inferInstance, N, hN, eN⟩

end AlgebraicGeometry.ProEtale.CondensedRing
