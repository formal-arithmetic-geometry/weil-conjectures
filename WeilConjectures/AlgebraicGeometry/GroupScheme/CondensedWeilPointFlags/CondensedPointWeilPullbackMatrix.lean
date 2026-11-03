/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-! # Pullback fixes scalar-normalized point matrices

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-pullback-matrix).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilPointFlags

/-- The canonical finite-free pullback comparison makes every matrix map invariant.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-pullback-matrix).

Proof: the geometric point is affine and has one underlying point, by its canonical
isomorphism to Spec of the algebraic closure. Entries of a pulled-back finite-free map
are restrictions of the original regular-module endomorphisms. The scalar-section
restriction formula evaluates such a restriction by precomposition with the scheme
map. On the one-point space that precomposition does not change its value. The
injectivity of section values identifies every matrix entry, hence the maps. -/
theorem point_pullback_matrix_fixed (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (g : pointSpace D ⟶ pointSpace D) {a b : ℕ}
    (f : free D l a ⟶ free D l b) :
    CondensedRing.upperStarFinFreeMap (Profinite.padicAlgClRingObj l) g f = f := by
  let : IsAffine (pointSpace D) := IsAffine.of_isIso
    (pullback.snd (𝟙 (Spec (.of D.k₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  let : Subsingleton (pointSpace D) :=
    Function.Injective.subsingleton (Scheme.Hom.injective
      (pullback.snd (𝟙 (Spec (.of D.k₀)))
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  apply Mod.finFree_hom_ext
  intro i j
  rw [CondensedRing.ι_upperStarFinFreeMap_π]
  apply CondensedRing.endValue_injective
  intro x
  rw [CondensedRing.endValue_restrictEnd]
  congr 1
  exact Subsingleton.elim _ _

end WeilConjectures.CondensedWeilPointFlags
