/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Homotopy colimit of good truncations

Source: Stacks Project, Cohomology on Sites, Lemmas 06YS and 077J;
Derived Categories, Lemma 0949
(blueprint: lem-pc-kflat-hocolim-truncations).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-kflat-hocolim-truncations) For a complex `K` of modules over a sheaf of
commutative rings on a site, the canonical map from the telescope of its good truncations to
`K` is a quasi-isomorphism. Also, filtered colimits preserve quasi-isomorphisms of such
complexes (Stacks, Tag 06YS).

Proof:
1. Apply `lem-pc-complex-hocolim-colimit` to the good truncations and their canonical
transition maps. Its telescope comparison gives a quasi-isomorphism to the termwise colimit.
2. In degree `i`, the term is zero for `n < i`, the cycles for `n = i`, and the term of
`K` for `n > i`. The transition maps are eventually identities, so this colimit is `K`.
Compose the telescope comparison with this isomorphism. The canonical cone map is zero
on the shifted summand and is the sum of the truncation inclusions on the unshifted summand.
3. As in `prop-pur-kinjective-resolutions-exist`, filtered colimits of sheaves of modules
on a small ringed site are exact. Hence they commute with kernels, images, and cohomology.
The induced map on each cohomology sheaf is the filtered colimit of isomorphisms, so it
is an isomorphism. This uses the meanings of cochain complexes and quasi-isomorphisms
in `def-pc-cochain-complex-modules` and `def-pc-quasi-iso-modules`.
The source uses these comparisons in 077J, invoked in the proof of 06YS. -/
theorem quasiIso_hocolim_truncLE_and_filtered_colimit
    {S : Type u} [Category.{u} S] {J : GrothendieckTopology S}
    (R : Sheaf J CommRingCat.{u})
    (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    (let E : ℕ → CochainComplex
        (SheafOfModules.{u} ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
        fun n => K.truncLE (n : ℤ)
      let A := ∐ E
      ∃ t : ∀ n : ℕ, E n ⟶ E (n + 1),
        (∀ n, t n ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ) = K.ιTruncLE (n : ℤ)) ∧
        ∃ f : mappingCone
            (𝟙 A - Sigma.desc (fun n => t n ≫ Sigma.ι E (n + 1))) ⟶ K,
          mappingCone.inr _ ≫ f =
            Sigma.desc (fun n : ℕ => (K.ιTruncLE (n : ℤ) : E n ⟶ K)) ∧
            (mappingCone.inl _).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0 ∧
            QuasiIso f) ∧
      (∀ (I : Type u) [SmallCategory I] [IsFiltered I]
        (F G : I ⥤ CochainComplex
          (SheafOfModules.{u} ((sheafCompose J
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
        (α : F ⟶ G), (∀ i : I, QuasiIso (α.app i)) →
          QuasiIso (colim.map α)) := by
  sorry

end CochainComplex
