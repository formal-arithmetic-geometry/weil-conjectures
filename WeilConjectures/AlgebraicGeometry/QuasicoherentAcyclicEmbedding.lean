/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Over
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.AffineCoverModuleEmbedding
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-!
# Embedding a quasi-coherent module into an acyclic quasi-coherent module

## References

* [Stacks Project, Tag 0BDY](https://stacks.math.columbia.edu/tag/0BDY)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a quasi-compact scheme over a field with affine diagonal, every quasi-coherent
module embeds into a quasi-coherent module with vanishing cohomology in positive degrees. -/
theorem exists_quasicoherent_acyclic_embedding (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [F.IsQuasicoherent] :
    ∃ F' : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      F'.IsQuasicoherent ∧ ∃ i : F ⟶ F', Mono i ∧
        ∀ p : ℕ, 1 ≤ p → IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F') := by
  obtain ⟨U, j, G, hU, hj, hG, i, hi⟩ := exists_affine_cover_module_embedding k X F
  have : IsAffine U := hU
  have : IsAffineHom j := hj
  have : G.IsQuasicoherent := hG
  refine ⟨(Modules.pushforward j).obj G,
    Modules.isQuasicoherent_pushforward_of_isAffineHom j G, i, hi, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have : Subsingleton (Modules.H G (q + 1)) :=
    Modules.subsingleton_H_succ_of_isAffine G q
  obtain ⟨e, _⟩ := Modules.exists_moduleCohomology_source_comparison U (q + 1)
  have : Subsingleton ((RingedSpace.moduleCohomology U.toRingedSpace (q + 1)).obj G) :=
    (e G).toEquiv.injective.subsingleton
  have : IsIso (Modules.moduleCohomologyEdgeMap j G (q + 1)) :=
    ((Modules.affine_morphism_cohomology_edge j G).2 (q + 1)).1
  have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj
      ((Modules.pushforward j).obj G)) :=
    (ConcreteCategory.bijective_of_isIso
      (Modules.moduleCohomologyEdgeMap j G (q + 1))).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme
