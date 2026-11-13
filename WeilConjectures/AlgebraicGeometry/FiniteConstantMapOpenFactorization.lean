/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantMapOpenFactorization

/-! # Extending a stalk factorization of a finite constant map

## References

* Stacks Project, Tag 09BH, Proposition 59.74.1 (3).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A map from a finitely generated constant module sheaf that factors through a
subsheaf at one geometric stalk factors on a Zariski neighbourhood of that point.
(Stacks, Tag 09BH.) -/
theorem exists_open_factorization_of_finite_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (N : ModuleCat.{u + 1} Λ) [Module.Finite Λ N]
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (U : X.Opens) (_hU : x ∈ U)
      (ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
      ψ ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map α := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' Λ N
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let Q := ModuleCat.of Λ (Fin n → Λ)
  let q' : Q ⟶ N := ModuleCat.ofHom q
  have : Epi q' := (ModuleCat.epi_iff_surjective q').mpr hq
  let S := (pointSmallEtale (X.algClosurePoint x)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  obtain ⟨U, hU, β, hβ⟩ := exists_open_factorization_of_finite_free_constant_map
    φ n (C.map q' ≫ α) x (S.map (C.map q') ≫ l) (by
      rw [Category.assoc, hl, S.map_comp])
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι
  have : Epi (C.map q') := by infer_instance
  have : Epi (P.map (C.map q')) := by infer_instance
  have : StrongEpi (P.map (C.map q')) := strongEpi_of_epi _
  let sq : CommSq β (P.map (C.map q')) (P.map φ) (P.map α) :=
    ⟨by simpa only [Functor.map_comp] using hβ⟩
  exact ⟨U, hU, sq.lift, sq.fac_right⟩

end AlgebraicGeometry.Scheme
