/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Blueprint statements

def-weil-pbc-constructible-complexes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Required definitions for def-weil-pbc-constructible-complexes. -/
def IsConstructibleEtaleModuleSheaf {T : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ S : LocallyClosedStratification T,
    (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) ∧
    ∀ k : Fin S.n,
      let G := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F
      ∃ d : LocallyConstantDatum G, ∀ i : d.cover.I₀,
        ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((G.over (d.cover.etalePrecoverageToEtale i)) ≅
            (constantSheaf
              ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} Λ)).obj M)

end AlgebraicGeometry.Scheme
