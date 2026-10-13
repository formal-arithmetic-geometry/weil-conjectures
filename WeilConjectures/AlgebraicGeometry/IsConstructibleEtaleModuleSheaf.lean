/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification

/-!
# Constructible etale sheaves of modules with finite constant values

Source: Stacks Project, Tags 095E(3), 03RU and 09XZ, and the blueprint's global
constructibility clause (blueprint: def-weil-pbc-etale-constructible-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A sheaf of modules over a finite commutative ring is constructible if a finite
locally closed stratification has constructible parts and each stratum pullback admits
an etale trivialization with finite constant module values. Sheaves with values in
`ModuleCat Λ` encode sheaves of modules over the constant ring sheaf `Λ_T`.

Construction, following the node:
1. Choose a finite locally closed partition with scheme immersions realizing its parts
   (`def-constructible-stratification`), and require each part to be constructible
   (`def-weil-constructible-subset`).
2. Pull back the module sheaf to each stratum using `Etale.upperStar`
   (`def-weil-pbc-inverse-image`, `def-weil-pbc-etale-sheaves`, `def-weil-pbc-etale-site`).
3. Choose a trivializing etale cover (`def-constructible-locally-constant`) and require
   module-sheaf isomorphisms to constant sheaves with finite module values on its members.
   Agreement with the geometric-stalk formulation is a separate lemma, not a condition here.
Source: Stacks Project, Tags 095E(3), 03RU and the global blueprint clause
(blueprint: def-weil-pbc-etale-constructible-sheaf). -/
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
