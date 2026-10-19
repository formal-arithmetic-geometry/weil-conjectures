/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.SheavesKilledByNZmodModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Data.PNat.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Algebra.Module.ZMod
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Constructibility of an abelian sheaf with its cyclic coefficient structure

Source: Stacks Project, Etale Cohomology, Definitions 03RU and 03RW(2),(3), with the
blueprint's global finite-partition convention
(blueprint: lem-weil-pbc-constructible-abelian-zn-module-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A constructible abelian sheaf killed by a positive integer is constructible with
its unique constant cyclic-ring module structure. Every originally witnessing finite
partition, including its immersed stratum schemes, still witnesses constructibility.
The positive natural `n` encodes the hypothesis `n ≥ 1`. The equality `hG` identifies
`G` with the module structure on `C` supplied by `sheaves_killed_by_n_zmod_modules`.
The existing constant-scalar restriction functor expresses this same object in the
module-valued encoding used by `IsConstructibleEtaleModuleSheaf`.

Source: Stacks Project, Etale Cohomology, Definitions 03RU and 03RW(2),(3); the
coefficient passage also used in Lemma 09Z7(2),(3).
(blueprint: lem-weil-pbc-constructible-abelian-zn-module-constructible)

Proof:
1. By `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`(2), `C` has a unique structure
   of module over the constant cyclic ring sheaf, namely `G` under `hG`. Clause (1)
   gives annihilation of its sections, and clause (3) makes all additive maps linear.
2. Fix any stratification witnessing `IsConstructibleAbelianSheaf C`. On each stratum
   choose its etale cover and finite constant abelian values. The underlying abelian
   sheaf of module inverse image agrees with abelian inverse image, first along the
   immersion and then along each cover map, by
   `prop-weil-pbc-inverse-image-modules-exact`(1),(2).
3. Discard empty cover members, keeping a cover, including the empty cover of an empty
   stratum. On a nonempty member choose a point and an algebraic closure of its residue
   field (`def-weil-algebraic-closure`, `def-weil-geometric-point`). Its geometric stalk
   is the constant group by `lem-weil-pbc-constant-sheaf-geometric-stalk`. Germs are
   represented by sections (`def-weil-pbc-geometric-stalks`), so they are killed by `n`.
   Therefore the finite constant group is killed by `n` too.
4. Give this group the cyclic module structure of
   `lem-weil-pbc-zmod-module-structure-killed-by-n`(1). Its constant module sheaf has
   the original constant abelian sheaf underneath, by
   `lem-weil-pbc-constant-module-sheaf-underlying` (`constantCommuteCompose`). Both
   directions of each additive trivialization are linear by step 1. Thus the module
   inverse image on every stratum is locally constant with finite module values.
5. Retain the chosen constructible parts, domains and immersions. Step 4 gives exactly
   the module trivializations in `IsConstructibleEtaleModuleSheaf`; localizing at a
   cover member agrees with its etale inverse image. This proves constructibility and
   the assertion for every originally witnessing stratification, without a converse. -/
theorem isConstructibleEtaleModuleSheaf_of_constructible_abelian
    (T : Scheme.{u}) (n : ℕ+)
    (C : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hC : IsConstructibleAbelianSheaf C) (hkill : (n : ℕ) • 𝟙 C = 0)
    (G : ringedSiteModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (ZMod (n : ℕ))))))
    (hG : (SheafOfModules.toSheaf
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (ZMod (n : ℕ)))))).obj G = C) :
    IsConstructibleEtaleModuleSheaf
      ((etaleConstantModuleRestrictionFunctor T (ULift.{u + 1} (ZMod (n : ℕ)))).obj G) ∧
    ∀ S : LocallyClosedStratification T,
      (∀ k : Fin S.n, Topology.IsConstructible (S.stratum k)) →
      (∀ k : Fin S.n, ∃ V : Cover.{u} etalePrecoverage (S.domain k),
        ∀ i : V.I₀, ∃ A : AddCommGrpCat.{u + 1}, Finite A ∧
          Nonempty
            ((Etale.upperStar AddCommGrpCat.{u + 1} (V.f i)).obj
              ((Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion k)).obj C) ≅
              (constantSheaf (V.X i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) →
      ∀ k : Fin S.n,
        ∃ d : LocallyConstantDatum
          ((Etale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (n : ℕ)))) (S.immersion k)).obj
              ((etaleConstantModuleRestrictionFunctor T (ULift.{u + 1} (ZMod (n : ℕ)))).obj G)),
          ∀ i : d.cover.I₀,
            ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (n : ℕ))), Finite M ∧
              Nonempty
                ((((Etale.upperStar
                  (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (n : ℕ)))) (S.immersion k)).obj
                    ((etaleConstantModuleRestrictionFunctor T
                      (ULift.{u + 1} (ZMod (n : ℕ)))).obj G)).over
                        (d.cover.etalePrecoverageToEtale i)) ≅
                  (constantSheaf
                    ((S.domain k).smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
                    (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (n : ℕ))))).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
