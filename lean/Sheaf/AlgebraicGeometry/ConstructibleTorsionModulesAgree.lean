/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.CurveCoefficientPair
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.AlgebraicGeometry.LocallyClosedStratification
import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
import Sheaf.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.Paper.SheavesKilledByNZmodModules
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Constructibility of torsion abelian sheaves and of cyclic-coefficient module sheaves

Source: Stacks Project, Tags 03RW(2),(3), 095E and 03RU; the comparison is agent-formulated
(blueprint: lem-weil-pbc-constructible-torsion-modules-agree).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An abelian sheaf killed by a positive integer is torsion and has a unique cyclic-ring
module structure. Constructibility of the curve coefficient pair (the recorded
`CurveCoefficientPair.IsConstructible`) agrees with constructibility of the module sheaf (the
recorded `IsConstructibleEtaleModuleSheaf`). On every fixed stratification (finite partition
into constructible locally closed parts with scheme immersions) the three stratum conditions
agree: finite local constancy of the set-sheaf pullback of the underlying sheaf of sets,
abelian local constancy of the abelian inverse image with finite geometric stalks, and
module local constancy with finite constant values. So the same partitions and immersions
serve for both notions. Uniqueness of the module structure is stated in the fiber of the
forgetful functor: any other module lift of `F` has exactly one module isomorphism compatible
with the given identifications with `F`.

Proof, following the node:
1. Sections killed by `n` are torsion (lem-weil-pbc-torsion-sheaf-characterizations).
   The unique cyclic-ring module action makes every additive restriction map linear
   (lem-weil-pbc-sheaves-killed-by-n-zmod-modules), giving the unique module lift.
   Together with the curve hypotheses this gives a curve coefficient pair.
2. Both definitions use the same constructible locally closed partitions and immersions
   (def-constructible-stratification, def-weil-constructible-subset).
3. Inverse image commutes with forgetting the module structure and stays killed by `n`
   (prop-weil-pbc-inverse-image-modules-exact); etale restriction is sectionwise.
4. On a nonempty trivializing etale scheme, a constant abelian value is its geometric
   stalk (lem-weil-pbc-constant-sheaf-geometric-stalk). Thus it is killed by `n` and has
   its unique cyclic-ring module action. Constant module sheaves have the corresponding
   constant abelian sheaves underneath (lem-weil-pbc-constant-module-sheaf-underlying).
   Every abelian isomorphism is then linear by step 1.
5. From abelian local constancy with finite stalks, discard empty cover members. Step 4
   upgrades every remaining finite abelian value to a finite cyclic-ring module value.
6. Conversely, forget a module trivialization. Each geometric point lifts through the
   etale cover (lem-weil-pbc-etale-cover-geometric-point-lift); its stalk is a finite
   constant value. This gives abelian local constancy with finite geometric stalks.
Source: Stacks Project, Tags 03RW(2),(3), 095E and 03RU; agent-formulated comparison
(blueprint: lem-weil-pbc-constructible-torsion-modules-agree). -/
theorem constructible_torsion_modules_agree
    {k : Type v} [Field k] [IsAlgClosed k] {C : Scheme.{v}}
    (f : C ⟶ Spec (.of k)) [IsCurve f]
    (n : ℕ) (hn : 0 < n) (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{v + 1})
    (hF : n • 𝟙 F = 0) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let R := ULift.{v + 1} (ZMod n)
    let U := sheafCompose C.smallEtaleTopology
      (forget₂ (ModuleCat.{v + 1} R) AddCommGrpCat.{v + 1})
    ∃ hT : C.IsTorsionAbelianSheaf F,
      let P : CurveCoefficientPair k := ⟨C, f, inferInstance, F, hT⟩
      ∃ (M : Sheaf C.smallEtaleTopology (ModuleCat.{v + 1} R)) (e : U.obj M ≅ F),
        (∀ (N : Sheaf C.smallEtaleTopology (ModuleCat.{v + 1} R)) (eN : U.obj N ≅ F),
          ∃! a : M ≅ N, U.mapIso a ≪≫ eN = e) ∧
        (P.IsConstructible ↔ IsConstructibleEtaleModuleSheaf M) ∧
        ∀ S : Stratification C,
          ((∀ i : Fin S.n,
              IsFiniteLocallyConstantEtaleSheafOfSets
                ((etaleSetPullback (S.immersion i)).obj
                  ((sheafCompose C.smallEtaleTopology
                    (CategoryTheory.forget AddCommGrpCat.{v + 1})).obj F))) ↔
            ∀ i : Fin S.n,
              let G := (Etale.upperStar AddCommGrpCat.{v + 1} (S.immersion i)).obj F
              IsLocallyConstantSheaf G ∧
                ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
                    (s : Spec (.of Ω) ⟶ S.domain i),
                  Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) ∧
          ((∀ i : Fin S.n,
              let G := (Etale.upperStar AddCommGrpCat.{v + 1} (S.immersion i)).obj F
              IsLocallyConstantSheaf G ∧
                ∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω]
                    (s : Spec (.of Ω) ⟶ S.domain i),
                  Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{v + 1})).obj G)) ↔
            ∀ i : Fin S.n,
              let G := (Etale.upperStar (ModuleCat.{v + 1} R) (S.immersion i)).obj M
              ∃ d : LocallyConstantDatum G, ∀ j : d.cover.I₀,
                ∃ A : ModuleCat.{v + 1} R, Finite A ∧
                  Nonempty ((G.over (d.cover.etalePrecoverageToEtale j)) ≅
                    (constantSheaf
                      ((S.domain i).smallEtaleTopology.over
                        (d.cover.etalePrecoverageToEtale j))
                      (ModuleCat.{v + 1} R)).obj A)) := by
  sorry

end AlgebraicGeometry.Scheme
