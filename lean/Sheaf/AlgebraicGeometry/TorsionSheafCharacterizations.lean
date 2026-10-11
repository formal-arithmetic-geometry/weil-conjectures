/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.Torsion
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Characterizations of torsion abelian étale sheaves

Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement, and
`sec-abelian-varieties/def-weil-pbc-etale-sheaves`
(blueprint: lem-weil-pbc-torsion-sheaf-characterizations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement
(blueprint: lem-weil-pbc-torsion-sheaf-characterizations).

Proof: (1) Exactness of geometric stalks (prop-weil-pbc-geometric-stalks-exact) identifies
stalks of the kernel of multiplication by n with n-torsion in the stalk. Commutation with
colimits (lem-kun-stalks-commute-colimits) identifies the stalk of the canonical colimit map
with inclusion of the union of these subgroups, namely the torsion subgroup.
(2) Conservativity (lemma-weil-pbc-geometric-stalk-conservative, Stacks 03PU) gives the first
condition iff every stalk is torsion. (3) Locally annihilated sections give torsion stalks:
represent a germ on a pointed neighbourhood and lift its geometric point to the covering
(lem-weil-pbc-etale-cover-geometric-point-lift, Stacks 03PR).
(4) Conversely, choose a geometric point over each point of U; its germ is annihilated by a
positive integer. Equality with zero in the filtered stalk is witnessed on a smaller pointed
neighbourhood. These neighbourhoods cover U. The cofiltered-neighbourhood and composition
facts are lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered and
lem-weil-pbc-etale-composition-cancellation. Condition (2) is the recorded local-section
predicate `CategoryTheory.Sheaf.IsTorsion` (a covering sieve on whose arrows the restriction
has finite additive order), condition (3) is `IsAddTorsion` of every geometric stalk. -/
theorem isTorsionAbelianSheaf_characterizations {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (IsTorsionAbelianSheaf F ↔ F.IsTorsion) ∧
    (IsTorsionAbelianSheaf F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
        IsAddTorsion (((pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F)) := by
  sorry

/-- Source: blueprint `sec-abelian-varieties/def-weil-pbc-etale-sheaves`, Q/Z example
(blueprint: lem-weil-pbc-torsion-sheaf-characterizations).

Proof: (5) The constant sheaf has geometric stalk Q/Z by
lem-weil-pbc-constant-sheaf-geometric-stalk, hence is torsion by the characterization above.
(6) The coproduct of positive-integer-indexed copies of T is étale over T, with disjoint open
coprojections (lem-weil-pbc-scheme-coproduct-copies). The sheaf condition gives the canonical
restriction isomorphism onto the product of sections on T: off-diagonal overlaps are empty,
and sections on the empty scheme form the zero group.
(7) For nonempty T, a geometric stalk identifies the composite of the constant-presheaf unit
and the germ map with the identity of Q/Z. Thus the unit is injective. The glued section with
coordinates 1/2^n cannot be killed by any k > 0, since 2^n > k for some n, and k/2^n is then
not an integer. The universe lift only places Q/Z in the sheaf's value universe. -/
theorem constant_ratModIntSheaf_sections_not_torsion (T : Scheme.{u}) :
    IsTorsionAbelianSheaf ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))) ∧
      (Nonempty T →
        ∃ (U : T.Etale) (e : U.left ≅ ∐ (fun _ : ℕ+ ↦ T))
          (j : ∀ n : ℕ+, Scheme.Etale.mk (𝟙 T) ⟶ U),
          U.hom = e.hom ≫ Sigma.desc (fun _ : ℕ+ ↦ 𝟙 T) ∧
          (∀ n : ℕ+, (j n).left = Sigma.ι (fun _ : ℕ+ ↦ T) n ≫ e.inv) ∧
          Function.Bijective (fun s : ((constantSheaf T.smallEtaleTopology
              AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of
                (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.obj (op U) ↦
            fun n : ℕ+ ↦ ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.map
                (j n).op s) ∧
          ∃ x : ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.obj
                (op U),
            (∀ n : ℕ+, ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                (AddCommGrpCat.of (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))))).obj.map
                  (j n).op x =
              (toSheafify T.smallEtaleTopology
                ((Functor.const T.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of
                    (ULift.{u + 1} (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))))).app
                      (op (Scheme.Etale.mk (𝟙 T)))
                        (ULift.up ((1 / (2 : ℚ) ^ (n : ℕ) : ℚ) :
                          ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)))) ∧
            ∀ k : ℕ, 0 < k → k • x ≠ 0) := by
  sorry

end AlgebraicGeometry.Scheme
