/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.EtaleSheaves

/-!
# Abelian sheaves killed by n are sheaves of Z/n-modules

Source: literature/stacks-project/etale-cohomology.tex, Definition 03RW and
Theorem 03SC (blueprint: lem-weil-pbc-sheaves-killed-by-n-zmod-modules).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The identification of sheaves of `(Z/n)_T`-modules with abelian sheaves killed by `n`.
Source: Stacks, etale-cohomology.tex, Definition 03RW (2), (3), and the proof of
Theorem 03SC; sites-modules.tex, definition-sheaf-modules
(blueprint: lem-weil-pbc-sheaves-killed-by-n-zmod-modules).
This identification is used implicitly by Stacks; its proof is the node's agent-written proof.

1. A module sheaf is an abelian sheaf with sectionwise module actions compatible with
restriction (def-weil-sheaf-of-modules-category). Its action is a morphism of presheaves of
sets. Underlying sets of abelian and ring sheaves are sheaves; their finite products are
sheaves (lem-weil-pbc-presheaf-finite-limits-objectwise).
2. Write `P` for the constant ring presheaf and `η : P → 𝒪` for sheafification. Underlying
sets preserve this sheafification (lem-weil-pbc-ring-sheafification-underlying-sets).
Sheafification preserves finite products (lem-weil-pbc-sheafification-sets-exact), so
`η^m × id` on any finite product with sheaves of sets is a sheafification. Maps from that
product into a sheaf extend uniquely from constants (def-weil-pbc-sheafification).
3. The ring map `η_U` sends the residue of an integer `a` to `a • 1`; hence its action in
any module sheaf is `a • s` (lem-weil-pbc-zmod-module-structure-killed-by-n).
4. Apply step 3 with `a = n`: the residue is zero, so every section is killed by `n`.
5. Conversely, on an `n`-killed abelian sheaf the constant action `ā • s = a • s` is
well defined and commutes with restriction (lem-weil-pbc-zmod-module-structure-killed-by-n).
Extend it uniquely by step 2. Check the unit, the two distributive laws, and associativity
on constants using step 2 and the integer action; this gives the required module sheaf.
6. Any other action agrees on constants by step 3, hence everywhere by step 2, proving
uniqueness while keeping the underlying abelian sheaf fixed.
7. For an additive sheaf map compare `φ(r • s)` and `r • φ(s)`. They agree on constants
because additive maps commute with integer multiplication, and thus everywhere by step 2.
This makes every abelian sheaf map linear (lem-weil-pbc-zmod-module-structure-killed-by-n).
8. Forgetting is faithful since module morphisms are additive morphisms with a property;
step 7 makes it full. Steps 4 and 5 characterize its image, and annihilation is invariant
under isomorphism, characterizing the essential image. Both an abelian isomorphism and
its inverse are linear by step 7, so it lifts to a module-sheaf isomorphism.
-/
theorem sheaves_killed_by_n_zmod_modules
    (T : Scheme.{u}) (n : ℕ) (hn : 1 ≤ n) :
    (∀ (G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (ZMod n))))) (U : T.Etaleᵒᵖ)
        (s : G.val.obj U), n • s = 0) ∧
      (∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (∀ (U : T.Etaleᵒᵖ) (s : F.1.obj U), n • s = 0) →
          ∃! G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n)))), (SheafOfModules.toSheaf ((constantSheaf
              T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of (ULift.{u + 1} (ZMod n))))).obj
              G = F) ∧
      (∀ (G : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n))))) (U : T.Etaleᵒᵖ)
        (a : ℤ) (s : G.val.obj U),
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod n))))).app U)
            (ULift.up (a : ZMod n)) • s = a • s) ∧
      (∀ (G G' : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n))))),
        Function.Bijective
          ((SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).map : (G ⟶ G') →
            ((SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
                (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G ⟶
              (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
                  (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G'))) ∧
      (∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
            (RingCat.of (ULift.{u + 1} (ZMod n))))).essImage F ↔
          ∀ (U : T.Etaleᵒᵖ) (s : F.1.obj U), n • s = 0) ∧
      (∀ (G G' : SheafOfModules.{u + 1} ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
          (RingCat.of (ULift.{u + 1} (ZMod n)))))
        (i : (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
            (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G ≅
          (SheafOfModules.toSheaf ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).obj G'),
        ∃ j : G ≅ G',
          (SheafOfModules.toSheaf
            ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1} (ZMod n))))).mapIso j = i) := by
  sorry

end AlgebraicGeometry
