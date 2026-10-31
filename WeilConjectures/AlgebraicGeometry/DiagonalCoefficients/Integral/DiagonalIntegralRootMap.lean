/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams

/-! # The projection-normalized integral root map

Source: coefficient changes, initial root-limit comparison.
(blueprint: lem-diagonal-integral-root-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem freeUnit_tensorMap
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S] (a : R ⟶ S) [IsMonHom a]
    {M N : C} (f : M ⟶ N) :
    (Mod.freeForgetAdjunction R).unit.app M ≫ (a ⊗ₘ f) =
      f ≫ (Mod.freeForgetAdjunction S).unit.app N := by
  change ((λ_ M).inv ≫ η[R] ▷ M ≫ 𝟙 _) ≫ (a ⊗ₘ f) =
    f ≫ (λ_ N).inv ≫ η[S] ▷ N ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, IsMonHom.one_hom,
    ← MonoidalCategory.whisker_exchange]
  rw [← Category.assoc, ← MonoidalCategory.leftUnitor_inv_naturality]
  rw [Category.assoc]

/-- The root-to-integral-line map exists and is uniquely fixed by every finite
projection. No local choice of a root generator is made.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), normalized root
limits. (blueprint: lem-diagonal-integral-root-map).

Proof: At level n, compose the n-th root-limit projection with the free-module
unit. The next-level root projection reduces by the prescribed root power map.
The free-module unit commutes with the tensor of this root power map and the
unital coefficient reduction, so these maps form a cone. Forgetting the fixed
integral scalar action preserves limits. Its limiting cone therefore gives the
map into the underlying integral line and every required projection equation.
The same limiting cone proves uniqueness. -/
theorem diagonalIntegralRoots_exists (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) :
    Nonempty (IntegralRoots l E X) := by
  let T := spIntegralTwistSystem X l E
  let U := Mod.forget
    (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X)
  let c : Cone (T ⋙ U) :=
    { pt := Scheme.purTwistZlOne X l
      π := NatTrans.ofOpSequence
        (fun n ↦ limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime))
          (op n) ≫
            (Mod.freeForgetAdjunction (condensedRingObj (spEllPointRingObj l E n) X)).unit.app
              (Scheme.proEtaleRootsOfUnitySheaf X (l ^ (n + 1)))) (by
          intro n
          dsimp only [Functor.const_obj_map]
          erw [Category.id_comp]
          dsimp only [T, U, Functor.comp_map, spIntegralTwistSystem]
          rw [Functor.ofOpSequence_map_homOfLE_succ]
          have ht := (spIntegralLevelTransition_existsUnique X l E n).exists.choose_spec
          change (spIntegralLevelTransition X l E n).hom = _ at ht
          change _ = _ ≫ (spIntegralLevelTransition X l E n).hom
          rw [ht]
          rw [Category.assoc, freeUnit_tensorMap]
          rw [← Category.assoc]
          congr 1
          simpa only [Scheme.proEtaleRootsOfUnityTower,
            Functor.ofOpSequence_map_homOfLE_succ] using
              (limit.w (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime))
                (homOfLE (Nat.le_succ n)).op).symm) }
  let h := isLimitOfPreserves U (limit.isLimit T)
  refine ⟨⟨h.lift c, fun n ↦ ?_⟩⟩
  exact h.fac c (op n)

/-- The finite projections determine the integral root comparison uniquely.

Source: blueprint coefficient changes, normalized root limits.
(blueprint: lem-diagonal-integral-root-map).

Proof: forgetting scalars preserves the inverse limit. Its projections jointly
cancel the two maps, and the prescribed projection formulas agree. -/
theorem diagonalIntegralRoots_unique (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l)
    (r s : IntegralRoots l E X) : r = s := by
  have h : r.hom = s.hom := by
    apply (isLimitOfPreserves
      (Mod.forget (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} l E.1) X))
      (limit.isLimit (spIntegralTwistSystem X l E))).hom_ext
    intro n
    change r.hom ≫ (limit.π (spIntegralTwistSystem X l E) n).hom =
      s.hom ≫ (limit.π (spIntegralTwistSystem X l E) n).hom
    rw [r.projections n.unop, s.projections n.unop]
  cases r
  cases s
  cases h
  rfl

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
