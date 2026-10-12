/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.PicardH1ProductSpanning
import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Injectivity of the two slice pullbacks in degree one

Source: Stacks Project, Varieties, Tag 0BED, applied in degree one to the structure sheaves
(blueprint: lem-sc-picard-h1-product-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem injective_pair_of_spanning
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (p : A →+ C) (q : B →+ C) (s : C →+ A) (t : C →+ B)
    (hspan : ∀ c, ∃ a b, p a + q b = c)
    (hsp : ∀ a, s (p a) = a) (htq : ∀ b, t (q b) = b)
    (hsq : ∀ b, s (q b) = 0) (htp : ∀ a, t (p a) = 0) :
    Function.Injective (s.prod t) := by
  intro c d h
  obtain ⟨a, b, hab⟩ := hspan (c - d)
  have hs : s (c - d) = 0 := by
    rw [map_sub, show s c = s d from congrArg Prod.fst h, sub_self]
  have ht : t (c - d) = 0 := by
    rw [map_sub, show t c = t d from congrArg Prod.snd h, sub_self]
  have ha : a = 0 := calc
    a = s (p a + q b) := by rw [map_add, hsp, hsq, add_zero]
    _ = s (c - d) := congrArg s hab
    _ = 0 := hs
  have hb : b = 0 := calc
    b = t (p a + q b) := by rw [map_add, htp, htq, zero_add]
    _ = t (c - d) := congrArg t hab
    _ = 0 := ht
  apply sub_eq_zero.mp
  calc
    c - d = p a + q b := hab.symm
    _ = 0 := by rw [ha, hb, map_zero, map_zero, zero_add]

/-- For proper `k`-schemes with only scalar global functions, the two rational-point slices
jointly detect classes in the first cohomology of the structure sheaf of their product.
Source: Stacks Project, Varieties, Tag 0BED, degree one
(blueprint: lem-sc-picard-h1-product-injective).

Proof: properness implies quasi-compactness and separatedness, hence affine diagonals
(`pqf-lem-proper-basic`). Apply `lem-sc-picard-kunneth-qcoh` to the structure sheaves in
degree one. The only summands have bidegrees `(1,0)` and `(0,1)`; scalar global sections
identify them with `H¹(X, O)` and `H¹(Y, O)`. Functoriality of the cup-product map shows that
pullback along `(1,y)` acts as the identity on the first summand and zero on the second:
the cross term factors through `Spec k`, whose first cohomology vanishes by
`pqf-lem-affine-vanishing`. Pullback along `(x,1)` similarly acts as zero and identity.
Thus the pair of pullbacks is the identity under the Kunneth identification, so is injective. -/
theorem picard_h1_product_injective (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))] [IsProper (Y ↘ Spec (CommRingCat.of k))]
    (hX : Function.Bijective (globalSectionsRingHom k (X := X)))
    (hY : Function.Bijective (globalSectionsRingHom k (X := Y)))
    (x : (X ↘ Spec (CommRingCat.of k)).fieldPoints k)
    (y : (Y ↘ Spec (CommRingCat.of k)).fieldPoints k) :
    let f := X ↘ Spec (CommRingCat.of k)
    let g := Y ↘ Spec (CommRingCat.of k)
    let iX : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ y.1) (by
      dsimp only [f, g]
      rw [Category.id_comp, Category.assoc, y.2]
      simp)
    let iY : Y ⟶ pullback f g := pullback.lift (g ≫ x.1) (𝟙 Y) (by
      dsimp only [f, g]
      rw [Category.id_comp, Category.assoc, x.2]
      simp)
    Function.Injective
      ((structureSheafCohomologyPullback iX 1).prod (structureSheafCohomologyPullback iY 1)) := by
  let f := X ↘ Spec (CommRingCat.of k)
  let g := Y ↘ Spec (CommRingCat.of k)
  let iX : X ⟶ pullback f g := pullback.lift (𝟙 X) (f ≫ y.1) (by
    dsimp only [f, g]
    rw [Category.id_comp, Category.assoc, y.2]
    simp)
  let iY : Y ⟶ pullback f g := pullback.lift (g ≫ x.1) (𝟙 Y) (by
    dsimp only [f, g]
    rw [Category.id_comp, Category.assoc, x.2]
    simp)
  change Function.Injective
    ((structureSheafCohomologyPullback iX 1).prod (structureSheafCohomologyPullback iY 1))
  have hcomp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
      (z : Sheaf.H (structureSheafAb C) 1) :
      structureSheafCohomologyPullback a 1 (structureSheafCohomologyPullback b 1 z) =
        structureSheafCohomologyPullback (a ≫ b) 1 z :=
    congrArg (fun e : Sheaf.H (structureSheafAb C) 1 →+
      Sheaf.H (structureSheafAb A) 1 ↦ e z)
      (structureSheafCohomologyPullback_functorial.2 a b 1).symm
  have hid (A : Scheme.{u}) (z : Sheaf.H (structureSheafAb A) 1) :
      structureSheafCohomologyPullback (𝟙 A) 1 z = z :=
    congrArg (fun e : Sheaf.H (structureSheafAb A) 1 →+
      Sheaf.H (structureSheafAb A) 1 ↦ e z)
      (structureSheafCohomologyPullback_functorial.1 A 1)
  have : Subsingleton (Sheaf.H (structureSheafAb (Spec (CommRingCat.of k))) 1) := by
    change Subsingleton
      (Modules.H (SheafOfModules.unit (Spec (CommRingCat.of k)).ringCatSheaf) 1)
    have := SheafOfModules.isQuasicoherent_unit.{u, u, u}
      (R := (Spec (CommRingCat.of k)).ringCatSheaf)
    exact Modules.subsingleton_H_succ_of_isAffine _ 0
  have hfst (a : Sheaf.H (structureSheafAb X) 1) :
      structureSheafCohomologyPullback iX 1
        (structureSheafCohomologyPullback (pullback.fst f g) 1 a) = a := by
    rw [hcomp, show iX ≫ pullback.fst f g = 𝟙 X from pullback.lift_fst .., hid]
  have hsnd (b : Sheaf.H (structureSheafAb Y) 1) :
      structureSheafCohomologyPullback iY 1
        (structureSheafCohomologyPullback (pullback.snd f g) 1 b) = b := by
    rw [hcomp, show iY ≫ pullback.snd f g = 𝟙 Y from pullback.lift_snd .., hid]
  have hcrossX (b : Sheaf.H (structureSheafAb Y) 1) :
      structureSheafCohomologyPullback iX 1
        (structureSheafCohomologyPullback (pullback.snd f g) 1 b) = 0 := by
    rw [hcomp, show iX ≫ pullback.snd f g = f ≫ y.1 from pullback.lift_snd ..,
      ← hcomp, Subsingleton.elim (structureSheafCohomologyPullback y.1 1 b) 0, map_zero]
  have hcrossY (a : Sheaf.H (structureSheafAb X) 1) :
      structureSheafCohomologyPullback iY 1
        (structureSheafCohomologyPullback (pullback.fst f g) 1 a) = 0 := by
    rw [hcomp, show iY ≫ pullback.fst f g = g ≫ x.1 from pullback.lift_fst ..,
      ← hcomp, Subsingleton.elim (structureSheafCohomologyPullback x.1 1 a) 0, map_zero]
  exact injective_pair_of_spanning
    (structureSheafCohomologyPullback (pullback.fst f g) 1)
    (structureSheafCohomologyPullback (pullback.snd f g) 1)
    (structureSheafCohomologyPullback iX 1) (structureSheafCohomologyPullback iY 1)
    (picard_h1_product_spanning k X Y hX hY) hfst hsnd hcrossX hcrossY

end AlgebraicGeometry.Scheme
