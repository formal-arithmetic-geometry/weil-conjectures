/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex

/-! # Vanishing of the complementary block on a reduced scheme

Source: `thm-pc-semicontinuity-base-change`, proof (3), larger minors vanish.
(blueprint: lem-pc-complementary-block-vanishes)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- A block diagonal form with an invertible a by a pivot has zero complementary
block if its field-valued fibre ranks are at most a on a reduced scheme.

Source: `thm-pc-semicontinuity-base-change`, proof (3), reducedness step in the
normal-form claim. (blueprint: lem-pc-complementary-block-vanishes)

Proof: For each z in U choose the field-valued point g from hrank. Its image is
j(z), so g factors through j and then through U, since both maps are open
immersions. Pull back hform to this field point, and take global sections.
The chosen bases remain isomorphisms, and f remains invertible. Thus the rank
of the original fibre matrix is a plus the rank of the fibre matrix of δ:
the image of a block diagonal linear map is the direct sum of its two images.
The upper bound a forces the latter rank to be zero, hence every entry of δ
vanishes at this field point. The field map factors through the residue field
at z by the stalk map; this is a field extension and hence injective. Each
entry therefore vanishes in that residue field. On any affine open in U each
entry belongs to every prime ideal, hence to the nilradical. The affine ring
is reduced, because U is an open subscheme of the reduced scheme Y. Its
nilradical is zero, so each entry is zero on that affine open. Affine opens
cover U, and the sheaf axiom implies that δ is zero. Empty U is vacuous;
if a = 0 this is the same reduced-ring criterion applied to the whole map;
if either complementary rank is zero its morphism is automatically zero. -/
theorem complementary_block_eq_zero_of_rank_le
    {Y Z : Scheme.{u}} [IsReduced Y] {M N : Y.Modules} {m n : ℕ}
    (eM : M ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin m)))
    (eN : N ≅ free (R := Y.ringCatSheaf) (ULift.{u} (Fin n)))
    (φ : M ⟶ N) (j : Z ⟶ Y) [IsOpenImmersion j] (a : ℕ) (U : Z.Opens)
    (hrank : ∀ z : Z, z ∈ U →
      ∃ (R : CommRingCat.{u}) (_ : IsField R) (g : Spec R ⟶ Y),
        Set.range g.base = {j.base z} ∧
        ((freeMatrix (eM.inv ≫ φ ≫ eN.hom)).map g.appTop).rank ≤ a)
    (eS : ((Modules.pullback j).obj M).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (m - a))))
    (eT : ((Modules.pullback j).obj N).restrict U.ι ≅
      free (ULift.{u} (Fin a)) ⊞ free (ULift.{u} (Fin (n - a))))
    (f : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin a)) ⟶
      free (ULift.{u} (Fin a))) [IsIso f]
    (δ : free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (m - a))) ⟶
      free (ULift.{u} (Fin (n - a))))
    (hform : (restrictFunctor U.ι).map ((Modules.pullback j).map φ) =
      eS.hom ≫ biprod.map f δ ≫ eT.inv) : δ = 0 := by sorry

end AlgebraicGeometry.Scheme.Modules
