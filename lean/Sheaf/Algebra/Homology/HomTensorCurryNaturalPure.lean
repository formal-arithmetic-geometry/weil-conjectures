/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Algebra.Homology.HomTensorDegreewise

/-!
# Pure-tensor evaluation of currying naturality

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-curry-natural-pure)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- Naturality of the pure-tensor equation for two degreewise currying maps.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, functoriality,
referring to More on Algebra, Lemma 15.73.1.
(blueprint: lem-sc-hom-tensor-curry-natural-pure)

Proof: Apply the currying condition for the primed complexes to the image of s
under the iterated Hom map. The componentwise action specified by
homComplex_exists first evaluates the outer map at f^i(x), then the inner map
at g^j(y), and postcomposes the result with h^(i+j+n). Thus the left side is
h^(i+j+n)(phi_i(f^i(x))_j(g^j(y))). For the right side use the same Hom-complex
projection formula. Precomposition by the total tensor map restricts to the
termwise tensor map on the (i,j) summand by ι_mapBifunctorMap. Naturality of
the sheafification unit, its tensorator and the tensor comparison sends the
image of x tensor y to the image of f^i(x) tensor g^j(y). Apply the unprimed
currying condition to obtain the same value. This is an equality on one pure
tensor; no coproduct, sheafification or internal-Hom extensionality is used. -/
theorem homTensorCurry_natural_pure
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a : (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n)
      (a' : (homComplex (R := R) K' (homComplex (R := R) L' M')).X n ⟶
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M').X n),
    HomTensorCurryCondition R K L M n a →
    HomTensorCurryCondition R K' L' M' n a' →
    ∀ (U : Cᵒᵖ)
      (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
      (W : (Over U.unop)ᵒᵖ) (i j : ℤ)
      (x : (K'.X i).val.obj (op W.unop.left))
      (y : (L'.X j).val.obj (op W.unop.left)),
      let α := (((homComplexFunctor (R := R)).map f.op).app
          (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)
      let β := (((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
        ((homComplexFunctor (R := R)).obj
          (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h
      let z := ((CochainComplex.ιMapBifunctor K' L' (curriedTensor Mod)
          i j (i + j) rfl).val.app (op W.unop.left)).hom
        (((homTensorSectionMap R (K'.X i) (L'.X j)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))
      (((((α.f n ≫ a') ≫ homTensorProjection R
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M'
            n (i + j) (i + j + n) rfl).val.app U).hom s).app W).hom z =
        (((((a ≫ β.f n) ≫ homTensorProjection R
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M'
            n (i + j) (i + j + n) rfl).val.app U).hom s).app W).hom z := by sorry

end CategoryTheory
