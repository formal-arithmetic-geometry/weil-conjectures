/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveChernHomEndpoints

/-! # Encoding precomposition by the Cartier class as its tensor action

This is a comparison of single arrows; no natural transformation or shift structure is assumed.
(blueprint: lem-pur-b3-projective-chern-hom-tensor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedForgetTwoInjective

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- Encoding native Hom precomposition gives tensoring with the encoded Cartier arrow.

Source: the tensor-Hom evaluation identity, Stacks 08J9 and 0A95, and the exact native
coefficient encoding in the projective Cartier construction.
(blueprint: lem-pur-b3-projective-chern-hom-tensor).

Proof: the positive Tate coefficient is an invertible module. Evaluation identifies Hom
from this coefficient shifted by two with tensor by its inverse shifted by minus two.
On complexes the precomposition square for a map from the unit is the tensor-Hom mate
square: evaluating phi after the class is the same as tensoring phi with that class and
then evaluating. Apply this square on simultaneous K-flat source and K-injective target
models. The coefficient encoding is an exact equivalence carrying the relative tensor,
unit, Tate pairing and evaluation to their ordinary module counterparts: all underived
maps take a pure tensor to the same pure tensor, and all differential signs coincide.
The square therefore descends to the derived categories. Its encoded class is exactly
projectiveChernPositiveClass, by the defining mapSingleArrow formula. Restrict to the
sheaf input M and its twisted pullback. The unit and inverse-Tate evaluation supply the
isomorphisms s and t in ProjectiveChernNormalized. Replacing either endpoint comparison by
another isomorphism only composes s with a source automorphism or t with a target
automorphism, and so preserves the stated existential normalization. The argument is
local on the scheme for K-flatness and uses exact open extension by zero; separatedness
is not used. The zero sheaf and empty scheme have the unique zero maps and unit isomorphisms. -/
theorem projectiveChernHom_normalized
    (H : (DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)))ᵒᵖ ×
        DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)) ⥤
          DerivedCategory (ProEtaleWeilSheaf k₀ l (ProjectiveLine X)))
    (ρ : Representatives
      (standardHomModel (ProEtaleWeilSheaf.ihomBifunctor k₀ l (ProjectiveLine X))).complex H)
    (C : ProEtale.NativeCartier.Construction k₀ l) (M : WeilSheaf k₀ l X)
    (e : ((upperStar (ProjectiveLine X ↘ X)).obj
          ((tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)).obj
            (WeilSheaf.toComplex.obj M))).obj ≅
      H.obj (op (projectiveChernHomTate (l := l) X),
        ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)).obj))
    (f : H.obj (op (projectiveChernHomUnit (l := l) X),
          ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)).obj) ≅
      ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)).obj) :
    ProjectiveChernNormalized X C M
      (ObjectProperty.homMk (e.hom ≫
        ((Functor.curry.obj H).map (projectiveChernNativePositiveClass X C).op).app
          ((upperStar (ProjectiveLine X ↘ X)).obj (WeilSheaf.toComplex.obj M)).obj ≫
        f.hom)) := by sorry

end AlgebraicGeometry.WeilComplex
