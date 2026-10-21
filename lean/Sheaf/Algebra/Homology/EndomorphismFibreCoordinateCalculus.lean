/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
public import Sheaf.Algebra.Homology.SignedMappingCoconeShift

/-! # Coordinates of the fibre of a chain endomorphism

Source: main-20261015, derived Nakayama first reduction, Cones paragraph;
Stacks Tags 014E and 011G.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)

The pair category is Mathlib's `Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))`.
Its objects have a complex `a` and an endomorphism `str`; morphisms have an underlying
chain map `f` and the intertwining equation `Hom.h`. Its category and preadditive
structures, and the shifts on this category, are the existing library structures.
The fibre and its shifts specialize the existing signed mapping-cocone construction.
All coordinate equalities below are equalities of morphisms in the abelian category.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The tautological endomorphism on the forgetful functor from endomorphism pairs.
Source: Stacks Tag 014E, functorial cone square; main-20261015, first reduction, Cones.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus) -/
def endomorphismPairTransformation :
    Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)) ⟶
      Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)) where
  app X := X.str
  naturality _ _ a := a.h

/-- The fibre functor on chain endomorphism pairs, with the canonical diagonal cone maps.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus) -/
def endomorphismFibreFunctor :
    Endofunctor.Algebra (𝟭 (CochainComplex A ℤ)) ⥤ CochainComplex A ℤ :=
  CategoryTheory.SignedCoconeShift.coconeFunctor
    (Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)))
    (Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)))
    endomorphismPairTransformation

/-- The tautological endomorphism commutes with the specified integer shifts.
Source: Stacks Tag 011G; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: the shift of a pair is its shifted complex with shifted endomorphism.
The forgetful shift comparison is the identity. Hence the required square is
`str[r] = str[r]`, using the shift conventions of def-weil-abstract-derived-category. -/
@[instance]
theorem endomorphismPairTransformation_commShift :
    NatTrans.CommShift (endomorphismPairTransformation (A := A)) ℤ := by
  sorry

/-- The specified natural signed shift comparison for the endomorphism-fibre functor.
Source: Stacks Tags 011G and 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus) -/
def endomorphismFibreShift (r : ℤ) :
    CategoryTheory.shiftFunctor (Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) r ⋙
        endomorphismFibreFunctor ≅
      endomorphismFibreFunctor ⋙ CategoryTheory.shiftFunctor (CochainComplex A ℤ) r :=
  CategoryTheory.SignedCoconeShift.coconeFunctorShiftNatIso
    (Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)))
    (Endofunctor.Algebra.forget (𝟭 (CochainComplex A ℤ)))
    endomorphismPairTransformation r

/-- The reordered fibre coordinates are a biproduct, with differential `(dv,-du-sv)`.
Source: Stacks Tags 014E and 011G; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: by def-sp-abelian finite biproducts exist. The mapping cone from
 def-weil-abstract-derived-category has differential `(du+sv,-dv)` at degree `q-1`.
Shifting by -1 negates it and exchanging the summands gives the displayed formulas.
The cone projections and inclusions are mutual biproduct coordinates, by their identity
and zero composites and the identity decomposition. Finally D squared has components
zero and `dsv-sdv=0` because s is a chain map. No boundedness is used. -/
theorem endomorphismFibre_coordinates
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) (q : ℤ) :
    IsIso (biprod.lift ((mappingCocone.fst X.str).f q)
        ((mappingCocone.snd X.str).v q (q - 1) (by omega))) ∧
      (mappingCocone X.str).d q (q + 1) ≫ (mappingCocone.fst X.str).f (q + 1) =
        (mappingCocone.fst X.str).f q ≫ X.a.d q (q + 1) ∧
      (mappingCocone X.str).d q (q + 1) ≫
          (mappingCocone.snd X.str).v (q + 1) q (by omega) =
        -((mappingCocone.snd X.str).v q (q - 1) (by omega) ≫ X.a.d (q - 1) q) -
          (mappingCocone.fst X.str).f q ≫ X.str.f q := by
  sorry

/-- The diagonal fibre functor is additive.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: intertwining maps are closed under addition, zero, identities and composition
by bilinearity (def-sp-abelian). The existing algebra category inherits these operations.
On each cone component the induced map is a, so the chain equation follows from
`da=ad` and `ta=as` (def-weil-abstract-derived-category). Identity and composition hold
componentwise; addition and zero likewise hold on both projections. -/
theorem endomorphismFibre_additive :
    (endomorphismFibreFunctor (A := A)).Additive := by
  sorry

/-- The fibre functor sends an intertwiner a to `(v,u) ↦ (av,au)`.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: the cone map of the square with both vertical maps a is diagonal. Shifting by
-1 preserves the two diagonal entries. Composition with each projection therefore
has the displayed value, by the cone and shift definitions in
 def-weil-abstract-derived-category. Together the projections determine the map. -/
theorem endomorphismFibre_map_coordinates
    {X Y : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))} (a : X ⟶ Y) (q : ℤ) :
    ((endomorphismFibreFunctor (A := A)).map a).f q ≫
          (mappingCocone.fst Y.str).f q =
        (mappingCocone.fst X.str).f q ≫ a.f.f q ∧
      ((endomorphismFibreFunctor (A := A)).map a).f q ≫
          (mappingCocone.snd Y.str).v q (q - 1) (by omega) =
        (mappingCocone.snd X.str).v q (q - 1) (by omega) ≫ a.f.f (q - 1) := by
  sorry

/-- Forward and inverse signed shift comparisons have coordinates `(v,(-1)^r u)`.
Source: Stacks Tags 011G and 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: write epsilon = (-1)^r. The source differential is `(epsilon dv,-epsilon du-sv)`
and the target differential is `(epsilon dv,-epsilon du-epsilon sv)` after reindexing.
Both composites with the signed diagonal are `(epsilon dv,-du-epsilon sv)`.
Thus it is a chain map; epsilon squared is one, so its inverse has the same formula.
The equations below test both inclusions, with the standard degree reindexing;
these determine the morphisms by finite biproducts (def-sp-abelian).
The natural isomorphism already includes naturality for every intertwiner. -/
theorem endomorphismFibreShift_coordinates
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) (r q : ℤ) :
    (mappingCocone.inl (X⟦r⟧).str).v q q (add_zero q) ≫
          ((endomorphismFibreShift r).hom.app X).f q =
        (mappingCocone.inl X.str).v (q + r) (q + r) (add_zero _) ≫
          (shiftFunctorObjXIso (mappingCocone X.str) r q (q + r) rfl).inv ∧
      (mappingCocone.inr (X⟦r⟧).str).1.v (q - 1) q (by omega) ≫
          ((endomorphismFibreShift r).hom.app X).f q =
        r.negOnePow • ((mappingCocone.inr X.str).1.v (q - 1 + r) (q + r) (by omega) ≫
          (shiftFunctorObjXIso (mappingCocone X.str) r q (q + r) rfl).inv) ∧
      (mappingCocone.inl X.str).v (q + r) (q + r) (add_zero _) ≫
          (shiftFunctorObjXIso (mappingCocone X.str) r q (q + r) rfl).inv ≫
          ((endomorphismFibreShift r).inv.app X).f q =
        (mappingCocone.inl (X⟦r⟧).str).v q q (add_zero q) ∧
      (mappingCocone.inr X.str).1.v (q - 1 + r) (q + r) (by omega) ≫
          (shiftFunctorObjXIso (mappingCocone X.str) r q (q + r) rfl).inv ≫
          ((endomorphismFibreShift r).inv.app X).f q =
        r.negOnePow • (mappingCocone.inr (X⟦r⟧).str).1.v (q - 1) q (by omega) := by
  sorry

/-- The specified signed comparisons satisfy zero and successive-shift coherence.
Source: Stacks Tag 011G; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: on the first inclusion both sides are the canonical reindexing. On the second,
zero uses (-1)^0=1 and addition uses (-1)^(r+r')=(-1)^r(-1)^r'. Reassociation of indices
is precisely the canonical shift coherence in def-weil-abstract-derived-category.
Equality on both inclusions implies equality, by def-sp-abelian. -/
theorem endomorphismFibreShift_coherence :
    endomorphismFibreShift (A := A) 0 =
        Functor.CommShift.isoZero (endomorphismFibreFunctor (A := A)) ℤ ∧
      ∀ r r' : ℤ, endomorphismFibreShift (A := A) (r + r') =
        Functor.CommShift.isoAdd (endomorphismFibreShift r) (endomorphismFibreShift r') := by
  sorry

/-- A strictly annihilated map satisfies the mapping-cocone lift equation.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: the differential of the zero degree -1 cochain is zero. The other summand is
`ofHom (J ≫ s)`, which vanishes by the strict annihilation hypothesis. This is the
chain-map condition for `(J,0)` in the coordinates of def-weil-abstract-derived-category. -/
theorem endomorphismFibreAugmentation_condition
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) {M : CochainComplex A ℤ}
    (J : M ⟶ X.a) (hJ : J ≫ X.str = 0) :
    δ (-1) 0 (0 : Cochain M X.a (-1)) + Cochain.ofHom (J ≫ X.str) = 0 := by
  sorry

/-- The strict augmentation into the fibre, constructed by the canonical cocone lift.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus) -/
def endomorphismFibreAugmentation
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) {M : CochainComplex A ℤ}
    (J : M ⟶ X.a) (hJ : J ≫ X.str = 0) :
    M ⟶ (endomorphismFibreFunctor (A := A)).obj X :=
  mappingCocone.lift X.str J 0 (endomorphismFibreAugmentation_condition X J hJ)

/-- The strict augmentation has coordinates `(J,0)`.
Source: Stacks Tag 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: in the reordered cone differential, D(J,0)=(dJ,-sJ)=(Jd,0) by the strict
annihilation and chain-map equations. The mapping-cocone lift has projections J and
zero, exactly the biproduct coordinates supplied by def-sp-abelian. -/
theorem endomorphismFibreAugmentation_coordinates
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) {M : CochainComplex A ℤ}
    (J : M ⟶ X.a) (hJ : J ≫ X.str = 0) (q : ℤ) :
    (endomorphismFibreAugmentation X J hJ).f q ≫ (mappingCocone.fst X.str).f q = J.f q ∧
      (endomorphismFibreAugmentation X J hJ).f q ≫
        (mappingCocone.snd X.str).v q (q - 1) (by omega) = 0 := by
  sorry

/-- Strict augmentations are natural in a commuting square.
Source: main-20261015, first reduction, Cones paragraph; Stacks Tag 014E.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: the two composites have first projections `J ≫ a` and `g ≫ J'`, equal by the
square hypothesis, and both have zero second projection. Equality of biproduct
components (def-sp-abelian) gives the asserted identity. -/
theorem endomorphismFibreAugmentation_naturality
    {X Y : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))} (a : X ⟶ Y)
    {M M' : CochainComplex A ℤ} (J : M ⟶ X.a) (J' : M' ⟶ Y.a)
    (hJ : J ≫ X.str = 0) (hJ' : J' ≫ Y.str = 0) (g : M ⟶ M')
    (hsquare : J ≫ a.f = g ≫ J') :
    endomorphismFibreAugmentation X J hJ ≫ (endomorphismFibreFunctor (A := A)).map a =
      g ≫ endomorphismFibreAugmentation Y J' hJ' := by
  sorry

/-- Strict annihilation persists under every integer shift.
Source: Stacks Tag 011G; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: the shift functor preserves compositions and zero, so the shifted composite
is the shift of `J ≫ s=0`. The shift of a pair is `(V[r],s[r])`, using the
forgetful identity comparison and def-weil-abstract-derived-category. -/
theorem endomorphismFibreAugmentation_shift_condition
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) {M : CochainComplex A ℤ}
    (J : M ⟶ X.a) (hJ : J ≫ X.str = 0) (r : ℤ) :
    J⟦r⟧' ≫ (X⟦r⟧).str = 0 := by
  sorry

/-- The same specified signed shift comparison preserves the strict augmentation.
Source: Stacks Tags 011G and 014E; main-20261015, first reduction, Cones paragraph.
(blueprint: lem-pe-endomorphism-fibre-coordinate-calculus)
Proof: shifting the annihilation equation gives the needed strict lift. Its coordinates
are `(J[r],0)`. Applying the signed comparison gives `(J[r],(-1)^r 0)=(J[r],0)`,
which are the coordinates of the shift of the original augmentation. Equality follows
from both biproduct projections (def-sp-abelian). No boundedness or exactness is used. -/
theorem endomorphismFibreAugmentation_shift
    (X : Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))) {M : CochainComplex A ℤ}
    (J : M ⟶ X.a) (hJ : J ≫ X.str = 0) (r : ℤ) :
    endomorphismFibreAugmentation (X⟦r⟧) (J⟦r⟧')
        (endomorphismFibreAugmentation_shift_condition X J hJ r) ≫
          (endomorphismFibreShift r).hom.app X =
      (endomorphismFibreAugmentation X J hJ)⟦r⟧' := by
  sorry

end CochainComplex
