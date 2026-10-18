/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure

/-!
# K-flat resolutions and the homotopy derivability structure

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-kflat-derivability).

The hypotheses and conclusions are stated for an arbitrary Grothendieck abelian monoidal
category.  The K-flat property on the homotopy category is expressed by the existence of a
K-flat cochain-complex representative; the quotient and its localizer morphism provide the
full subcategory and its restricted quasi-isomorphisms.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

/--
Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-kflat-derivability).

Proof plan.  A Grothendieck abelian category has small colimits and exact filtered colimits;
the two-sided flat objects contain zero and are closed under finite sums and direct summands,
so the supplied functorial flat epimorphisms are covers by the flat class.  The functorial
bounded-above flat-resolution statement gives one functor on all bounded-above complexes,
with a natural quasi-isomorphism and flat terms, compatible with every upper bound.  Apply it
to good truncations and take their integer-indexed termwise colimit to obtain a functor `R`
on all unbounded complexes and a natural map `r` to the identity.  Exactness of filtered
colimits identifies cohomology of this colimit with the colimit of the cohomologies, so each
component of `r` is a quasi-isomorphism.  The bounded-above flat-complex result makes each
stage two-sided K-flat.  Tensoring the colimit with a quasi-isomorphism commutes with the
colimit in either variable because tensoring preserves all small colimits; the stagewise
quasi-isomorphisms therefore show that every `R`-value is K-flat.  K-flatness is invariant
under homotopy and closed under zero, shifts and cones by the K-flat homotopy-triangulated
statement.  Finally apply the homotopy-resolution derivability criterion to `R` and `r`;
this gives the left derivability structure on the full subcategory of `K(C)` consisting of
objects with K-flat representatives.  The construction is functorial on complexes only.
-/
theorem kFlat_derivability
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ (X : C), PreservesColimits (tensorLeft X)]
    [∀ (X : C), PreservesColimits (tensorRight X)]
    (P : C ⥤ C) (p : P ⟶ 𝟭 C)
    (hflat : ∀ X : C, ObjectProperty.flat (P.obj X))
    (hepi : ∀ X : C, Epi (p.app X)) :
    ∃ (R : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
      (r : R ⟶ 𝟭 (CochainComplex C ℤ)),
      (∀ X : CochainComplex C ℤ, (R.obj X).IsKFlatForTotalTensor) ∧
      (∀ X : CochainComplex C ℤ, QuasiIso (r.app X)) ∧
      (HomotopyCategory.quasiIsoLocalizerMorphism
        (fun K : HomotopyCategory C (.up ℤ) =>
          ∃ X : CochainComplex C ℤ,
            (HomotopyCategory.quotient C (.up ℤ)).obj X = K ∧
              X.IsKFlatForTotalTensor)).IsLeftDerivabilityStructure := by
  sorry

end CategoryTheory
