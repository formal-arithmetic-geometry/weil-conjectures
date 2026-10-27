/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The universal isomorphism locus of a diagram of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05XD,
`spaces-more-morphisms-lemma-where-isomorphism`
(blueprint: lem-sfb-space-universal-isomorphism-open).

The open subspace represents the isomorphism condition after arbitrary algebraic-space
base change. If the base is represented by a scheme, its open subspace is represented by
an open subscheme, with the representing isomorphism compatible with the inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universal isomorphism locus is open, including on a scheme base.
Source: Stacks Project, More on Morphisms of Spaces, Tag 05XD,
`spaces-more-morphisms-lemma-where-isomorphism`
(blueprint: lem-sfb-space-universal-isomorphism-open).

Proof: (1) Universal closedness implies closedness by the identity base change; local
finite presentation implies local finite type on every chart, since finitely presented
algebras are finitely generated, using def-sfb-space-morphism-properties,
def-sbc-locally-finite-presentation and def-weil-finite-type-morphism.
(2) Apply lem-sfb-space-universal-surjective-flat-open (Tag 05XC) to obtain an open
subspace V1 representing the simultaneous surjectivity and flatness condition.
(3) Apply lem-sfb-space-universal-closed-immersion-open (Tag 05XA), using (1), to obtain
an open subspace V2 representing the closed immersion condition.
(4) Intersect the two subfunctors. Every scheme test is the intersection of the two
representing open subschemes, so this is an open subspace. Factorization through it is
equivalent to factorization through both V1 and V2, by the pointwise intersection.
(5) A factorization therefore makes the base-changed morphism surjective, flat and a
closed immersion, hence an isomorphism by
lem-sfb-space-surjective-flat-closed-immersion-isomorphism. Conversely an isomorphism is
surjective on points and representably a closed immersion (def-weil-closed-immersion).
Choose a scheme atlas of its target and use the inverse isomorphism to give a chart of
the source; the induced scheme morphism is the flat identity. The flat chart criterion
lem-sfb-space-local-properties-chart-test gives flatness on all chart diagrams. Thus
the test map factors through both opens and their intersection. Fibre products are the
sheaf fibre products of lem-trf-space-fibre-products-etale-covers.
(6) When B is represented by a scheme, apply the scheme-test defining property of
def-a1-space-open-subspace to its identity, transported along the representing
isomorphism. This gives the claimed open subscheme and inclusion compatibility. -/
theorem exists_openSubspace_universal_isomorphism {S : Scheme.{u}}
    (A C B : AlgebraicSpace S) (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C)
    (w : f ≫ q = p)
    (hp_lfp : MapIsLocallyOfFinitePresentation p) (hp_flat : MapIsFlat p)
    (hp_closed : MapIsUniversallyClosed p)
    (hq_lft : MapIsLocally (@LocallyOfFiniteType) q)
    (hq_closed : IsClosedMap (mapPoint q.hom.hom)) (hq_sep : MapIsSeparated q) :
    ∃ U : OpenSubspace B,
      (∀ (B' : AlgebraicSpace S) (h : B' ⟶ B),
        (∃ l : B'.obj.obj ⟶ U.val.toFunctor, l ≫ U.val.ι = h.hom.hom) ↔
          IsIso (pullback.map p.hom h.hom q.hom h.hom f.hom (𝟙 B'.obj) (𝟙 B.obj)
            (by simpa using (congrArg (fun k : A ⟶ B ↦ k.hom) w).symm)
            (by simp))) ∧
      (∀ (T : Over S) (e : B.obj.obj ≅ yoneda.obj T),
        ∃ (V : Over S) (j : V ⟶ T), IsOpenImmersion j.left ∧
          ∃ eU : U.val.toFunctor ≅ yoneda.obj V,
            U.val.ι ≫ e.hom = eU.hom ≫ yoneda.map j) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
