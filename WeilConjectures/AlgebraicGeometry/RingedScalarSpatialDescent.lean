/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedScalarSpatialOrdinaryEquation

/-! # Descent of ordinary scalar/spatial coherence to the derived comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D
(`lemma-derived-pullback-composition`) and Tag 0FPI; agent normalized K-flat descent,
Steps 3--5 of the parent proof.
(blueprint: new-ringed-scalar-spatial-descent)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.RingedRefinement

/-- If the ordinary scalar comparison commutes with the ordinary spatial compositor
(`hOrd`), then the derived scalar comparison `sc.pull` commutes with the derived spatial
compositor `p.pullComp`, functor associators displayed:
`c_{gf,a} ∘ (α^B_{f,g} S^W_a) = (S^U_a α^A_{f,g}) ∘ (c_{f,a} P^A_g) ∘ (P^B_f c_{g,a})`.

Source: Stacks, sites-cohomology.tex, Tag 0D6D; agent normalized descent.

Proof.
1. Apply the finite-word descent lemma (blueprint
lem-trf-ringed-kflat-word-comparison-descent) to the six ringed sites `(X, A_X)`,
`(X, B_X)`, `X ∈ {U, V, W}`, with geometric edges `f, g, f ≫ g` (ordinary pullbacks of
ringed topoi, by `c.pull`) and scalar edges `a_X` (the K-flat universal pairs `o.scalar`);
exact geometric edges use their exact localization (`Operation.left`,
`mapDerivedCategoryFactors`). Every complex has a flat-term K-flat resolution `P`, every
intermediate word of `P` stays flat-term K-flat, all word counits at `P` are invertible, and
a derived comparison is unique given its counit equation at such `P`.
2. `sc.pull f a` satisfies the counit equation of the descent of `sc.ordinary f a`: this is
`sc.representative`. `p.pullComp f g R` is by definition the termwise localization of
`p.ordinaryComp f g R` with the canonical composition factor, so the exact-functor
factorization (blueprint lem-weil-pbc-exact-functor-derived-factorization) gives its counit
equation on every complex. By uniqueness both are the descents of their ordinary maps.
3. Descent preserves vertical composition and whiskering, so both sides of the claim, after
the invertible target word counit for `E_U F^A_{gf}` at `Q P`, equal the source word counit
followed by `Q` of the corresponding side of `hOrd` at `P`. By `hOrd` these agree; cancel the
counit, and equality on all resolutions `Q P` gives equality of natural transformations.
The same argument runs on the vertical sequence sites in systems mode.
(blueprint: new-ringed-scalar-spatial-descent) -/
theorem ringedScalarSpatialDescent
    (m : SheafOfModules.OpenTensorNormalization.Mode) (T : Scheme.{u})
    (c : Coefficients m T) (o : Calculus c)
    (p : Spatial o) (sc : ScalarComparisons o)
    {A B : Rings m T} (a : A ⟶ B) {U V W : Over T}
    (f : U ⟶ V) (g : V ⟶ W)
    (hOrd :
      (Functor.associator (o.scalar W a).E
        (o.operation g B).pullback (o.operation f B).pullback).hom ≫
          Functor.whiskerLeft (o.scalar W a).E ((p.ordinaryComp f g B).hom) ≫
          (sc.ordinary (f ≫ g) a).hom =
        Functor.whiskerRight (sc.ordinary g a).hom (o.operation f B).pullback ≫
          (Functor.associator (o.operation g A).pullback
            (o.scalar V a).E (o.operation f B).pullback).hom ≫
          Functor.whiskerLeft (o.operation g A).pullback (sc.ordinary f a).hom ≫
          (Functor.associator (o.operation g A).pullback
            (o.operation f A).pullback (o.scalar U a).E).inv ≫
          Functor.whiskerRight ((p.ordinaryComp f g A).hom)
            (o.scalar U a).E) :
    (Functor.associator (o.scalar W a).T
      (o.operation g B).left (o.operation f B).left).hom ≫
        Functor.whiskerLeft (o.scalar W a).T (p.pullComp f g B).hom ≫
        (sc.pull (f ≫ g) a).hom =
      Functor.whiskerRight (sc.pull g a).hom (o.operation f B).left ≫
        (Functor.associator (o.operation g A).left
          (o.scalar V a).T (o.operation f B).left).hom ≫
        Functor.whiskerLeft (o.operation g A).left (sc.pull f a).hom ≫
        (Functor.associator (o.operation g A).left
          (o.operation f A).left (o.scalar U a).T).inv ≫
        Functor.whiskerRight (p.pullComp f g A).hom
          (o.scalar U a).T := by
  sorry

end SheafOfModules.RingedRefinement
