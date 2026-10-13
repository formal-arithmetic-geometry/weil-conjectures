/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Comparison of the Hom complex with an opposite total complex

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product Hom differential;
cohomology.tex, Tags 0GM7 and 0GM8, finite-diagonal Hom calculation.
(blueprint: lem-sc-hom-complex-dual-total-comparison) -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

/-- Identify the short complex of the product Hom complex with the unop short complex
of the total
of its commuting Hom bicomplex in the opposite category, with the second index negated.
This comparison does not assume exact columns or boundedness.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product Hom differential;
cohomology.tex, Tags 0GM7 and 0GM8, the Hom calculation.
(blueprint: lem-sc-hom-complex-dual-total-comparison)

Proof: unop the coproduct cocone of the total in degree `-n`. It is a product
cone in module sheaves with factors indexed by `p+q=-n`. Reindex by `p`, so
`q=-p-n`, and use `e` to identify these factors with Hom(E^p,A^(p+n)).
The product universal property in `homComplex_exists` gives an isomorphism
of the degree objects. Multiply the p-th projection in degree n by the unit
`(-1)^(p*n+p*(p+1)/2)`. Its ratio under n increasing by one is `(-1)^p`,
and its ratio between (p+1,n) and (p,n+1) is `(-1)^(n+1)`.
The total differential has horizontal coefficient 1 and vertical coefficient
`(-1)^p`. The two assumed differential formulas therefore identify its unop,
with degrees reversed, with `d_A f - (-1)^n f d_E`. Check these equalities
on every product projection; no finiteness or sectionwise lifting is needed.
The isomorphisms in degrees n-1,n,n+1 give an isomorphism of short complexes
between the Hom short complex at n and the unop of the total short complex
at -n. This is the asserted short-complex isomorphism;
its construction uses only products and the two differential formulas.
Empty or zero products obey the same argument. -/
theorem homComplex_sc_iso_dual_total
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (K : HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (e : ∀ p q : ℤ, (K.X p).X q ≅ op (SheafOfModules.homObj (E.X p) (A.X (-q))))
    (h₁ : ∀ p p' q : ℤ,
      (K.d p p').f q ≫ (e p' q).hom = (e p q).hom ≫
        (SheafOfModules.homObjMap (E.d p p') (𝟙 (A.X (-q)))).op)
    (h₂ : ∀ p q q' : ℤ,
      (K.X p).d q q' ≫ (e p q').hom = (e p q).hom ≫
        (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.d (-q') (-q))).op)
    (n : ℤ) :
    Nonempty ((CategoryTheory.homComplex E A).sc n ≅
      ((K.total (ComplexShape.up ℤ)).sc (-n)).unop) := by sorry

end CochainComplex
