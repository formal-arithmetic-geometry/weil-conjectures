/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

/-!
# Derived Hom from a bounded-above projective complex

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, case (2), together with
Tag 06XR (blueprint: lem-sc-affine-projective-complex-derived-hom).

The ring is a commutative ring with identity, as in the Stacks conventions.
Modules are encoded on the one-point site using the shared `onePointRingSheaf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory

/-- A bounded-above projective complex computes derived Hom into a bounded-below complex:
`Q Hom^•(P, L) ≅ R Hom(P, L)`, the comparison being the image under `Q` of the canonical
map `Hom^•(P, L) → Hom^•(P, I(L))` for any functorial K-injective replacement `L → I(L)`,
and the cohomology of `Hom^•(P, L)` vanishes in all sufficiently negative degrees.

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, case (2), together with
Tag 06XR (blueprint: lem-sc-affine-projective-complex-derived-hom).

Proof:
1. Choose the functorial K-injective resolution `L → I(L)` supplied by
   `def-pur-derived-internal-hom`. The bounded-above projective complex `P` is K-projective
   by `lem-sc-bounded-above-projective-kprojective` (`isKProjective_of_projective`).
2. Applying `Hom(P, -)` to the cone of `L → I(L)` gives an acyclic complex. Hence
   `Hom(P, L) → Hom(P, I(L))` is a quasi-isomorphism and becomes an isomorphism under `Q`.
   By `derivedInternalHom_comparison`, the latter complex represents derived internal Hom.
3. The product terms of `homComplex` (`def-pur-derived-internal-hom`, through
   `def-pur-hom-complex`) are `∏ p, Hom(P^p, L^(p+n))`. A nonzero factor requires
   `p ≤ d` and `e ≤ p+n`, which is impossible when `n < e-d`. Thus the terms, and then
   their cohomology, vanish in all sufficiently negative degrees. -/
theorem affineProjectiveComplexDerivedHom
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R)))]
    (P L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf R))) ℤ)
    (d e : ℤ)
    [P.IsStrictlyLE d] [L.IsStrictlyGE e]
    [∀ n : ℤ, Projective (P.X n)] :
    Nonempty (DerivedCategory.Q.obj
        (homComplex (R := CochainComplex.onePointRingSheaf R) P L) ≅
      (derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf R)).obj
        (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L)) ∧
    (∀ (I : CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ ⥤
        CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ)
      (η : 𝟭 (CochainComplex (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf R))) ℤ) ⟶ I),
      (∀ N : CochainComplex (SheafOfModules.{u}
          ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (CochainComplex.onePointRingSheaf R))) ℤ,
        QuasiIso (η.app N) ∧ (I.obj N).IsKInjective) →
        IsIso (DerivedCategory.Q.map
          (((homComplexFunctor (R := CochainComplex.onePointRingSheaf R)).obj (op P)).map
            (η.app L)))) ∧
    ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((homComplex (R := CochainComplex.onePointRingSheaf R) P L).homology n) := by
  sorry

end CategoryTheory
