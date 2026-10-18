module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits

/-!
# Bounded representatives and bounded roofs in the derived category

Source: Stacks Project, `derived.tex`, Tags 05RW and 05RT--05RV
(blueprint: lem-kun-bounded-derived-roofs).
-/

@[expose] public section

universe u v w

open CategoryTheory Category Limits

namespace DerivedCategory

/--
(blueprint: lem-kun-bounded-derived-roofs)
Source: Stacks Project, `derived.tex`, Tags 05RT, 05RU, 05RV, 05RW and `homology.tex`
Tag 0118 (section-truncations).

Let `R` be a commutative ring and let `D^b(R)` be the bounded derived category of
`R`-modules.  The localization `Q` factors through the homotopy category `K(R)`; every
`C ∈ D^b(R)` has a cochain representative `K` supported in some `[a, b]`, `a ≤ b`; every
`u : C ⟶ C'` between bounded representatives is a bounded roof `K ← M → L` with `M ⟶ K`
a quasi-isomorphism, after transport along the chosen isomorphisms; two such roofs with
the same derived morphism have a bounded common refinement `P` by quasi-isomorphisms
`vᵢ : P ⟶ Mᵢ` with `v₁ ≫ s₁ ≃ v₂ ≫ s₂` and `v₁ ≫ g₁ ≃ v₂ ≫ g₂` chain homotopic.  The
equivalence of roofs is taken in `K(R)`; strict chain-map refinements need not exist.

Proof (the node's steps).
1. (def-weil-pbc-bounded-derived-subcategories, lem-sfb-bounded-representative;
   Tags 05RW, 05RV) `C ∈ D^b(R)` has cohomology zero below some `a` and above some `b`;
   enlarge to `a ≤ b`.  A bounded representative `K` supported in `[a, b]` with
   `C ≅ Q(K)` exists (`DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`); zero objects
   allow any interval.  Likewise for `C'`.
2. (lem-kun-derived-bounded-roof-factorization, def-weil-abstract-derived-category;
   Tag 05RW) For representatives `K, L` with `K` in `[a, b]` and `L` zero below `a`,
   transport `u` to `f : Q(K) ⟶ Q(L)`.  The bounded right factorization
   (`DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE`) gives `M` in `[a, b]`,
   `s : M ⟶ K`, `g : M ⟶ L` with `f = Q(s)⁻¹ ≫ Q(g)`.  `Q(s)` invertible makes every
   `Hⁿ(s)` invertible since `Hⁿ` factors through `Q`, so `s` is a quasi-isomorphism.
3. (lem-pc-quasi-isomorphisms-multiplicative-system,
   lem-pc-right-fraction-common-refinement; Tags 05RT, 05RU) If two roofs give the same
   morphism, work in `K(R)`: quasi-isomorphisms there have a right calculus of fractions
   with localization `D(R)`, and the right-fraction criterion gives `Z` and chain maps
   `tᵢ : Z ⟶ Mᵢ` with `s₁t₁ = s₂t₂` and `g₁t₁ = g₂t₂` in `K(R)` (chain homotopies) and
   the common denominator `s₁t₁` a quasi-isomorphism.  No calculus of fractions in
   `CoCh(R)` is asserted.
4. (def-weil-abstract-derived-category; elementary) Each `tᵢ` is a quasi-isomorphism:
   `Hⁿ(tᵢ) = Hⁿ(sᵢ)⁻¹ Hⁿ(sᵢtᵢ)`.  Choose `a < b` with `M₁, M₂, K, L` vanishing outside
   `[a, b]`; then `Hⁿ(Z) = 0` outside `[a, b]`.
5. (def-kun-truncations; homology Tag 0118) Put `T = τ_{≤b} Z`, `P = τ_{≥a} T`, with
   canonical `j : T ⟶ Z` and `q : T ⟶ P`.  By the cohomology of the truncations and
   Step 4, `j` and `q` are quasi-isomorphisms, and `P` is supported in `[a, b]`.
6. (def-kun-truncations; elementary) `rᵢ = tᵢ ∘ j` factors as `vᵢ ∘ q`: above `a` use
   `rᵢⁿ`, below `a` zero, in degree `a` the map from `Tᵃ / im d_T^{a-1}` induced by `rᵢᵃ`
   (it exists as `Mᵢ^{a-1} = 0`).  `Hⁿ(vᵢ) = Hⁿ(rᵢ) Hⁿ(q)⁻¹`, so `vᵢ` is a
   quasi-isomorphism.
7. (def-kun-truncations; elementary) Restrict the homotopy between `s₁t₁` and `s₂t₂`
   along `j` (at degree `b`, `d_Z^b` vanishes on `Tᵇ = ker d_Z^b`), and descend it along
   `q` (its degree-`a` component has target `K^{a-1} = 0`; the equation in degree `a`
   follows by precomposing with the surjection `qᵃ`).  This gives `s₁v₁ ≃ s₂v₂`; the same
   construction with target `L` gives `g₁v₁ ≃ g₂v₂`.  Homotopic maps have the same class
   in `K(R)`, so localization gives the same fraction; for other representative
   isomorphisms transport the endpoints as in Step 2.
-/
theorem boundedDerivedRoofs
    (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)] :
    (Nonempty
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh) ≅ DerivedCategory.Q)) ∧
      (∀ (C : DerivedCategory.Bounded (ModuleCat.{v} R)),
        ∃ (a b : ℤ) (K : CochainComplex (ModuleCat.{v} R) ℤ),
          a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
            Nonempty (C.1 ≅ DerivedCategory.Q.obj K)) ∧
      (∀ (C C' : DerivedCategory (ModuleCat.{v} R))
          (a b : ℤ) (K L : CochainComplex (ModuleCat.{v} R) ℤ),
        K.IsStrictlyGE a → K.IsStrictlyLE b →
        L.IsStrictlyGE a → L.IsStrictlyLE b →
        a ≤ b →
        ∀ (eC : C ≅ DerivedCategory.Q.obj K)
          (eC' : C' ≅ DerivedCategory.Q.obj L) (u : C ⟶ C'),
          ∃ (M : CochainComplex (ModuleCat.{v} R) ℤ)
            (_ : M.IsStrictlyGE a) (_ : M.IsStrictlyLE b)
            (s : M ⟶ K) (_ : QuasiIso s)
            (g : M ⟶ L),
            u = eC.hom ≫ inv (DerivedCategory.Q.map s) ≫
              DerivedCategory.Q.map g ≫ eC'.inv) ∧
      (∀ (K L M₁ M₂ : CochainComplex (ModuleCat.{v} R) ℤ)
          (s₁ : M₁ ⟶ K) (g₁ : M₁ ⟶ L)
          (s₂ : M₂ ⟶ K) (g₂ : M₂ ⟶ L)
          [hs₁ : QuasiIso s₁]
          [hs₂ : QuasiIso s₂],
        (∃ (a b : ℤ),
          a ≤ b ∧ K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧
            L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
            M₁.IsStrictlyGE a ∧ M₁.IsStrictlyLE b ∧
            M₂.IsStrictlyGE a ∧ M₂.IsStrictlyLE b) →
        inv (DerivedCategory.Q.map s₁) ≫ DerivedCategory.Q.map g₁ =
          inv (DerivedCategory.Q.map s₂) ≫ DerivedCategory.Q.map g₂ →
        ∃ (P : CochainComplex (ModuleCat.{v} R) ℤ)
          (v₁ : P ⟶ M₁) (v₂ : P ⟶ M₂),
          (∃ (c d : ℤ), c ≤ d ∧ P.IsStrictlyGE c ∧ P.IsStrictlyLE d) ∧
          QuasiIso v₁ ∧
          QuasiIso v₂ ∧
          Nonempty (Homotopy (v₁ ≫ s₁) (v₂ ≫ s₂)) ∧
          Nonempty (Homotopy (v₁ ≫ g₁) (v₂ ≫ g₂))) := by
  sorry

end DerivedCategory
