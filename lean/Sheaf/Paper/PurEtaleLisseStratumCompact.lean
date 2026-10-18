/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CompactObject
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Compactness of a lisse sheaf extended from a locally closed stratum

Source: Bhatt--Scholze, *Pro-étale topology*, Section 6.4, Example 6.4.1,
Lemmas 6.4.4 and 6.4.6, and the last paragraph of Proposition 6.4.8,
printed pp. 48--49 (blueprint: lem-pur-etale-lisse-stratum-compact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A finite locally constant flat module sheaf, extended by zero from a locally closed
stratum and then pushed forward to the ambient finite-type scheme, is compact in the
unbounded ordinary étale derived category. No separatedness of `X` is assumed.

Proof, following the node (adjoint form of Bhatt--Scholze, Section 6.4):
1. Put `W = X \ g(Z)` with open inclusion `q : W ⟶ X`. A finite affine cover of `X` by
   finite-type `k`-algebras restricts to one of `Z`, so `Z` is finite type over `k`
   (`def-weil-closed-immersion`). By `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-noetherian-open-subscheme-noetherian`, `X, Z, V, W` are Noetherian, hence
   quasi-separated (`lem-weil-pbc-locally-noetherian-quasi-separated`).
   `lem-weil-pbc-qcqs-morphism-permanence` makes `j, q` quasi-compact, hence finite type
   (`lem-weil-pbc-qc-open-immersion-finite-type`), and the structure map `a : V ⟶ Spec k`
   qcqs. No separatedness is used.
2. Module sheaves form Grothendieck abelian categories
   (`lem-weil-pbc-module-sheaves-grothendieck-abelian`), so derived coproducts are termwise
   and exact (`lem-kun-grothendieck-derived-coproducts`). Exact inverse image is a left
   adjoint (`prop-weil-pbc-inverse-image-modules-exact`), so `g^*, j^*, q^*` and étale slice
   restrictions preserve derived coproducts.
3. `C` is torsion and `k` separably closed: `lem-etale-finite-type-sep-closed-derived-dimension`
   applied separately to `q` and `a`, with `lem-etale-qcqs-finite-dimension-derived-coproducts`,
   gives that `Rq_*` and `Ra_*` preserve coproducts. Sections on `(Spec k)_ét` are exact and
   preserve sums (`lem-weil-pbc-spec-algebraically-closed-etale-sheaf-constant`), so
   `RΓ(V, -)` preserves coproducts.
4. `g_*` is exact (`lem-cbc-open-closed-recollement`), so `Rg_* = g_*` and the closed counit
   (`prop-weil-open-closed-recollement-adjunctions`) gives `g^* g_* ≅ id`. Compare the
   closed-support triangles `g_* Rg^! K → K → Rq_* q^* K` (`lem-exc-closed-support-triangle`,
   `lem-exc-closed-ambient`) for `K_i` and for `⨁ K_i`; steps 2 and 3 make the last two
   comparisons isomorphisms, so the first is too, and applying `g^*` shows that `Rg^!`, hence
   `B = j^* Rg^!`, commutes with coproducts.
5. On each nonempty member of a trivializing étale cover, `L` is constant with value a finite
   `C`-module `P`, flat as a geometric stalk. `P` is finitely presented (finite kernel of
   `C^n → P`), hence projective (`lem-weil-pbc-finitely-presented-flat-module-projective`),
   hence a retract of `C^n`; the constant sheaf is a retract of `C_V^n` there.
6. Put `H_L(N) = RHom_C(L, N)` (`def-pur-derived-internal-hom`). The comparison
   `⨁ H_L(N_i) → H_L(⨁ N_i)` may be tested after trivializing restrictions
   (`lem-weil-pbc-ringed-internal-hom-exact-restriction`, step 2). There
   `RHom_C(C^n, N) ≅ N^n` gives an isomorphism, and the retract `v u = id_L` gives the
   inverse `S(u) α_{C^n}⁻¹ T(v)` of `α_L`. Exact stalks
   (`prop-weil-pbc-geometric-stalks-exact`) and conservativity
   (`lemma-weil-pbc-geometric-stalk-conservative`) on cohomology sheaves conclude.
7. For `j : V ⟶ Z`, the adjunctions `g_* ⊣ Rg^!`, `j_! ⊣ j^*` and
   `lem-pur-rhom-global-sections` give, naturally in `K`,
   `Hom_X(g_* j_! L, K) ≅ Hom_V(L, j^* Rg^! K) ≅ H^0 RΓ(V, H_L(B K))`. `B`, `H_L` and
   `RΓ(V, -)` preserve coproducts by steps 4, 6 and 3, and `H^0` commutes with direct sums
   of complexes of `C`-modules (`lem-weil-pbc-ring-modules-grothendieck-abelian`). Hence the
   comparison of `def-pc-compact-object` is bijective, including for an empty family.

Source: Bhatt--Scholze, *Pro-étale topology*, Section 6.4, Example 6.4.1, Lemmas 6.4.4 and
6.4.6, and the last paragraph of the proof of Proposition 6.4.8, printed pp. 48--49
(blueprint: lem-pur-etale-lisse-stratum-compact). -/
theorem isCompactObject_lowerStar_openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf
    {k : Type u} [Field k] [IsAlgClosed k]
    (ell : ℕ) (hell : Nat.Prime ell) (hellk : IsUnit (ell : k))
    {C : Type (u + 1)} [CommRing C] [Finite C]
    (hC : ∃ r : ℕ, (ell : C) ^ r = 0)
    {X Z V : Scheme.{u}}
    (g : Z ⟶ X) [IsClosedImmersion g]
    (j : V ⟶ Z) [IsOpenImmersion j]
    (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} C))
    [Scheme.IsFiniteLocallyConstantSheaf L]
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ V),
      ObjectProperty.flat ((Scheme.pointSmallEtale s).sheafFiber.obj L)) :
    ∃ (hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C X)),
      @IsCompactObject (DerivedCategoryModule C X) _ _ hcoprod
      ((DerivedCategory.singleFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} C) g).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} C) j).obj L))) := by
  sorry

end AlgebraicGeometry.Etale
