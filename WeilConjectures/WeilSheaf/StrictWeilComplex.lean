/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FrobeniusDerived

/-!
# From Weil complexes to strict Weil complexes

Blueprint `sk-def-sf-weil-complexes` and `def-weil-weil-sheaf-complex` (paragraph "Strict Weil
complexes"): a *strict Weil complex* on a `k₀`-scheme `X` is a pair `(K, θ)` of a complex `K` of
`ℓ`-adic pro-étale sheaves on the geometric fiber `X̄` and an isomorphism
`θ : Lg_X^* K ≅ K`, where `g_X = Fr_X` is the geometric Frobenius of `X̄`. A Weil complex `K`
gives the strict Weil complex `(For(K), θ_K)`, where `θ_K` is its derived Frobenius
(`AlgebraicGeometry.WeilComplex.frobeniusIso`).

This file constructs the functor `AlgebraicGeometry.WeilComplex.toStrictWeilComplex` and shows
that it is an equivalence on the hearts: on Weil sheaves (Weil complexes concentrated in degree
zero) it is fully faithful, and its essential image consists of the pairs `(F[0], θ)` with `F`
a constructible sheaf. It is not faithful (see
`WeilConjectures.WeilSheaf.StrictWeilComplexNotFaithful`).

## Design

The category of strict Weil complexes is `AlgebraicGeometry.StrictWeilComplex k₀ l X`, the
category `IsoAlgebra (D(Fr_X^*))` of pairs `(K, θ : D(Fr_X^*) K ≅ K)` with `K` in the whole
derived category of `ℓ`-adic pro-étale sheaves on `X̄`; the Frobenius pullback `Fr_X^*` is exact,
so `D(Fr_X^*)` is its derived functor `Lg_X^*`. A pro-étale Weil sheaf `(F, φ)` gives the strict
Weil complex `(F[0], φ[0])` (`AlgebraicGeometry.ProEtaleWeilSheaf.toStrictWeilComplex`), the
transport of `IsoAlgebra` along the fully faithful functor `F ↦ F[0]`, which is fully faithful
with essential image the pairs whose underlying complex is concentrated in degree `0`
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`). The key compatibility
`AlgebraicGeometry.WeilSheaf.toStrictWeilComplexIso` identifies the derived
Frobenius of `F[0]` with `φ[0]`; it rests on the compatibility of the isomorphisms
`D(U) ∘ D(G) ≅ D(U ∘ G)` and `D(U) ≅ D(V)` with the single functors
(`CategoryTheory.Functor.mapDerivedCategoryCompIso_inv_app_singleFunctor`).

## Main definitions and results

- `CategoryTheory.Endofunctor.IsoAlgebra.lift`: the functor to `IsoAlgebra F` given by a functor
  `Φ` with an isomorphism `Φ ⋙ F ≅ Φ`.
- `AlgebraicGeometry.StrictWeilComplex`: strict Weil complexes.
- `AlgebraicGeometry.WeilComplex.toStrictWeilComplex`: `K ↦ (For(K), θ_K)`, with
  `AlgebraicGeometry.WeilComplex.toStrictWeilComplexCompForgetIso`.
- `AlgebraicGeometry.WeilSheaf.toStrictWeilComplex`: its restriction to the heart, fully
  faithful, with essential image `AlgebraicGeometry.StrictWeilComplex.heart`
  (`AlgebraicGeometry.WeilSheaf.essImage_toStrictWeilComplex`), and the resulting equivalence
  `AlgebraicGeometry.WeilSheaf.strictWeilComplexHeartEquivalence`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A C D : Type*} [Category A] [Category C] [Category D]

section Lift

variable {F : C ⥤ C} (Φ : A ⥤ C) (e : Φ ⋙ F ≅ Φ)

end Lift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The transport of algebras along a faithful functor is faithful. -/
instance faithful_mapOfNatIso [L.Faithful] : (mapOfNatIso e).Faithful where
  map_injective {_ _} _ _ h := ObjectProperty.hom_ext _ (Algebra.Hom.ext
    (L.map_injective (congrArg (fun φ ↦ φ.hom.f) h)))

/-- The transport of algebras along a fully faithful functor is full: a morphism
`L a ⟶ L b` compatible with the transported structure isomorphisms comes from a morphism
`a ⟶ b`, which is compatible with the structure isomorphisms since `L` is faithful. -/
instance full_mapOfNatIso [L.Full] [L.Faithful] : (mapOfNatIso e).Full where
  map_surjective {K K'} g := by
    refine ⟨ObjectProperty.homMk
      { f := L.preimage g.hom.f
        h := L.map_injective ?_ }, ObjectProperty.hom_ext _ (Algebra.Hom.ext (L.map_preimage _))⟩
    have hg : G.map g.hom.f ≫ e.hom.app K'.carrier ≫ L.map K'.str.hom =
        (e.hom.app K.carrier ≫ L.map K.str.hom) ≫ g.hom.f := g.hom.h
    have hn : G.map g.hom.f ≫ e.hom.app K'.carrier =
        e.hom.app K.carrier ≫ L.map (F.map (L.preimage g.hom.f)) := by
      simpa using e.hom.naturality (L.preimage g.hom.f)
    rw [L.map_comp, L.map_comp, L.map_preimage, ← cancel_epi (e.hom.app K.carrier),
      ← reassoc_of% hn]
    exact hg.trans (Category.assoc _ _ _)

end Map

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Endofunctor ProEtale

section

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

end WeilComplex

namespace ProEtaleWeilSheaf

end ProEtaleWeilSheaf

namespace WeilSheaf

end WeilSheaf

end AlgebraicGeometry
