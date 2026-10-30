/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Continuity of `Hom` out of a bounded constructible `E`-complex

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, a topologically noetherian scheme `X` and a bounded
constructible complex `C ∈ Dᵇc(X)⟦E̲⟧`, morphisms in `D(X_proét, E)` from `C` to a filtered
colimit `K = colim_j K_j` of complexes of `E_X`-modules which all vanish below a fixed degree are
the filtered colimit of the morphisms `C ⟶ K_j`, in every shift
(`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj`, blueprint
`sk-lem-constructible-ext-continuity` (1)).

## Sorried input

`ProEtale.CondensedRing.constructibleExtContinuity_continuousMapRingObj` states the blueprint node
`sk-lem-constructible-ext-continuity` (1) of the subsection `sk-lem-constructible-ext-continuity`;
it is proved there. The proof reduces, by dévissage along the generation of `Dᵇc(X, E)` by the
extensions by zero `a_! L` of lisse sheaves (`sk-cor-coefficient-heart-ii`), to the continuity of
pro-étale cohomology on quasi-compact quasi-separated objects (`sk-cor-pe-bounded-continuity`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Blueprint `sk-lem-constructible-ext-continuity` (1), for the coefficient ring `E̲` of a finite
subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (to be proved in the subsection
`sk-lem-constructible-ext-continuity`). Let `X` be a topologically noetherian scheme,
`C ∈ Dᵇc(X, E)`, and `K = colim_j K_j` a filtered colimit of complexes of `E_X`-modules all of
which vanish below a fixed degree `a`. Then for every `q ∈ ℤ`, the natural map
`colim_j Hom(C, K_j[q]) ⟶ Hom(C, K[q])` is bijective:

* every morphism `C ⟶ K[q]` factors through some `K_j[q]`;
* two morphisms `C ⟶ K_j[q]` with the same image in `Hom(C, K[q])` agree in some
  `Hom(C, K_{j'}[q])`. -/
theorem constructibleExtContinuity_continuousMapRingObj [TopologicalSpace.NoetherianSpace X]
    (C : Dᵇc(X)⟦Profinite.continuousMapRingObj E⟧) {J : Type} [SmallCategory J] [IsFiltered J]
    (K : J ⥤ CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) ℤ)
    (a : ℤ) (hK : ∀ j, (K.obj j).IsStrictlyGE a) (c : Cocone K) (hc : IsColimit c) (q : ℤ) :
    (∀ f : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj c.pt),
      ∃ (j : J) (g : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj (K.obj j))),
        f = g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j))) ∧
    (∀ (j : J) (g g' : C.obj ⟶ (shiftFunctor _ q).obj (DerivedCategory.Q.obj (K.obj j))),
      g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j)) =
          g' ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (c.ι.app j)) →
        ∃ (j' : J) (t : j ⟶ j'),
          g ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (K.map t)) =
            g' ≫ (shiftFunctor _ q).map (DerivedCategory.Q.map (K.map t))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
