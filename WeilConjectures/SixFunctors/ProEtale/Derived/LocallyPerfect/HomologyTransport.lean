/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.SixFunctors.ProEtale.Derived.LocallyPerfect.Defs

/-!
# Cycles and cohomology sheaves of pulled back complexes

Let `g : Z ⟶ Y` be a morphism of schemes. The pullback `g^*` of pro-étale sheaves of modules is
exact, so for a complex `L` of pro-étale sheaves on `Y` the cycles and the cohomology sheaves of
`g^* L` are the pullbacks of those of `L`. This file records these identifications and their
compatibilities with `toCycles`, `homologyπ` and the maps induced by chain maps.

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarCyclesIso`: `Z^i(g^* L) ≅ g^* Z^i(L)`.
- `AlgebraicGeometry.ProEtale.upperStarHomologyIso`: `H^i(g^* L) ≅ g^* H^i(L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ] {Y Z : Scheme.{u}} (g : Z ⟶ Y)
  (L : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ) (i : ℤ)

/-- The cycles of a pulled back complex are the pullback of the cycles. -/
noncomputable def upperStarCyclesIso :
    (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj L).cycles i ≅
      (g)^*[ModuleCat.{u + 1} Λ].obj (L.cycles i) :=
  (L.sc i).mapCyclesIso (g)^*[ModuleCat.{u + 1} Λ]

/-- The cohomology sheaves of a pulled back complex are the pullbacks of the cohomology
sheaves. -/
noncomputable def upperStarHomologyIso :
    (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj L).homology i ≅
      (g)^*[ModuleCat.{u + 1} Λ].obj (L.homology i) :=
  (L.sc i).mapHomologyIso (g)^*[ModuleCat.{u + 1} Λ]

@[reassoc (attr := simp)]
lemma upperStarCyclesIso_hom_iCycles :
    (upperStarCyclesIso g L i).hom ≫ (g)^*[ModuleCat.{u + 1} Λ].map (L.iCycles i) =
      (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj L).iCycles i :=
  (L.sc i).mapCyclesIso_hom_iCycles _

@[reassoc (attr := simp)]
lemma toCycles_upperStarCyclesIso_hom (j : ℤ) :
    (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj L).toCycles j i ≫
        (upperStarCyclesIso g L i).hom =
      (g)^*[ModuleCat.{u + 1} Λ].map (L.toCycles j i) := by
  have : Mono ((g)^*[ModuleCat.{u + 1} Λ].map (L.iCycles i)) := by
    rw [← (L.sc i).mapCyclesIso_hom_iCycles]
    infer_instance
  rw [← cancel_mono ((g)^*[ModuleCat.{u + 1} Λ].map (L.iCycles i)), Category.assoc,
    upperStarCyclesIso_hom_iCycles, HomologicalComplex.toCycles_i, ← Functor.map_comp,
    HomologicalComplex.toCycles_i]
  rfl

@[reassoc]
lemma homologyπ_upperStarHomologyIso_hom :
    (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).obj L).homologyπ i ≫
        (upperStarHomologyIso g L i).hom =
      (upperStarCyclesIso g L i).hom ≫ (g)^*[ModuleCat.{u + 1} Λ].map (L.homologyπ i) :=
  (L.sc i).homologyπ_mapHomologyIso_hom _

variable {L} in
@[reassoc]
lemma cyclesMap_upperStarCyclesIso_hom
    {L' : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ}
    (φ : L ⟶ L') :
    HomologicalComplex.cyclesMap (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex (.up ℤ)).map
        φ) i ≫ (upperStarCyclesIso g L' i).hom =
      (upperStarCyclesIso g L i).hom ≫
        (g)^*[ModuleCat.{u + 1} Λ].map (HomologicalComplex.cyclesMap φ i) :=
  ShortComplex.mapCyclesIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map φ) _

variable {L} in
@[reassoc]
lemma homologyMap_upperStarHomologyIso_hom
    {L' : CochainComplex (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ℤ}
    (φ : L ⟶ L') :
    HomologicalComplex.homologyMap (((g)^*[ModuleCat.{u + 1} Λ].mapHomologicalComplex
        (.up ℤ)).map φ) i ≫ (upperStarHomologyIso g L' i).hom =
      (upperStarHomologyIso g L i).hom ≫
        (g)^*[ModuleCat.{u + 1} Λ].map (HomologicalComplex.homologyMap φ i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map φ) _

end AlgebraicGeometry.ProEtale
