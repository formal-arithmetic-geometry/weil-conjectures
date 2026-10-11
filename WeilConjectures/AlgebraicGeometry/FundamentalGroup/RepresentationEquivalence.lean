/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representation
public import WeilConjectures.CategoryTheory.Sites.Point.FreeYoneda

/-!
# The Galois correspondence for finite locally constant sheaves of modules

Let `Y` be a connected scheme with a geometric point `s`, let `G = π₁(Y, s)` be a fundamental
group of the fibre functor at `s` and let `Λ` be a finite ring. The geometric stalk at `s` is an
equivalence between finite locally constant sheaves of `Λ`-modules on the small étale site of
`Y` and finite `Λ`-modules with a continuous `G`-action.

## Strategy

For a finite étale `Y`-scheme `P`, the free sheaf `Λ[P]` is finite locally constant, with stalk
the permutation representation `Λ[P_s]`. Morphisms out of `Λ[P]` correspond to sections over
`P`, i.e. to morphisms of sheaves of sets out of `Hom_Y(-, P)`, and these correspond to
`G`-equivariant maps out of `P_s`: so the stalk functor is bijective on morphisms out of free
sheaves. Every finite locally constant sheaf of modules `F` is a quotient of a free sheaf
`Λ[P]` (take `P` representing the underlying sheaf of sets of `F`), with finite locally constant
kernel; together with the faithfulness of the stalk functor this gives full faithfulness.
Every finite continuous representation `V` is the cokernel of a map `Λ[K] ⟶ Λ[V]` of permutation
representations, which comes from a map of free sheaves; its cokernel is a finite locally
constant sheaf with stalk `V`, as the stalk functor is right exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstantModule

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

variable (Λ) in
/-- The free sheaf `Λ[P]` on a finite étale `Y`-scheme `P`, a finite locally constant sheaf of
`Λ`-modules. -/
noncomputable def free (P : Y.FiniteEtale) : Y.FiniteLocallyConstantModule Λ :=
  ⟨Sheaf.freeYoneda Y.smallEtaleTopology P.obj (ModuleCat.of Λ Λ),
    have : IsFinite P.obj.hom := P.property
    Etale.isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite P.obj⟩

variable (Λ) in
/-- The generating section of `Λ[P]` over `P`, as a morphism of sheaves of sets
`Hom_Y(-, P) ⟶ Λ[P]`. -/
noncomputable def unit (P : Y.FiniteEtale) :
    (FiniteEtale.toFiniteLocallyConstant Y).obj P ⟶ (forget Y Λ).obj (free Λ P) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    (uliftYonedaEquiv.symm
      (GrothendieckTopology.Point.sheafFreeYonedaGen (J := Y.smallEtaleTopology) Λ P.obj)))

end AlgebraicGeometry.Scheme.FiniteLocallyConstantModule
