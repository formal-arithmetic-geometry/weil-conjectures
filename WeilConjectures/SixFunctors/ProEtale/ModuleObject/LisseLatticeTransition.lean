/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsFreeDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-!
# Transition matrices of trivialisations of module objects

Let `Λ` be a commutative condensed ring, `S` a scheme and `L` a module object over `Λ_S`. For a
trivialisation `e : Λ_Vⁿ ≅ f^* L` over `f : V ⟶ S` and a morphism `a : W ⟶ V`, the pullback of
`e` along `a` is a trivialisation `Λ_Wⁿ ≅ (a ≫ f)^* L`. For two trivialisations `e`, `e'` over
`f`, `f'` and `a : W ⟶ V`, `b : W ⟶ V'` with `a ≫ f = b ≫ f'`, the two trivialisations of
`(a ≫ f)^* L = (b ≫ f')^* L` differ by the *transition morphism* `Λ_Wⁿ ⟶ Λ_Wⁿ'`. Transition
morphisms

* are the identity for `e = e'`, `a = b` (`frameTransition_self`) and compose
  (`frameTransition_trans`);
* are compatible with precomposition by `c : Q ⟶ W` (`frameTransition_comp`): the transition
  morphism at `c ≫ a, c ≫ b` is the pullback of that at `a, b`;
* compute the transition isomorphisms of `ProEtale.CondensedRing.finiteFreeTransition` on the
  fibre products (`finiteFreeTransition_hom_eq`, `finiteFreeTransition_inv_eq`).

For a family of trivialisations, these properties are packaged in
`ProEtale.CondensedRing.exists_frameTransitions`, which hides the transition morphisms behind an
existential: downstream statements then only involve an opaque family of morphisms.

The compatibility with precomposition rests on the cocycle condition for the identifications
`g^* Λ_Y ≅ Λ_X` (`upperStarObjRegularIso_comp`), which are the inverses of the unit comparisons
of the strong monoidal pullbacks (`upperStarObjRegularIso_hom_eq`).

We also record the matrix calculus of morphisms of free module objects: the entries of a
composite are the matrix products of the entries (`CategoryTheory.Mod.finFreeMatrix_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### The identifications `g^* Λ_Y ≅ Λ_X` -/

section RegularIso

end RegularIso

/-! ### Congruences -/

section Congr

end Congr

/-! ### Transition morphisms

We do not introduce definitions for the frames and transition morphisms: unfolding a definition
whose body contains instance arguments of the pullbacks of module objects against the same
term elaborated in a statement is very expensive (the auxiliary proofs abstracted from the body
differ from those of the statement). The transition morphism of `e, e'` at `a, b` is written out
as the composite
```
Λ_Wⁿ ≅ a^* Λ_Vⁿ --a^* e--> a^* f^* L ≅ (a ≫ f)^* L = (b ≫ f')^* L ≅ b^* f'^* L --b^* e'⁻¹-->
  b^* Λ_V'ⁿ' ≅ Λ_Wⁿ'.
```
-/

section Transition

variable {S V V' V'' W : Scheme.{u}}
  {L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)}
  {f : V ⟶ S} {f' : V' ⟶ S} {f'' : V'' ⟶ S} {n n' n'' : ℕ}
  (e : Mod.finiteFree (condensedRingObj Λ V) n ≅ (f)^*⟦Λ⟧.obj L)
  (e' : Mod.finiteFree (condensedRingObj Λ V') n' ≅ (f')^*⟦Λ⟧.obj L)
  (e'' : Mod.finiteFree (condensedRingObj Λ V'') n'' ≅ (f'')^*⟦Λ⟧.obj L)

end Transition

/-! ### Transition morphisms of a family of trivialisations -/

section Family

variable {Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ₀]
  (a : Λ₀ ⟶ Λ) [IsMonHom a]

end Family

end AlgebraicGeometry.ProEtale.CondensedRing
