module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/-- Restriction to an over-site preserves epimorphisms.
Source: Stacks Project, Modules, Lemma 01BY, local lifting argument.
An epimorphism of sheaves is locally surjective; pulling a local lift back along
an object of the over-site gives the same local lift there. We apply the
locally-surjective characterization of epimorphisms on the over-site, after
pulling back the covering and lift. (blueprint: lem-stage3-epi-over-functor) -/
theorem epi_overFunctor_map
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A B : SheafOfModules.{u} R} (e : A ⟶ B) [Epi e] (U : C) :
    Epi ((SheafOfModules.overFunctor R U).map e) := by
  sorry

end
