module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/-- Epimorphic images of finite type sheaves are finite type.
Source: Stacks Project, Modules, Lemma 01B7 (blueprint: lem-weil-pbc-sheaf-finite-type-epi-image).
The proof is the local-generator argument from Lemma 01B7. On each open neighbourhood
where finitely many sections generate `A`, their images generate `B`: for a section of
`B`, use the epimorphism to lift it locally to `A`, then express each lift locally as a
linear combination of the chosen generators. Refining the two coverings gives a finite
generating family for `B` around every point, which is exactly `B.IsFiniteType`. The
same argument applies on the restricted open sites used for relation kernels. -/
theorem sheaf_finiteType_of_epi
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    {A B : SheafOfModules.{u} R} (e : A ⟶ B) [Epi e] :
    A.IsFiniteType → B.IsFiniteType := by
  sorry

end
