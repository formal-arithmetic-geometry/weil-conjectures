module

public import Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

/-- The shifted section Hom-complex comparison in the homotopy category is natural.
Source: Stacks Project, Tag 0A8Y, Equation (21.34.0.1).
(blueprint: lem-pur-hom-complex-sections-homotopy-naturality)

Proof: evaluate the product projections of the sheaf Hom complex at U. Sections
in degree n are families of maps L^p|U to I^(p+n)|U. The differential formula
identifies cycles with chain maps into the shifted target, whose differential
is (-1)^n times the original differential. Multiply a family in degree n-1
by (-1)^n to identify its differential with a null-homotopy into that target.
Quotienting gives a bijection between homology classes
and homotopy classes, since both quotient projections are surjective. Apply
this construction to (L,I') and (L',I), obtaining a and b. Componentwise
composition sends a family f to s f t; the homotopy sign correction depends
only on n and hence commutes with both maps. This proves the displayed equality
on cycles and then on all homology classes. No K-injectivity or localization
at quasi-isomorphisms is used. Degree zero recovers the unshifted comparison;
zero complexes give singleton Hom sets; unbounded complexes use products. -/
theorem homComplex_sections_homotopy_naturality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) (n : ℤ) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let E := (SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := module_overFunctor_preservesZero R₀ U
    let res := (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let Q := HomotopyCategory.quotient (SheafOfModules.{max u v} (R₀.over U))
      (ComplexShape.up ℤ)
    let f := E.map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)
    ∃ a : (E.obj (homComplex (R := R) L I')).homology n ≃
        (Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧)),
      ∃ b : (E.obj (homComplex (R := R) L' I)).homology n ≃
          (Q.obj (res.obj L') ⟶ Q.obj ((res.obj I)⟦n⟧)),
        ∀ x, b (HomologicalComplex.homologyMap f n x) =
          Q.map (res.map t) ≫ a x ≫ Q.map ((shiftFunctor _ n).map (res.map s)) := by
  sorry

end CategoryTheory
