module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.CategoryTheory.Functor.OfSequence

import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Canonical sequential DG colimit triangles

Source: Stacks Project, dga.tex, Tags 09QI and 0CRL, lemma-derived-products and
lemma-homotopy-colimit (blueprint: lem-sfb-dg-sequential-colimit-triangle).

Degreewise universal properties specify the actual DG direct sums and colimits.
The telescope uses the chosen derived coproduct and retains its canonical legs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.DgAlgebra

/-- Every small family has a degreewise DG direct sum whose actual inclusions
exhibit its image as a coproduct in the derived category, including the empty sum.
Source: Stacks Project, dga.tex, Tag 09QI, clauses (1) and (2)
(blueprint: lem-sfb-dg-sequential-colimit-triangle).

Proof: cohomology commutes with degreewise sums and products by taking cycles,
boundaries and primitives coordinatewise (finite support for sums). Resolve each
module by a semi-free module using lem-coef-dg-module-semi-free-replacement.
By lem-coef-dg-semi-free-homotopically-projective each resolution is homotopically
projective. Maps from their sum form the product of their Hom complexes, so the
sum is also homotopically projective. Its map to the original sum is a
quasi-isomorphism. Lem-sfb-dg-homotopically-projective-hom-derived computes derived
maps from these resolutions by degree-zero Hom cohomology. Commutation with
products gives precisely the coproduct universal property, with restriction along
the actual summand inclusions. -/
theorem exists_degreewise_coproduct_derived
    (A : Algebra.{u}) [DerivedStructure A] (I : Type u) (M : I → RightModule A) :
    ∃ B : Cofan M,
      (∀ n : ℤ, Nonempty (IsColimit
        (((underlying A) ⋙ HomologicalComplex.eval
          (ModuleCat.{u} (ULift.{u} ℤ)) (ComplexShape.up ℤ) n).mapCocone B))) ∧
      Nonempty (IsColimit ((Q A).mapCocone B)) := by
  sorry

/-- The sequential DG colimit exists and is computed on each component module.
Source: Stacks Project, dga.tex, Tag 0CRL, and derived.tex, Tag 093W
(blueprint: lem-sfb-dg-sequential-colimit-triangle).

Proof: take the quotient of the degreewise direct sum by the relations identifying
a summand element with its image in the next summand. Differential and right action
preserve these relations, so descend to the quotient. A map out of the quotient
is precisely a family compatible with successive transitions, hence with all
transitions. This gives the required degreewise colimit, with its induced
DG structure and canonical maps. No injectivity is used. -/
theorem exists_degreewise_sequential_colimit
    (A : Algebra.{u}) (E : ℕ ⥤ RightModule A) :
    ∃ c : Cocone E, ∀ n : ℤ, Nonempty (IsColimit
      (((underlying A) ⋙ HomologicalComplex.eval
        (ModuleCat.{u} (ULift.{u} ℤ)) (ComplexShape.up ℤ) n).mapCocone c)) := by
  sorry

/-- Any degreewise sequential DG colimit has the telescope triangle with the
canonical colimit legs, and is a sequential homotopy colimit.
Source: Stacks Project, dga.tex, Tag 0CRL, using Tag 09QI
(blueprint: lem-sfb-dg-sequential-colimit-triangle).

Proof:
1. Degreewise cohomology commutes with sums and products by the coordinate argument
in exists_degreewise_coproduct_derived. That result identifies DG sums and their
actual inclusions with derived coproducts, by semi-free replacements and the
homotopically-projective Hom comparison (the three proof nodes cited there).
2. On B = direct sum E_m define f on summand m as inclusion_m minus inclusion_(m+1)
after v_m. Define j by the colimit maps. Compatibility gives j f = 0. Degreewise,
f(x)=0 forces x_0=0 and then x_m=v_(m-1)(x_(m-1))=0 by induction, without assuming
any v_m injective. The cokernel relations give exactly the degreewise colimit.
3. Thus 0 -> B -> B -> c.pt -> 0 is degreewise exact. The DG cone C(f) has
componentwise action and differential (y,x) |-> (d y + f x,-d x). The map
C(f) -> c.pt is j on B and zero on B[1]; it preserves the action and differential.
Lem-pc-cone-short-exact-quasi-iso makes it a quasi-isomorphism on underlying
complexes, hence it is inverted in the DG derived category.
4. Transport the distinguished mapping-cone triangle through this isomorphism.
Its first two legs are f and j because the cone-to-colimit map composed with
the cone inclusion is j already as DG maps. Identify B with the chosen derived
coproduct by its canonical inclusions. This gives the stated first map and every
canonical-leg equation, and witnesses def-kun-truncations. -/
theorem sequential_colimit_triangle
    (A : Algebra.{u}) [DerivedStructure A] (E : ℕ ⥤ RightModule A)
    (c : Cocone E)
    (hc : ∀ n : ℤ, Nonempty (IsColimit
      (((underlying A) ⋙ HomologicalComplex.eval
        (ModuleCat.{u} (ULift.{u} ℤ)) (ComplexShape.up ℤ) n).mapCocone c))) :
    (∃ (j : (∐ (fun m : ℕ ↦ (Q A).obj (E.obj m))) ⟶ (Q A).obj c.pt)
        (δ : (Q A).obj c.pt ⟶ (∐ (fun m : ℕ ↦ (Q A).obj (E.obj m)))⟦(1 : ℤ)⟧),
      (∀ m : ℕ, Sigma.ι (fun k : ℕ ↦ (Q A).obj (E.obj k)) m ≫ j =
        (Q A).map (c.ι.app m)) ∧
      Triangle.mk
        (𝟙 _ - Sigma.desc (fun m : ℕ ↦
          (Q A).map (E.map (homOfLE (Nat.le_succ m))) ≫
            Sigma.ι (fun k : ℕ ↦ (Q A).obj (E.obj k)) (m + 1))) j δ ∈
        distTriang (Derived A)) ∧
      IsSequentialHomotopyColimit (fun m : ℕ ↦ (Q A).obj (E.obj m))
        (fun m : ℕ ↦ (Q A).map (E.map (homOfLE (Nat.le_succ m)))) ((Q A).obj c.pt) := by
  sorry

end CategoryTheory.DgAlgebra
