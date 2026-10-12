module

public import Sheaf.Topology.RingedSpaceModuleEnoughInjectives
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme

attribute [local instance] Abelian.hasFiniteBiproducts

open Classical in
/-- A given, possibly large coproduct of module sheaves has a small directed presentation
by finite biproducts of its summands, with the original inclusions as component maps.

Source: Stacks Project, Modules, Tag 01AH; Cohomology, Tag 09J7, the finite-subsum
presentation used in the proof. The universe reduction is the smallness argument in
`lem-weil-pbc-qcqs-cohomology-finite-subsum-representatives`.
(blueprint: lem-weil-pbc-module-coproduct-small-subsum-diagram).

Proof: Let N be the subtype of indices i for which F i is not a zero object. Each such
sheaf has an open U_i and a nonzero section s_i: if all its section modules were zero,
its identity would be zero, making the sheaf a zero object. The coproduct universal
property gives a projection S to F i, identity on component i and zero on every other
component. Thus the image of s_i under the given inclusion is nonzero. The assignment
of i to (U_i, iota_i(s_i)) is injective into the disjoint union of section sets of S over
all opens: equality for distinct i and k contradicts projection to F i. That union is
u-small, hence N is equivalent to a type B in Type u. Discarding the zero components
preserves the coproduct universal property, since maps out of them are unique.
Index by Finset B, including the empty set. The finite stages are the biproducts of
F at the corresponding original indices. Transition maps are defined by sending each
inclusion to its matching inclusion in the larger stage; the coproduct universal
property verifies the identity and composition laws. Union gives directedness and the
empty set gives nonemptiness. A compatible cocone on the finite stages is exactly a
family of maps on the nonzero summands, so S, with the original inclusions on each
component, is its colimit (also Mathlib's finite-subcoproduct colimit construction).
For each finite subset of B take its finite image J in I. The equivalence between its
indices and J induces a biproduct isomorphism e from the stage to the biproduct over J.
Its inverse followed by the cocone leg has component iota_j by construction. These
isomorphisms are genuine finite-biproduct constructions. No cohomology, compactness or
quasi-separatedness is used. If N is empty there is just the zero stage, as required. -/
theorem exists_small_finiteSubsum_diagram (X : Scheme.{u}) (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (hS : IsColimit (Cofan.mk S ι)) :
    ∃ (A : Type u) (_ : Preorder A) (_ : Nonempty A) (_ : IsDirected A (· ≤ ·))
      (D : A ⥤ SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (τ : D ⟶ (Functor.const A).obj S) (_ : IsColimit (Cocone.mk S τ)),
      ∀ a : A, ∃ (J : Finset I) (e : D.obj a ≅ ⨁ (fun j : J ↦ F j)),
        ∀ j : J, biproduct.ι (fun j : J ↦ F j) j ≫ e.inv ≫ τ.app a = ι j := by
  sorry

end AlgebraicGeometry.Scheme
