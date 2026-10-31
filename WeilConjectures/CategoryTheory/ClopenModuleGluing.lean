/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ClopenSheafPartition
public import WeilConjectures.CategoryTheory.RingedSheafSliceConstruction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.DerivedCechImageTotalization
import WeilConjectures.CategoryTheory.ElementSiteDescent
import WeilConjectures.CategoryTheory.Sites.SmallSheafCoproductLabels
import Mathlib.CategoryTheory.Equivalence

/-!
# Clopen gluing for modules on a ringed site

Source: the finite clopen module transport in the proof of the Weil mixedness theorem
(blueprint: lem-zl-real-arbitrary-ring-clopen-gluing).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [instance] cechImage_elementPullback_additive

/-- Modules over an arbitrary ring sheaf glue across a finite clopen partition.

The equivalence has the canonical restriction functor. Its inverse is both the product and
coproduct of the canonical extensions by zero. The equivalence's unit and counit are natural
isomorphisms. Kernels, cokernels and exact short complexes are detected on the pieces.

Source: blueprint `sec-deligne-laumon-general/sk-i-dl-general-real/
thm-zl-real-mixed-by-curves.proof.md`, paragraph 5; Stacks Project, Tags 0791 and 04TS
(blueprint: lem-zl-real-arbitrary-ring-clopen-gluing).

Proof:
1. Present each open piece by the element site of its subterminal sheaf. The partition cover
   gives a covering by labelled sections. Distinct labels can coexist only on an empty-covered
   object, where all module sheaves have a singleton section set (Tags 0791, 00WK).
2. For a tuple of modules, take compatible families indexed by (i, W → V, u ∈ U_i(W)).
   Addition, scalar action, restriction and maps are coordinatewise. The sheaf axiom on each
   element site glues such families uniquely over a covering of V (Tag 04TR).
3. On the jth element site, evaluation at (j, id, u_j) is an isomorphism: subterminality
   determines all j-coordinates and empty-covered overlaps force all other coordinates zero.
4. Send a global section to all its restrictions. Invert this map by gluing on a labelled
   covering; equal labels agree by compatibility and unequal labels on overlaps agree because
   those overlaps are empty-covered. Separatedness proves independence of the covering.
5. These section isomorphisms are natural and linear. Restricting and then evaluating is the
   identity, so both triangle identities hold and give the stated additive equivalence.
6. Extension of a module from one piece is the tuple supported in that coordinate: its Hom
   functor is left adjoint to restriction and its other restrictions vanish. The tuple has both
   product and coproduct universal properties for these single-coordinate objects; transport
   them through the equivalence to obtain the displayed limiting fan and colimiting cofan.
7. Kernels and cokernels in a product category have their universal properties coordinatewise.
   Equivalences preserve and reflect these properties, hence preserve finite limits and
   colimits and detect exactness. Cokernels here are sheaf cokernels, not presheaf cokernels.
8. An initial piece has only empty-covered element objects, hence only zero module sheaves.
   If the index is empty, the cover forces every site object to be empty-covered, and both
   categories are terminal. The construction also allows the zero ring and noncommutative rings.
-/
theorem clopen_module_gluing
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (I : Type w)
    (P : ClopenSheafPartition (J := J) I) :
    ∃ E : ringedSiteModules.{u} R ≌
        (∀ i : I, ringedSiteModules.{u} (elementRing R (P.pieces i))),
      E.functor = Functor.pi' (fun i ↦ elementModulePullback R (P.pieces i)) ∧
      (∀ (M N : ringedSiteModules.{u} R) (f g : M ⟶ N) (i : I),
        (E.functor.map (f + g)) i = (E.functor.map f) i + (E.functor.map g) i) ∧
      (∀ (M N : ∀ i : I, ringedSiteModules.{u} (elementRing R (P.pieces i)))
        (f g : M ⟶ N), E.inverse.map (fun i ↦ f i + g i) =
          E.inverse.map f + E.inverse.map g) ∧
      PreservesFiniteLimits E.functor ∧ PreservesFiniteColimits E.functor ∧
      PreservesFiniteLimits E.inverse ∧ PreservesFiniteColimits E.inverse ∧
      (∀ M : ∀ i : I, ringedSiteModules.{u} (elementRing R (P.pieces i)),
        ∃ (p : ∀ i : I, E.inverse.obj M ⟶
            (elementModuleExtension R (P.pieces i)).obj (M i))
          (q : ∀ i : I, (elementModuleExtension R (P.pieces i)).obj (M i) ⟶
            E.inverse.obj M),
          Nonempty (IsLimit (Fan.mk (E.inverse.obj M) p)) ∧
          Nonempty (IsColimit (Cofan.mk (E.inverse.obj M) q))) ∧
      (∀ (M N : ringedSiteModules.{u} R) (f : M ⟶ N) (c : KernelFork f),
        Nonempty (IsLimit c) ↔
          ∀ i : I, Nonempty (IsLimit ((elementModulePullback R (P.pieces i)).mapCone c))) ∧
      (∀ (M N : ringedSiteModules.{u} R) (f : M ⟶ N) (c : CokernelCofork f),
        Nonempty (IsColimit c) ↔
          ∀ i : I, Nonempty (IsColimit
            ((elementModulePullback R (P.pieces i)).mapCocone c))) ∧
      (∀ S : ShortComplex (ringedSiteModules.{u} R),
        S.Exact ↔ ∀ i : I, (S.map (elementModulePullback R (P.pieces i))).Exact) := by
  sorry

end CategoryTheory
end
