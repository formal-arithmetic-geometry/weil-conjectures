/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.Topology.BasisSheafCofinalCoverings
import Sheaf.Topology.SheafOnBasisExtends

/-!
# Extending modules from a basis

Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.Opens

/-- A module presheaf on an intersection-closed basis with finite refinements and finite
unique gluing extends to a sheaf of modules, with its universal property and basis stalks.
Source: Stacks Project, Sheaves on Spaces, Section 009H, Tags 009L, 009N, 009T and 009U.
(blueprint: lem-weil-pbc-sheaf-of-modules-from-basis).

Proof:
1. Finite basis coverings form a cofinal system of coverings by the finite-refinement
   hypothesis. Apply `lem-weil-pbc-basis-sheaf-cofinal-coverings` (009L) to obtain gluing
   for all basis coverings, including the empty covering.
2. Apply `lem-weil-pbc-sheaf-on-basis-extends` (009N and 009Q) to the underlying abelian
   presheaf to obtain the abelian sheaf and restriction-compatible additive identifications.
3. Transport scalar multiplication on basis opens along those identifications. Extend the
   resulting map from the product of the ring presheaf and the abelian sheaf into the sheaf
   using `lem-weil-pbc-sheaf-morphism-on-basis`. Each module axiom is an equality of maps
   into a sheaf, true on the basis, hence everywhere by the same lemma. Naturality gives
   semilinearity of restrictions, and the identifications are linear (009T).
4. Extend each compatible family of linear maps by the morphism-extension lemma. Compare
   the two scalar-action maps on the basis to obtain linearity globally. Uniqueness follows
   from uniqueness for abelian sheaves. Basiswise bijectivity implies an isomorphism; its
   inverse is linear. Apply this to the inverse identifications of another extension to
   obtain uniqueness up to unique isomorphism (009U).
5. By `lem-weil-pbc-stalk-germs-on-basis`, every stalk element has a basis representative,
   and equal representatives agree after a basis restriction. Thus compatible additive
   maps on basis neighbourhoods descend uniquely to the stalk. Addition is checked on a
   common basis neighbourhood. The germ scalar formula from `def-weil-pbc-module-stalk`
   identifies the module action with the action on this colimit. -/
theorem exists_sheafOfModules_from_basis
    (X : TopCat.{u}) (B : Set (Opens X)) (hB : IsBasis B)
    (hcap : ∀ U V : B, U.val ⊓ V.val ∈ B)
    (hrefine : ∀ (U : B) (C : Set B),
      (∀ V ∈ C, V.val ≤ U.val) → (⨆ V ∈ C, V.val) = U.val →
      ∃ (n : ℕ) (W : Fin n → B), (⨆ i, (W i).val) = U.val ∧
        ∀ i, ∃ V ∈ C, (W i).val ≤ V.val)
    (R : TopCat.Sheaf RingCat.{u} X)
    (F : ∀ U : B, ModuleCat.{u} (R.obj.obj (op U.val)))
    (r : ∀ (U V : B), V.val ≤ U.val → F U →+ F V)
    (rid : ∀ (U : B) (s : F U), r U U le_rfl s = s)
    (rcomp : ∀ (U V W : B) (hVU : V.val ≤ U.val) (hWV : W.val ≤ V.val) (s : F U),
      r V W hWV (r U V hVU s) = r U W (hWV.trans hVU) s)
    (rsmul : ∀ (U V : B) (h : V.val ≤ U.val) (a : R.obj.obj (op U.val)) (s : F U),
      r U V h (a • s) = R.obj.map (homOfLE h).op a • r U V h s)
    (hglue : ∀ (U : B) (n : ℕ) (V : Fin n → B) (hV : ∀ i, (V i).val ≤ U.val),
      (⨆ i, (V i).val) = U.val → ∀ s : ∀ i, F (V i),
      (∀ i j,
        r (V i) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_left (s i) =
        r (V j) ⟨(V i).val ⊓ (V j).val, hcap (V i) (V j)⟩ inf_le_right (s j)) →
      ∃! t : F U, ∀ i, r U (V i) (hV i) t = s i) :
    ∃ (E : SheafOfModules.{u} R)
      (ι : ∀ U : B, E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
      (∀ (U V : B) (h : V.val ≤ U.val) (t : E.val.obj (op U.val)),
        ι V (E.val.map (homOfLE h).op t) = r U V h (ι U t)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (ψ : ∀ U : B, F U →ₗ[R.obj.obj (op U.val)] G.val.obj (op U.val)),
        (∀ (U V : B) (h : V.val ≤ U.val) (s : F U),
          ψ V (r U V h s) = G.val.map (homOfLE h).op (ψ U s)) →
        (∃! Ψ : E ⟶ G, ∀ (U : B) (t : E.val.obj (op U.val)),
          Ψ.val.app (op U.val) t = ψ U (ι U t)) ∧
        (∀ (Ψ : E ⟶ G),
          (∀ (U : B) (t : E.val.obj (op U.val)),
            Ψ.val.app (op U.val) t = ψ U (ι U t)) →
          (∀ U : B, Function.Bijective (ψ U)) → IsIso Ψ)) ∧
      (∀ (G : SheafOfModules.{u} R)
        (j : ∀ U : B, G.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)] F U),
        (∀ (U V : B) (h : V.val ≤ U.val) (t : G.val.obj (op U.val)),
          j V (G.val.map (homOfLE h).op t) = r U V h (j U t)) →
        ∃! e : E ≅ G, ∀ (U : B) (t : E.val.obj (op U.val)),
          j U (e.hom.val.app (op U.val) t) = ι U t) ∧
      (∀ (x : X) (A : AddCommGrpCat.{u})
        (φ : ∀ U : {U : B // x ∈ U.val}, F U.val →+ A),
        (∀ (U V : {U : B // x ∈ U.val}) (h : V.val.val ≤ U.val.val) (s : F U.val),
          φ V (r U.val V.val h s) = φ U s) →
        ∃! f : PresheafOfModules.stalkObj R.obj x E.val →+ A,
          ∀ (U : {U : B // x ∈ U.val}) (s : F U.val),
            f ((TopCat.Presheaf.germ (X := X) E.val.presheaf U.val.val x U.property).hom
              ((ι U.val).symm s)) = φ U s) ∧
      (∀ (x : X) (U : B) (hx : x ∈ U.val) (a : R.obj.obj (op U.val)) (s : F U),
        (TopCat.Presheaf.germ (X := X) E.val.presheaf U.val x hx).hom
          ((ι U).symm (a • s)) =
          TopCat.Presheaf.germ (X := X) R.obj U.val x hx a •
            (TopCat.Presheaf.germ (X := X) E.val.presheaf U.val x hx).hom ((ι U).symm s)) := by
  sorry

end TopologicalSpace.Opens
