/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Natural linear comparison of equivariant coequalizers

Source: Stacks Project, Categories, Tag 002A, definition-coequalizers and the following
uniqueness paragraph; equivariant and natural refinement for the final clause of the
current blueprint's lem-sfb-extend-to-qlbar-constructible.proof.md.
(blueprint: lem-sfb-equivariant-coequalizer-comparison)
-/

@[expose] public section

universe uD vD uJ vJ

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

/-- A functorial image of a coequalizer projection is epic whenever the image cocone
is colimiting. This uses only the two legs of that cocone. -/
private theorem epi_map_cofork
    {D : Type uD} [Category.{vD} D] {E : Type uJ} [Category.{vJ} E]
    {X Y : D} {a b : X ⟶ Y} (s : Cofork a b) (F : D ⥤ E)
    (hs : IsColimit (F.mapCocone s)) : Epi (F.map s.π) where
  left_cancellation f g h := by
    apply hs.hom_ext
    intro j
    change F.map (s.ι.app j) ≫ f = F.map (s.ι.app j) ≫ g
    cases j with
    | zero =>
        simp only [Cofork.app_zero_eq_comp_π_left, F.map_comp, Category.assoc, h]
    | one => exact h

/-- Linearity descends through an equivariant quotient whose tensor image is epic. -/
private theorem isModHom_of_tensor_epi
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (A : D) [MonObj A] {X Y Z : Mod D A}
    (s : X.X ⟶ Y.X) (t : X.X ⟶ Z.X)
    [IsModHom A s] [IsModHom A t] [Epi ((tensorLeft A).map s)]
    (f : Y.X ⟶ Z.X) (hf : s ≫ f = t) : IsModHom A f where
  smul_hom := by
    apply (cancel_epi ((tensorLeft A).map s)).1
    change (tensorLeft A).map s ≫ ModObj.smul (M := A) (X := Y.X) ≫ f =
      (tensorLeft A).map s ≫ (tensorLeft A).map f ≫ ModObj.smul (M := A) (X := Z.X)
    erw [← Category.assoc, ← IsModHom.smul_hom (A := A) (f := s), Category.assoc, hf,
      ← Category.assoc, ← Functor.map_comp, hf]
    exact IsModHom.smul_hom (A := A) (f := t)

/-- Two natural, equivariant coequalizer presentations of internal modules have a unique
natural module isomorphism normalized by their quotient maps, and its inverse has the
opposite normalization. The tensor hypotheses concern only the displayed coforks.

Source: Stacks Project, Categories, Tag 002A, definition-coequalizers and the following
uniqueness paragraph; the equivariant and natural refinement is the direct argument in
this node, serving the final clause of lem-sfb-extend-to-qlbar-constructible.proof.md.
(blueprint: lem-sfb-equivariant-coequalizer-comparison)

Proof:
1. A coequalizer is epic: two maps agreeing after its projection are two factorizations
of the same equalizing map, so uniqueness identifies them. This applies to both quotient
maps and to both tensor images by the four assumed colimit universal properties.
2. At each j, factor q_j uniquely through r_j to obtain c_j, and factor r_j uniquely
through q_j to obtain d_j. This uses no module structure on H_j.
3. Precompose d_j c_j with r_j and c_j d_j with q_j. The normalization equations make
both composites identities after those projections; step 1 cancels the projections.
4. Precompose the action equation for c_j with A tensor r_j. Equivariance of r_j and
q_j, c_j r_j = q_j, and functoriality of tensor make both sides equal. Cancel A tensor
r_j by step 1. The module-morphism definition of sk-def-sfb-module-objects gives linearity.
5. Similarly, precompose the action equation for d_j with A tensor q_j, use equivariance
and d_j q_j = r_j, and cancel A tensor q_j to obtain linearity of d_j.
6. For u : j to k, precompose the naturality square for c with r_j. Naturality of q and
r and c_j r_j = q_j identify the composites; cancel r_j to get naturality in modules.
7. Naturality of the inverse follows from that of c and the inverse identities in
step 3, as implemented by NatIso.ofComponents. Module morphisms have the underlying
composition.
8. Assemble c and d into natural module transformations. Step 3 proves that they are
inverse. For any second normalized comparison, precompose each component with r_j and
cancel; componentwise equality gives equality of natural isomorphisms. Every step is
objectwise or arrowwise in J, so no colimit over J or smallness of J is used.
-/
theorem existsUnique_equivariant_coequalizer_comparison
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
    (A : D) [MonObj A] {J : Type uJ} [Category.{vJ} J]
    (H : J ⥤ D) (B P Q : J ⥤ Mod D A)
    (a b : H ⟶ B ⋙ Mod.forget (D := D) A)
    (q : B ⋙ Mod.forget (D := D) A ⟶ P ⋙ Mod.forget (D := D) A)
    (r : B ⋙ Mod.forget (D := D) A ⟶ Q ⋙ Mod.forget (D := D) A)
    (hq : ∀ j : J, a.app j ≫ q.app j = b.app j ≫ q.app j)
    (hr : ∀ j : J, a.app j ≫ r.app j = b.app j ≫ r.app j)
    (hq_colimit : ∀ j : J, IsColimit (Cofork.ofπ (q.app j) (hq j)))
    (hr_colimit : ∀ j : J, IsColimit (Cofork.ofπ (r.app j) (hr j)))
    (hq_linear : ∀ j : J,
      IsModHom A (M := (B.obj j).X) (N := (P.obj j).X) (q.app j))
    (hr_linear : ∀ j : J,
      IsModHom A (M := (B.obj j).X) (N := (Q.obj j).X) (r.app j))
    (hq_tensor : ∀ j : J,
      IsColimit ((tensorLeft A).mapCocone (Cofork.ofπ (q.app j) (hq j))))
    (hr_tensor : ∀ j : J,
      IsColimit ((tensorLeft A).mapCocone (Cofork.ofπ (r.app j) (hr j)))) :
    ∃! c : Q ≅ P,
      (∀ j : J, r.app j ≫ (c.hom.app j).hom = q.app j) ∧
      (∀ j : J, q.app j ≫ (c.inv.app j).hom = r.app j) := by
  let e (j : J) : (Q.obj j).X ≅ (P.obj j).X :=
    (hr_colimit j).coconePointUniqueUpToIso (hq_colimit j)
  have he (j : J) : r.app j ≫ (e j).hom = q.app j :=
    (hr_colimit j).comp_coconePointUniqueUpToIso_hom
      (hq_colimit j) WalkingParallelPair.one
  have he' (j : J) : q.app j ≫ (e j).inv = r.app j :=
    (hr_colimit j).comp_coconePointUniqueUpToIso_inv
      (hq_colimit j) WalkingParallelPair.one
  have linear (j : J) : IsModHom A (e j).hom := by
    have := hr_linear j
    have := hq_linear j
    have : Epi ((tensorLeft A).map (r.app j)) :=
      epi_map_cofork (Cofork.ofπ (r.app j) (hr j)) (tensorLeft A) (hr_tensor j)
    exact isModHom_of_tensor_epi A (r.app j) (q.app j) (e j).hom (he j)
  have linear' (j : J) : IsModHom A (e j).inv := by
    have := hq_linear j
    have := hr_linear j
    have : Epi ((tensorLeft A).map (q.app j)) :=
      epi_map_cofork (Cofork.ofπ (q.app j) (hq j)) (tensorLeft A) (hq_tensor j)
    exact isModHom_of_tensor_epi A (q.app j) (r.app j) (e j).inv (he' j)
  let c (j : J) : Q.obj j ≅ P.obj j :=
    { hom := ⟨(e j).hom⟩
      inv := ⟨(e j).inv⟩
      hom_inv_id := Mod.hom_ext _ _ (e j).hom_inv_id
      inv_hom_id := Mod.hom_ext _ _ (e j).inv_hom_id }
  let comparison : Q ≅ P := NatIso.ofComponents c (by
    intro j k u
    apply Mod.hom_ext
    apply Cofork.IsColimit.hom_ext (hr_colimit j)
    change r.app j ≫ (Q.map u).hom ≫ (e k).hom =
      r.app j ≫ (e j).hom ≫ (P.map u).hom
    erw [← Category.assoc, ← r.naturality u, Category.assoc, he k,
      ← Category.assoc, he j]
    exact q.naturality u)
  refine ⟨comparison, ⟨he, he'⟩, ?_⟩
  intro other hother
  apply Iso.ext
  apply NatTrans.ext
  funext j
  apply Mod.hom_ext
  apply Cofork.IsColimit.hom_ext (hr_colimit j)
  exact (hother.1 j).trans (he j).symm

end CategoryTheory
