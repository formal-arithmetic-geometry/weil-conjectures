/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftOverlapRelations

/-! # Finite chains of arrows from closed-lift tests

Source: Step 4 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ClosedLiftChain

/-- A factorization of a fixed arrow through an indexed closed-lift test.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus). -/
structure Vertex {X Z : Scheme.{u}} (z : Z ⟶ X) {P V : X.ProEt} (f : V ⟶ P) where
  index : ClosedLiftArrowIndex z P
  arrow : V ⟶ index.val.1
  comm : arrow ≫ index.val.2 = f

/-- Adjacent factorizations extend, together and over `P`, to one closed-lift test.
The common source `V` need not itself be a test.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus). -/
def Edge {X Z : Scheme.{u}} {z : Z ⟶ X} {P V : X.ProEt} {f : V ⟶ P}
    (v w : Vertex z f) : Prop :=
  ∃ (U : X.ProEt) (_ : ClosedLiftTest z U) (a : V ⟶ U)
    (b : U ⟶ v.index.val.1) (c : U ⟶ w.index.val.1),
    a ≫ b = v.arrow ∧ a ≫ c = w.arrow ∧
      b ≫ v.index.val.2 = c ≫ w.index.val.2

/-- The difference of the corresponding summands, canonically lifted to the kernel.
The equality over `P` is part of the vertices, so this is an actual construction.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus). -/
noncomputable def difference (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} {z : Z ⟶ X} {P V : X.ProEt} {f : V ⟶ P}
    (v w : Vertex z f) :
    (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj V ⟶
      kernel (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  refine kernel.lift _
    (F.map v.arrow ≫ closedLiftArrowι A z P v.index -
      F.map w.arrow ≫ closedLiftArrowι A z P w.index) ?_
  simp only [Preadditive.sub_comp, Category.assoc, closedLiftArrowι_augmentation]
  change F.map v.arrow ≫ F.map v.index.val.2 -
    F.map w.arrow ≫ F.map w.index.val.2 = 0
  rw [← F.map_comp, ← F.map_comp, v.comm, w.comm, sub_self]

private theorem edge_zero (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} {z : Z ⟶ X} {P V : X.ProEt} {f : V ⟶ P}
    {v w : Vertex z f} (h : Edge v w) :
    difference A v w ≫ cokernel.π (closedLiftGeneratorAugmentation A z
      (kernel (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom)).hom = 0 := by
  obtain ⟨U, hU, a, b, c, hab, hac, hbc⟩ := h
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let e := closedLiftGeneratorAugmentation A z (F.obj P)
  let r : F.obj U ⟶ kernel e.hom := kernel.lift _
    (F.map b ≫ closedLiftArrowι A z P v.index -
      F.map c ≫ closedLiftArrowι A z P w.index) (by
      dsimp only [e, F]
      simp only [Preadditive.sub_comp, Category.assoc, closedLiftArrowι_augmentation]
      change F.map b ≫ F.map v.index.val.2 - F.map c ≫ F.map w.index.val.2 = 0
      rw [← F.map_comp, ← F.map_comp, hbc, sub_self])
  have hfac : difference A v w = F.map a ≫ r := by
    apply (cancel_mono (kernel.ι e.hom)).1
    dsimp only [difference, r, e, F]
    simp only [Category.assoc, kernel.lift_ι, Preadditive.comp_sub]
    rw [← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp, hab, hac]
  rw [hfac, Category.assoc, closedLiftTestRelation_cokernel A z _ U hU r, comp_zero]

/-- Every finite chain gives a relation killed by the closed-test augmentation.

Source: Step 4 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus).

Proof: an edge extends to a test `U`. Its difference is the restriction of the kernel
map on `U`, hence is killed by the test summand of the augmentation. Induct on the
reflexive transitive closure. At a concatenation the two kernel differences add to
the endpoint difference: compose with the kernel inclusion, cancel the middle
summand, and use its monicity. Additivity then proves the assertion. -/
theorem difference_cokernel (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} {z : Z ⟶ X} {P V : X.ProEt} {f : V ⟶ P}
    {v w : Vertex z f} (h : Relation.ReflTransGen Edge v w) :
    difference A v w ≫ cokernel.π (closedLiftGeneratorAugmentation A z
      (kernel (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom)).hom = 0 := by
  induction h with
  | refl =>
    have hz : difference A v v = 0 := by
      apply (cancel_mono (kernel.ι (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom)).1
      simp only [difference, kernel.lift_ι, sub_self, zero_comp]
    rw [hz, zero_comp]
  | @tail w y h hwy ih =>
    have hadd : difference A v y = difference A v w + difference A w y := by
      apply (cancel_mono (kernel.ι (closedLiftGeneratorAugmentation A z
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom)).1
      simp only [difference, kernel.lift_ι, Preadditive.add_comp]
      abel
    rw [hadd, Preadditive.add_comp, ih, edge_zero A hwy, add_zero]

private theorem freeSheafHomEquiv_map (A : Type u) [CommRing A]
    {X : Scheme.{u}} {V U : X.ProEt} (a : V ⟶ U)
    (M : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (r : (ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj U ⟶ M) :
    ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) V M
        ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).map a ≫ r) =
      M.obj.map a.op (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) U M r) := by
  simp only [ProEtale.freeSheafHomEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

/-- Local chains on a covering family kill an elementary overlap relation.

Source: Step 4 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-closed-lift-chain-calculus).

Proof: restrict the overlap relation along every covering arrow. Its kernel inclusion
is exactly the difference of the two endpoint vertices, hence the maps themselves
agree by kernel monicity. The chain calculation kills this difference. Free-sheaf
Yoneda identifies the remaining map with one section of its target; that section
restricts to zero on a covering family and is therefore zero by sheaf separatedness. -/
theorem overlap_cokernel_of_chains (A : Type u) [CommRing A]
    {X Z : Scheme.{u}} (z : Z ⟶ X) (P : X.ProEt)
    (t s : ClosedLiftArrowIndex z P)
    {κ : Type (u + 1)} (V : κ → X.ProEt)
    (a : ∀ j, V j ⟶ pullback t.val.2 s.val.2)
    (hcover : Presieve.ofArrows V a ∈ ProEt.precoverage X _)
    (hchain : ∀ j, Relation.ReflTransGen Edge
      (⟨t, a j ≫ pullback.fst t.val.2 s.val.2, by
          simp only [Category.assoc]⟩ :
        Vertex z (a j ≫ pullback.fst t.val.2 s.val.2 ≫ t.val.2))
      ⟨s, a j ≫ pullback.snd t.val.2 s.val.2, by
        simp only [Category.assoc, pullback.condition]⟩) :
    closedLiftOverlapRelation A z P t s ≫
      cokernel.π (closedLiftGeneratorAugmentation A z
        (kernel (closedLiftGeneratorAugmentation A z
          ((ProEtale.freeSheaf (ULift.{u + 1, u} A) X).obj P)).hom)).hom = 0 := by
  let F := ProEtale.freeSheaf (ULift.{u + 1, u} A) X
  let e := closedLiftGeneratorAugmentation A z (F.obj P)
  let d := closedLiftGeneratorAugmentation A z (kernel e.hom)
  let C := cokernel d.hom
  let r := closedLiftOverlapRelation A z P t s ≫ cokernel.π d.hom
  have hz (j : κ) : F.map (a j) ≫ r = 0 := by
    have H := difference_cokernel A (hchain j)
    have hd : F.map (a j) ≫ closedLiftOverlapRelation A z P t s =
        difference A
          (⟨t, a j ≫ pullback.fst t.val.2 s.val.2, by
          simp only [Category.assoc]⟩ :
            Vertex z (a j ≫ pullback.fst t.val.2 s.val.2 ≫ t.val.2))
          ⟨s, a j ≫ pullback.snd t.val.2 s.val.2, by
            simp only [Category.assoc, pullback.condition]⟩ := by
      apply (cancel_mono (kernel.ι e.hom)).1
      dsimp only [e, F]
      simp only [closedLiftOverlapRelation, difference, Category.assoc, kernel.lift_ι,
        Preadditive.comp_sub, Functor.map_comp]
    simpa only [r, ← Category.assoc, hd] using H
  apply (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A)
    (pullback t.val.2 s.val.2) C).injective
  let C' := (sheafCompose (ProEt.topology X)
    (CategoryTheory.forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).obj C
  have hsh := (isSheaf_iff_isSheaf_of_type _ _).mp C'.property
  apply (hsh.isSheafFor_of_mem_precoverage hcover).isSeparatedFor.ext
  rintro U b ⟨j⟩
  change C.obj.map (a j).op
      (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) _ C r) =
    C.obj.map (a j).op
      (ProEtale.freeSheafHomEquiv (ULift.{u + 1, u} A) _ C 0)
  rw [← freeSheafHomEquiv_map, ← freeSheafHomEquiv_map, hz, comp_zero]

end AlgebraicGeometry.Scheme.ClosedLiftChain
