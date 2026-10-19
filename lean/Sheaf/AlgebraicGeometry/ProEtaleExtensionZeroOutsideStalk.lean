/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U5
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Vanishing of extension by zero at a geometric point outside the open

Source: Stacks Project, Tags 09AE, 03DI, 03DJ and 00Y8(3), and the stalk paragraph
of blueprint lemma `lem-cbc-proetale-extension-zero`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The geometric stalk of an extended module sheaf vanishes outside the open.
Source: Stacks Project, Tags 09AE, 03DI, 03DJ, 0F6B, 0F6C and 00Y8(3);
blueprint lemma `lem-cbc-proetale-extension-zero`, stalk-description paragraph.
(blueprint: lem-cbc-proetale-extension-zero-outside-stalk).

Proof: To show that the colimit is zero, show its identity equals zero and test this
on every colimit coprojection and every section s. Nonfactorization of y through j
means its underlying point lies outside the range of j: otherwise the open immersion
lifting property would factor y through U. For a pointed neighbourhood N, its chosen
point x therefore also lies over the complement of U. The existing source theorem
`exists_map_eq_zero_openImmersionLowerShriek` supplies a weakly etale refinement
f : V -> N containing a point q over x on which s restricts to zero. The fibre product
V x_N Spec Omega is nonempty, by the pullback preimage theorem. Its weakly etale map
to Spec Omega has a section by `exists_comp_eq_id_of_weaklyEtale`; composition with
the other projection gives a lift of y to V compatible with the lift to N. Thus V
becomes a pointed refinement M -> N. The colimit relation identifies the class of s
with that of its restriction to M, which is zero. Every coprojection therefore
annihilates the difference of the identity and zero, proving the assertion. -/
theorem openExtension_outside_stalk (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X)
    (hy : ¬ ∃ z : Spec (.of Ω) ⟶ U, z ≫ j = y)
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)) :
    IsZero (Scheme.proEtaleGeometricFixedModuleStalk y A
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F)) := by
  classical
  let G := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F
  let D := Scheme.proEtaleGeometricStalkDiagram y G
  change IsZero (colimit D)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro N
  apply ModuleCat.hom_ext
  ext s
  have hy' : y.base (IsLocalRing.closedPoint Ω) ∉ Set.range j.base := by
    intro h
    have hsub : Set.range y.base ⊆ Set.range j.base := by
      rintro _ ⟨q, rfl⟩
      simpa only [Subsingleton.elim q (IsLocalRing.closedPoint Ω)] using h
    exact hy ⟨IsOpenImmersion.lift j y hsub, IsOpenImmersion.lift_fac j y hsub⟩
  let x := N.unop.hom.left.base (IsLocalRing.closedPoint Ω)
  have hx : N.unop.right.hom.base x ∉ Set.range j.base := by
    change (N.unop.hom.left ≫ N.unop.right.hom).base _ ∉ _
    have hN : N.unop.hom.left ≫ N.unop.right.hom = y := Over.w N.unop.hom
    exact (congrArg (fun k : Spec (.of Ω) ⟶ X ↦
      k.base (IsLocalRing.closedPoint Ω)) hN).symm ▸ hy'
  obtain ⟨V, f, ⟨q, hq⟩, hs⟩ :=
    exists_map_eq_zero_openImmersionLowerShriek j F s x hx
  have hf : WeaklyEtale f.left := by
    refine MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
      f.left ((Scheme.proEtaleGeometricNeighbourhoodForget y).obj N.unop).hom
      (inferInstance : WeaklyEtale _) ?_
    exact (MorphismProperty.Over.w f) ▸ V.prop
  obtain ⟨p, _, hp⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f.left) (g := N.unop.hom.left) q (IsLocalRing.closedPoint Ω) hq
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd f.left N.unop.hom.left) p
  let w := σ ≫ pullback.fst f.left N.unop.hom.left
  have hw : w ≫ f.left = N.unop.hom.left := by
    dsimp only [w]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  let M : Scheme.ProEtaleGeometricNeighbourhood y :=
    StructuredArrow.mk (Y := V) (Over.homMk w (by
      change w ≫ V.hom = y
      rw [← MorphismProperty.Over.w f, ← Category.assoc, hw]
      exact Over.w N.unop.hom))
  let a : M ⟶ N.unop := StructuredArrow.homMk f (by
    apply Over.OverMorphism.ext
    exact hw)
  have hc := colimit.w D a.op
  have he := congrArg (fun t ↦ t s) hc
  change colimit.ι D N s = 0
  rw [← he]
  change colimit.ι D (Opposite.op M) (G.obj.map f.op s) = 0
  rw [hs, map_zero]


end AlgebraicGeometry.ProEtale
