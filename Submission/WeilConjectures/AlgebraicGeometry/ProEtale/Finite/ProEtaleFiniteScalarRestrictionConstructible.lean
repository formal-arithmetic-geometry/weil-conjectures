/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite scalar restriction preserves pro-etale constructibility

Source: current Weil blueprint, sec-proetale-coefficients,
`sk-prop-integral-criterion-reductions.proof.md`, second paragraph, last sentence;
Stacks Tags 03DA, 03D2, 093I, 093Q, 09AJ, 010N and 015F
(blueprint: lem-pe-finite-scalar-restriction-constructible).

The coefficient map is arbitrary; no surjectivity or flatness is imposed.
The intrinsic constant-ring module category and its existing exact restriction functor
are used throughout. The witness statements retain each original local trivialization cover.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ S₀ : Cᵒᵖ ⥤ RingCat.{w}} {R S : Sheaf J RingCat.{w}}
  (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  (a₀ : R₀ ⟶ S₀) (a : R ⟶ S) (comm : α ≫ a.hom = a₀ ≫ β)
  (P : _root_.PresheafOfModules.{t} S₀)

end

private theorem constantDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) _).map a ≫
        proEtaleConstantDirectImageMap f _ B =
      proEtaleConstantDirectImageMap f _ A ≫
        (proEtaleSheafDirectImage f _).map
          ((constantSheaf (ProEt.topology X) _).map a) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    (((proEtaleSheafDirectImage f _).obj
      ((constantSheaf (ProEt.topology X) _).obj B)).property)
  have hA := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A)
    ((proEtaleSheafDirectImage f _).obj ((constantSheaf (ProEt.topology X) _).obj A)))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  have hB := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj B)
    ((proEtaleSheafDirectImage f _).obj ((constantSheaf (ProEt.topology X) _).obj B)))
    (Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)))
  change toSheafify (ProEt.topology Y) _ ≫
      sheafifyMap (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a) ≫
      (proEtaleConstantDirectImageMap f _ B).hom =
    toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ A).hom ≫
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (sheafifyMap (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  rw [show toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ B).hom = _ from hB]
  rw [← Category.assoc, show toSheafify (ProEt.topology Y) _ ≫
      (proEtaleConstantDirectImageMap f _ A).hom = _ from hA]
  exact (congrArg (Functor.whiskerLeft (proEtaleBaseChange f).op)
    (toSheafify_naturality (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map a)))

end AlgebraicGeometry.Scheme
