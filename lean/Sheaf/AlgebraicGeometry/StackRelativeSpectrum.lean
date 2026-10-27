/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q61 and Q40
-/
module

public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Elements

/-! # The relative-spectrum category of algebra points

Source: Stacks Project, Constructions, Tags 01LW--01LX, section-spec and
its equation-spec; the stack version is used in Alper Lemma 5.2.11
(blueprint: def-sfb-stack-relative-spectrum).

The objects are algebra maps on the entire slice over a test object. Restriction
makes them a presheaf; the opposite category of elements retains the direction
of the original arrows. Its based projection forgets only the algebra map.
No algebraicity, quasi-coherence or representability assertion is part of this
construction. These five declarations are moved from AdequateRelativeSpectrum.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory Opposite

namespace CategoryTheory

/-- Algebra maps to regular functions on the entire slice over a test object.
The equation requires the map to be an algebra map, not just a ring map.
Source: Stacks Tag 01LX, functor of points
(blueprint: def-sfb-stack-relative-spectrum). -/
def ModuliAlgebraPoint {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) (x : F.obj) :=
  { a : (Over.forget x).op ⋙ A.right.obj ⟶
      (Over.forget x).op ⋙ (moduliStructureSheaf F hF).obj //
    Functor.whiskerLeft (Over.forget x).op A.hom.hom ≫ a = 𝟙 _ }

/-- Restriction of algebra maps along all arrows of the total category.
Source: Stacks Tag 01LX (blueprint: def-sfb-stack-relative-spectrum). -/
def moduliAlgebraPointPresheaf {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : F.objᵒᵖ ⥤ Type (max (u + 1) v w) where
  obj x := ModuliAlgebraPoint A x.unop
  map f := ↾fun a ↦ ⟨Functor.whiskerLeft (Over.map f.unop).op a.1, by
    apply NatTrans.ext
    funext z
    exact congrArg (fun t ↦ t.app (op ((Over.map f.unop).obj z.unop))) a.2⟩
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext z
    have hn := a.1.naturality
      (Over.homMk (𝟙 z.unop.left) (by simp) :
        (Over.map (𝟙 x.unop)).obj z.unop ⟶ z.unop).op
    simpa using hn
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext z
    change a.1.app (op (Over.mk (z.unop.hom ≫ (g.unop ≫ f.unop)))) =
      a.1.app (op (Over.mk ((z.unop.hom ≫ g.unop) ≫ f.unop)))
    rw [Category.assoc]

/-- The category of pairs `(x, a)` and compatible arrows, projected to the original
fibred category. Taking the opposite category of elements gives arrows in the
same direction as the arrows of the stack.
Source: Stacks Tag 01LX (blueprint: def-sfb-stack-relative-spectrum). -/
def moduliRelativeSpectrumForget {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) :
    (moduliAlgebraPointPresheaf A).Elementsᵒᵖ ⥤ F.obj where
  obj x := x.unop.1.unop
  map f := f.unop.1.unop

/-- The actual relative-spectrum functor of points, with its projection to schemes.
No algebraicity or finiteness is assumed to define this based category.
Source: Stacks Tag 01LX; Alper Lemma 5.2.11
(blueprint: def-sfb-stack-relative-spectrum). -/
def moduliRelativeSpectrum {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (moduliRelativeSpectrumForget A ⋙ F.p)

/-- The canonical projection remembers the test object and forgets its algebra map.
Source: Stacks Tag 01LX (blueprint: def-sfb-stack-relative-spectrum). -/
def moduliRelativeSpectrumProjection {S : AlgebraicGeometry.Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} {hF : IsFibredInGroupoids F}
    (A : ModuliAlgebraSheaf F hF) : BasedFunctor (moduliRelativeSpectrum A) F where
  toFunctor := moduliRelativeSpectrumForget A
  w := rfl


end CategoryTheory
