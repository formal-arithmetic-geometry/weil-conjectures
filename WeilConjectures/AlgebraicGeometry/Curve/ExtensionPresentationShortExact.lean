/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] CategoryTheory.essentiallySmallSelf
attribute [local instance 2000] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 2000] CategoryTheory.sheafIsAbelian CategoryTheory.Abelian.hasPushouts
namespace CategoryTheory.Sheaf.Torsor
private noncomputable abbrev integers (S : AlgebraicGeometry.Scheme.{u}) :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{max u w + 1}).obj
    (AddCommGrpCat.of (ULift.{max u w + 1} ℤ))

private noncomputable abbrev one (S : AlgebraicGeometry.Scheme.{u}) (U : S.Etaleᵒᵖ) :
    (integers.{u, w} S).obj.obj U :=
  (toSheafify S.smallEtaleTopology
    ((Functor.const S.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max u w + 1} ℤ)))).app U ⟨1⟩

end CategoryTheory.Sheaf.Torsor
