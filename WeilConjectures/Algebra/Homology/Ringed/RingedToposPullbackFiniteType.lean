/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.Ringed.RingedToposPullbackCoverData
import WeilConjectures.Algebra.Homology.Ringed.RingedToposPullbackLocalGenerators

/-! # Ordinary ringed-topos pullback preserves finite type

Source: Stacks Project, Modules on Sites, Tag 03DO, clause (5), with
Definition `definition-site-local` and Lemma `lemma-local-final-object`
(blueprint: lem-weil-pbc-ringed-topos-pullback-finite-type).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace SheafOfModules

/-- Ordinary tensor pullback preserves local finite generation for arbitrary ringed topoi.
Source: Stacks Project, Modules on Sites, Tag 03DO, clause (5)
(blueprint: lem-weil-pbc-ringed-topos-pullback-finite-type).

`RI` and `I` express the inverse-image ring and module in any algebraic presentation.
The equation on `c` says that its underlying map, after the inverse-image ring
identification, is exactly `f.ringMap`. Thus the conclusion concerns the specified
ordinary tensor pullback. `IsFiniteType` uses a cover of the terminal sheaf by site
objects, with a finite family of generating sections on each object slice.

Proof:
1. Choose local finite generators of M: a family `q.X i` covering the terminal sheaf
   of the source site and finite generating sections on each slice `M.over (q.X i)`.
2. Index the new family by triples `(i, V, t)`, `t` a section on `V` of the inverse
   image under f of the sheafified representable of `q.X i`. These objects cover
   the terminal sheaf of the target site, because f is a left exact left adjoint
   (lem-weil-pbc-ringed-topos-pullback-cover-data).
3. For each triple, the finite generators on `q.X i` transport along the section `t`
   to finite generating sections of the ordinary pullback on the slice at `V`
   (lem-weil-pbc-ringed-topos-pullback-local-generators).
4. These covers and finite generating families form local generator data of finite
   type for the ordinary pullback, hence `IsFiniteType`.
No flatness, points, finite presentation, or functor of the presented sites is used. -/
theorem isFiniteType_ordinaryRingedToposPullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (_hc : I.ringUnderlying.hom ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map c =
      f.ringMap)
    (M : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    [M.IsFiniteType] : (ordinaryRingedToposPullback I c M).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  have := f.leftExact
  let T : Type u := Σ i : q.I, Σ V : C,
    (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj (q.X i)))).obj.obj
      (Opposite.op V)
  have hgen (j : T) :
      ∃ τ : ((ordinaryRingedToposPullback I c M).over j.2.1).GeneratingSections,
        τ.IsFiniteType := by
    have := hq.isFiniteType j.1
    exact ordinaryRingedToposPullback_localGenerators A B f RI I c _hc M (q.X j.1)
      (q.generators j.1) j.2.1 j.2.2
  let q' : (ordinaryRingedToposPullback I c M).LocalGeneratorsData := {
    I := T
    X := fun j ↦ j.2.1
    coversTop := inverseImage_section_cover f.inverse f.direct f.adj q.X q.coversTop
    generators := fun j ↦ (hgen j).choose }
  have hq' : q'.IsFiniteType := by
    apply LocalGeneratorsData.IsFiniteType.mk
    intro j
    exact (hgen j).choose_spec
  exact SheafOfModules.IsFiniteType.mk (M := ordinaryRingedToposPullback I c M) ⟨q', hq'⟩

end SheafOfModules
