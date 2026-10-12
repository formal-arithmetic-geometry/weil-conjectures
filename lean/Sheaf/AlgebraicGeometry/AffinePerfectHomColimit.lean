/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.Algebra.FinitePresentationColimit
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.RhomGlobalSections
import Sheaf.Paper.AffineProjectiveComplexDerivedHom

/-! # Affine full faithfulness for perfect complexes over a filtered colimit

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE,
affine case (blueprint: lem-pc-affine-perfect-hom-colimit).

The equivalences `ident` identify a presentation `H` with the stage derived Hom sets.
The equations `htransition` and `hcanonical` specify scalar extension on every chain-map
representative, so neither the diagram nor its comparison map is arbitrary.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The canonical affine derived Hom comparison is bijective.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof.
Proof: (1) bounded projective sources compute derived Hom by the ordinary Hom complex
(lem-sc-affine-projective-complex-derived-hom and lem-pur-rhom-global-sections).
Bounded flat targets are K-flat (lem-pc-module-bounded-flat-kflat), so termwise scalar
extension represents derived scalar extension. (2) In each degree the Hom complex is a
finite product of Hom modules from finitely presented terms. Component maps descend,
and equality is detected at a later stage (lem-pc-fp-module-map-descent-affine). This gives
a degreewise isomorphism commuting with differentials. (3) A cycle descends after making
its differential zero at a later stage; a boundary relation descends in the same way.
Thus filtered colimits commute with zeroth cohomology, giving the asserted bijection.
(blueprint: lem-pc-affine-perfect-hom-colimit) -/
theorem affine_perfect_hom_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    [∀ i : I, HasDerivedCategory.{w} (ModuleCat.{u} (F.obj i))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (colimit F : CommRingCat.{u}))]
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (H : Set.Ici i₀ ⥤ Type w) [HasColimit H]
    (ident : ∀ i : Set.Ici i₀, H.obj i ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀)))
    (htransition : ∀ (i j : Set.Ici i₀) (hij : i ≤ j)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      ident j (H.map (homOfLE hij) ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
          (F.map (homOfLE j.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp
            (homOfLE i.property) (homOfLE hij))) E₀ K₀ f))
    (c : Cocone H)
    (e : c.pt ≃
      (DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj E₀) ⟶
       DerivedCategory.Q.obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (colimit.ι F i₀).hom) (.up ℤ)).obj K₀)))
    (hcanonical : ∀ (i : Set.Ici i₀)
      (f : (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj E₀ ⟶
        (Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom) (.up ℤ)).obj K₀),
      e (c.ι.app i ((ident i).symm (DerivedCategory.Q.map f))) =
        DerivedCategory.Q.map (scalarExtensionHom
          (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
          (colimit.ι F i₀).hom
          (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
          E₀ K₀ f)) :
    Function.Bijective (e ∘ colimit.desc H c) := by
  sorry

end CochainComplex
