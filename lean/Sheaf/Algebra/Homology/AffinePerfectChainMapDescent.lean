/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.Algebra.FinitePresentationColimit

/-! # Descent of chain maps between affine perfect complexes

Source: Stacks Project, Tag 09RE, affine case (1).
(blueprint: lem-pc-affine-perfect-chain-map-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Chain maps between the limit base changes of bounded finite projective complexes
are scalar extensions of chain maps at some later stage.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 for finite-presentation descent.
Proof: A finite projective module is finitely presented. Apply map descent to the
finitely many components of `f` in the finite support of `E₀`, and enlarge all chosen
stages to one stage above `i₀`. Define all other components to be zero. Each chain-map
identity holds after extension to the colimit. Equality detection for maps from a
finitely presented module makes each identity hold at a later stage. Only finitely
many identities involve a nonzero source term, so directedness supplies one stage
where all of them hold. These components define `g`. The canonical associativity
isomorphisms of scalar extension identify its extension componentwise with `f`;
extensionality of complex morphisms gives the displayed equality.
For a preorder, pass to its posetal reflection: identify mutually comparable
indices and choose representatives. Between mutually comparable indices `F` gives
inverse ring isomorphisms, since their composites are identities in the thin index
category. Thus the representative diagram is equivalent to the original diagram,
and their colimits and scalar extensions are canonically identified. Apply the
partial-order finite-presentation descent theorem to this representative diagram,
then transport back and choose an upper bound with the requested original index.
Alternatively its presentation-matrix proof works verbatim with directedness alone,
using the filtered-ring elementwise criterion, which requires no antisymmetry.
(blueprint: lem-pc-affine-perfect-chain-map-descent) -/
theorem affine_perfect_chainMap_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (f : ((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀) :
    ∃ (i : Set.Ici i₀)
      (g : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
        ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀),
      scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
        E₀ K₀ g = f := by sorry

end CochainComplex
