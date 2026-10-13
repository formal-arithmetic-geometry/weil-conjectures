/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

public import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.Algebra.FinitePresentationColimit

/-! # Descent of homotopies between affine perfect chain maps

Source: Stacks Project, Tag 09RE, affine case (1).
(blueprint: lem-pc-affine-perfect-homotopy-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A homotopy between two stage chain maps after extension to the colimit
exists already after extension to a sufficiently late stage.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 for finite-presentation descent.
Proof: Choose the homotopy over the colimit. Its degree-minus-one components have
source `E₀` after base change, and only finitely many source degrees are nonzero.
Descend these components by finite presentation and take one common stage above `i`.
At that stage form the degree-zero maps given by the differential of this graded
family. Their equality to `f - g` holds over the colimit by the original homotopy
identity. Detect each of these finitely many equalities at a later stage, and take
one common upper bound. Set the remaining graded components to zero. The shape
condition and homotopy identities then hold in every degree, giving the asserted
homotopy. Canonical scalar-extension associativity identifies all extended maps
with `scalarExtensionHom`; proof irrelevance identifies the composition witnesses.
For a preorder, pass to its posetal reflection: identify mutually comparable
indices and choose representatives. Between mutually comparable indices `F` gives
inverse ring isomorphisms, since their composites are identities in the thin index
category. Thus the representative diagram is equivalent to the original diagram,
and their colimits and scalar extensions are canonically identified. Apply the
partial-order finite-presentation descent theorem to this representative diagram,
then transport back and choose an upper bound with the requested original index.
Alternatively its presentation-matrix proof works verbatim with directedness alone,
using the filtered-ring elementwise criterion, which requires no antisymmetry.
(blueprint: lem-pc-affine-perfect-homotopy-descent) -/
theorem affine_perfect_homotopy_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (f g : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀)
    (h : Nonempty (Homotopy
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm) E₀ K₀ f)
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm) E₀ K₀ g))) :
    ∃ (j : Set.Ici i₀) (hij : i ≤ j), Nonempty (Homotopy
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
        (F.map (homOfLE j.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hij))) E₀ K₀ f)
      (scalarExtensionHom (F.map (homOfLE i.property)).hom (F.map (homOfLE hij)).hom
        (F.map (homOfLE j.property)).hom
        (congrArg CommRingCat.Hom.hom (F.map_comp
          (homOfLE i.property) (homOfLE hij))) E₀ K₀ g)) := by sorry

end CochainComplex
