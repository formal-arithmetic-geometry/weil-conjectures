/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.TruncationHypercohomology

/-! # Finite filtered comparison from a bounded-below second-page coproduct comparison

Source: Stacks Project, Tags 015J and 08DZ, the bounded-below spectral-sequence reduction
(blueprint: lem-pc-bounded-below-coproduct-filtration).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Second-page coproduct isomorphisms give a finite filtered comparison with isomorphic
associated graded maps. This is the spectral-sequence part of the coproduct argument;
it does not assert that the underlying comparison is an isomorphism or an epimorphism.
Source: Stacks Project, Tag 015J, finite convergence, and Tag 08DZ, spectral-sequence
reduction; exact-couple naturality is Stacks Tags 011R, 011T and 012F
(blueprint: lem-pc-bounded-below-coproduct-filtration).

Proof: Represent each K_i and S by a bounded-below complex using the common cohomological
bound a and canonical lower truncation. Apply `exists_truncationHypercohomology` to
these representatives. Its natural second-page identifications identify the maps induced
by u_i with R^p F applied to H^r(u_i). Take the termwise coproduct of the summands' exact
couples; sums in a Grothendieck abelian category are exact, so this is an exact couple.
Naturality gives its map to the target couple, with second-page maps exactly hE2.
Use `BigradedExactCouple.coupleMorphism` to derive maps of successive pages. Exactness of
sums preserves kernels, images and cokernels, so the second-page isomorphisms imply
isomorphisms at every subsequent page and hence at each stable term. For total degree q
only 0 <= p <= q-a occurs. The hypercohomology theorem gives abutment filtrations with
common full step 0 and zero step q-a+1. Sum the summands' filtration steps: exactness
makes their inclusions monic and their successive quotients the coproducts of the
summands' graded pieces. This defines FS on the coproduct of the abutments, and the
target abutment filtration defines FT. Sum the natural filtered abutment maps to obtain
phi. Its underlying map is Sigma.desc of H^q(RF(u_i)), by the natural abutment
identifications. The compatibility of the stable-page maps with associated graded maps
in `coupleMorphism` identifies gradedMap phi with the stable-page isomorphisms, giving
hgraded. Both filtrations are finite with the same bounds. For q<a, all abutments are
zero and use the zero filtrations; for an empty family the source filtration is zero
and the same exact-couple argument applies. No choices of representatives or filtrations
are used to define library data: this theorem asserts only their existence. -/
theorem exists_boundedBelow_coproduct_filtration
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type v) (K : I → DerivedCategory A) (S : DerivedCategory A)
    (u : ∀ i, K i ⟶ S) (a q : ℤ)
    (hK : ∀ (i : I) (r : ℤ), r < a →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (K i)))
    (hS : ∀ r : ℤ, r < a → IsZero ((DerivedCategory.homologyFunctor A r).obj S))
    (hE2 : ∀ (p : ℕ) (r : ℤ), IsIso (Sigma.desc (fun i ↦
      (DerivedCategory.singleFunctor A 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor B (p : ℤ)).map
          ((DerivedCategory.homologyFunctor A r).map (u i))))) :
    ∃ (FS : DecreasingFiltration
        (∐ (fun i ↦ (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).obj
          (K i))))
      (FT : DecreasingFiltration
        ((F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).obj S))
      (phi : FilteredObject.Hom ⟨_, FS⟩ ⟨_, FT⟩),
      FS.IsFinite ∧ FT.IsFinite ∧
        phi.hom = Sigma.desc (fun i ↦
          (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor B q).map (u i)) ∧
        ∀ p : ℤ, IsIso (FilteredObject.gradedMap phi p) := by sorry

end CategoryTheory
