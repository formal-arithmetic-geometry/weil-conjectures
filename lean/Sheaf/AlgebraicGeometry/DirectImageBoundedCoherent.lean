/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Proper-support direct image preserves bounded coherent complexes

Source: literature/stacks-project/perfect.tex, Derived Categories of Schemes,
Lemma 36.11.3 (Tag 08E2; label lemma-direct-image-coherent)
(blueprint: lem-pc-direct-image-bounded-coherent).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If `S` is Noetherian and `f : X ⟶ S` is locally of finite type, then the derived
 direct image of a bounded complex with coherent cohomology and proper support has
 bounded coherent cohomology. Source: Stacks Project, Tag 08E2, Lemma 36.11.3
 (blueprint: lem-pc-direct-image-bounded-coherent).

Proof:
1. Represent `E` by a bounded complex and apply `thm-sp-truncation-e2` to the
   left exact module direct-image functor. This gives the convergent spectral sequence
   `Rᵖf_* Hᑫ(E) ⇒ Hᵖ⁺ᑫ(Rf_*E)` and finite filtrations on its abutment.
2. By `lem-pc-coherent-support-proper-higher-direct-image`, each term of its
   second page is coherent, since each source cohomology sheaf has proper support.
3. The filtration pieces are subquotients of these terms; coherence on the locally
   Noetherian target is closed under subquotients and finite extensions. Thus every
   cohomology sheaf of the direct image is coherent.
4. The lower bound follows from the vanishing quadrant of `thm-sp-truncation-e2`.
5. Use `lem-pc-direct-image-qc-support-reduction` to restrict to a quasi-compact
   quasi-separated open containing all supports, without changing the direct image.
   Apply `lem-pc-derived-direct-image-uniform-truncation-bound` to obtain the upper bound. -/
theorem directImage_isBounded_coherent
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) :
    (∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage f).obj E))) ∧
    (∀ i : ℤ,
      RingedSpace.IsCoherent S.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj
          ((schemeDerivedDirectImage f).obj E))) := by
  sorry

end AlgebraicGeometry.Scheme
