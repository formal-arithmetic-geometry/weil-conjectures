/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts

/-! # Copowers for proper geometric-point derived direct image

This is the component-level comparison used to assemble preservation of all discrete
colimits.  Its proof is the finite-coefficient proper cohomology argument from Tags 0F11
and 0F12.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Proper direct image over a geometric point preserves a sum of copies of one object.
Source: Stacks Project, Lemma 59.96.3 (Tag 0F11), used in Lemma 59.96.5 (Tag 0F12).
(blueprint: lem-etale-proper-geometric-point-derived-copowers)

Proof in words: the additive group of a finite coefficient ring is torsion, including
for the zero ring. Properness makes p finite type and qcqs. Apply the source-library
finite cohomological-dimension theorem to p as a morphism of finite-type k-schemes,
using the identity as the structure map on Spec k. The source-library coproduct theorem
then shows that Rp_* preserves every I-indexed coproduct, hence the constant family at E.
Both source theorems include empty schemes and empty indexing types. -/
theorem proper_geometricPoint_preservesCopowers
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p]
    (I : Type (u + 1))
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    PreservesColimit (Discrete.functor (fun _ : I ↦ E))
      (R((p)_*[ModuleCat.{u + 1} Λ])) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have hf := hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    Λ hΛ p (𝟙 _) p (Category.comp_id p)
  have := preservesCoproducts_rightDerivedLowerStar Λ p hf I
  infer_instance

end AlgebraicGeometry.Etale
