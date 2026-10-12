module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The bounded-above finite-free Hom complex computes derived internal Hom when the
second complex is bounded below. This is the injective-resolution and acyclic-Hom
part of `derivedInternalHom_of_boundedAbove_finiteFree`.
Source: Stacks Project, Cohomology, Tag 0GM8, case (2), and Section 08J7
(blueprint: lem-sc-derived-hom-finite-free-model-aux).
Proof: replace `G` by a bounded-below K-injective resolution `I`; the cone of the
replacement is bounded below and acyclic, so finite-free Hom preserves the
quasi-isomorphism. The derived internal Hom computation with `I` and the
K-injective comparison then identify the localized Hom complex with derived Hom.
-/
theorem derivedInternalHom_of_boundedAbove_finiteFree_aux
    (U : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U))]
    (E G : CochainComplex (SheafOfModules.{u} (moduleRings U)) ℤ)
    (hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hEfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U) (ULift.{u} (Fin r))))
    (hGbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (G.X q)) :
    Nonempty (DerivedCategory.Q.obj (CategoryTheory.homComplex (R := U.sheaf) E G) ≅
      (CategoryTheory.derivedInternalHom (Opens.grothendieckTopology U) U.sheaf).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj G)) := by
  sorry

end AlgebraicGeometry
