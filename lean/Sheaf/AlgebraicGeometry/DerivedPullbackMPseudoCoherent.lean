module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.MPseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect

/-! # Derived pullback preserves degreewise pseudo-coherence

Source: Stacks Project, Cohomology of Sheaves, Tag 09U7,
`lemma-pseudo-coherent-pullback`, specialized to schemes
(blueprint: lem-sfb-derived-pullback-m-pseudocoherent).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Derived pullback along any morphism of schemes preserves `m`-pseudo-coherence,
with no flatness, quasi-coherence or Noetherian assumption.

Source: Stacks Project, Cohomology of Sheaves, Tag 09U7,
`lemma-pseudo-coherent-pullback`, specialized to schemes
(blueprint: lem-sfb-derived-pullback-m-pseudocoherent).

Proof:
1. Choose local strictly perfect approximations `Pᵢ ⟶ K|Vᵢ` using
   def-sfb-m-pseudo-coherent-complex. The inverse images `Uᵢ` cover `T`;
   lem-pc-derived-pullback-open-restriction-universes identifies the restriction
   of `Lh* K` with `Lhᵢ* (K|Vᵢ)`.
2. Complete each approximation to a distinguished triangle by
   def-weil-triangulated-category. Its cone `Cᵢ` has zero cohomology in degrees
   at least `m`, by lem-sf-derived-homology-long-exact and the approximation's
   isomorphisms above `m` and surjectivity at `m`.
3. Factor derived pullback into exact module inverse image and derived scalar
   extension, using def-pc-derived-pullback. The former is triangulated by
   lem-pc-inverse-image-module-functor-exact and
   lem-sf-exact-functor-derived-triangulated; the latter is triangulated by
   lem-pur-derived-change-of-rings. Hence the pulled triangle is distinguished.
4. Exact inverse image commutes with cohomology by
   lem-weil-pbc-exact-functor-complex-cohomology. Apply clause (a) of
   lem-weil-pbc-ringed-tensor-cohomological-bounds with bound `m - 1` to see
   that `Lhᵢ* Cᵢ` still has zero cohomology in degrees at least `m`.
5. Each `Pᵢ` is perfect by def-pc-perfect-complex, so
   lem-pc-derived-pullback-perfect makes its pullback perfect. Refine the
   cover to choose strictly perfect models for these pulled objects. Exact
   restriction preserves the distinguished triangles and their cohomology
   vanishing by lem-sf-exact-functor-derived-triangulated and
   lem-weil-pbc-exact-functor-complex-cohomology. The natural restriction
   comparison of step 1 identifies their targets with restrictions of `Lh* K`.
6. The long exact cohomology sequence (lem-sf-derived-homology-long-exact)
   gives isomorphisms above `m` and surjectivity at `m` for the resulting
   strictly perfect approximations. The refined opens cover `T`, giving
   precisely def-sfb-m-pseudo-coherent-complex. -/
theorem derivedPullback_preserves_mPseudoCoherent {T Y : Scheme.{u}} (h : T ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [∀ U : T.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (m : ℤ) (K : schemeDerivedCategory Y) (hK : Scheme.IsMPseudoCoherent Y m K) :
    Scheme.IsMPseudoCoherent T m ((derivedPullback h).obj K) := by
  sorry

end AlgebraicGeometry
