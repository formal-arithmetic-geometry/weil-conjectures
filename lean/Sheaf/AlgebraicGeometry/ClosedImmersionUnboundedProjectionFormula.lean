module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
import WeilConjectures.Topology.ClosedImmersionPushforwardExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Topology.StalkDirectSums
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.LocallySurjective
import Sheaf.Algebra.Homology.KFlatTensorProduct
import Sheaf.AlgebraicGeometry.KFlatPullbackAdjunctionComparison

/-! # Unbounded projection formula for a closed immersion

Source: Stacks Project, cohomology.tex, Tag 0B55,
lemma-projection-formula-closed-immersion, including the exactness assertion in its proof.
(blueprint: lem-sfb-closed-immersion-unbounded-projection-formula).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option autoImplicit false

namespace AlgebraicGeometry

/-- Closed-immersion direct image is exact, every complex computes its right derived
functor, and the canonical projection-formula morphism is invertible for every pair
of unbounded derived structure-module objects. There is no quasi-coherence,
boundedness, or Tor-dimension condition.

The second clause is the right-derived unit at the homotopy class of an arbitrary
complex. The canonical isomorphisms `DerivedCategory.quotientCompQhIso` identify its
source with the localization of termwise direct image and its target with `Ri_*` of
the localization of that complex. The last clause uses the adjunction
`relativeMVAdj`, pinned to the shared derived units and counits, and the unique
K-flat-characterized tensor comparison of `exists_canonicalPullbackTensorComparison`.
Thus the displayed arrow is precisely the adjoint of tensor comparison followed
by the tensor of the counit with the identity, as in equation-projection-formula-map.

Source: Stacks Project, cohomology.tex, Tag 0B55,
lemma-projection-formula-closed-immersion.
(blueprint: lem-sfb-closed-immersion-unbounded-projection-formula).

Proof:
1. The underlying closed embedding has exact abelian-sheaf direct image
   (lem-sc-closed-immersion-pushforward-exact). The faithful forgetful functor
   preserves kernels and cokernels (lem-weil-pbc-module-sheaves-colimits-forgetful),
   so reflects exactness. Apply lem-weil-pbc-exact-functor-derived-functor to get
   invertibility of the right-derived unit at every complex.
2. Represent E by any complex A and Q by a K-flat resolution K
   (lem-pc-kflat-resolution). Pullback of K is K-flat
   (lem-pc-kflat-pullback-preservation). The two sides are represented by
   Tot(i_*A tensor K) and i_*Tot(A tensor i^*K). Replacing A by a K-flat resolution
   does not alter the latter: its cone tensored with i^*K is acyclic
   (def-pc-kflat-complex). The same cone argument applies to the source.
3. The ordinary projection map sends s tensor t to s tensor i^*t
   (def-pur-sheaf-tensor-product, lem-pc-module-pullback-adjunction).
   Off the closed image both stalks vanish. On the image the map is
   u tensor v mapped to u tensor (v tensor 1), with inverse
   u tensor (v tensor b) mapped to b*u tensor v. Tensor balancing verifies the
   inverse and naturality (lem-weil-pbc-closed-pushforward-stalks,
   lem-weil-pbc-module-stalk-tensor, lem-weil-pbc-module-stalk-pullback).
4. Stalks detect monomorphisms and epimorphisms of abelian sheaves
   (lem-sc-abelian-sheaf-mono-iff-stalk-mono,
   lem-sc-abelian-sheaf-epi-iff-stalk-epi); forgetting modules detects zero kernels
   and cokernels. Thus the ordinary map is invertible. Direct image also commutes
   with all direct sums, since their comparison is the identity on image stalks
   and zero elsewhere (lem-pc-stalk-direct-sums). This includes the empty sum.
5. Sum the ordinary projection maps over p+q=n to obtain a degreewise isomorphism
   of total complexes. Naturality commutes with both differentials and their
   identical signs (-1)^p (def-pc-tensor-complex-sheaves).
6. Take a K-flat resolution B to i_*A. Tensoring it with K is a quasi-isomorphism
   and B tensor K is K-flat (lem-pc-kflat-tensor-product). The comparison in
   lem-pc-kflat-pullback-adjunction-comparison is inverse to the shared left-derived
   counit: apply it to i^*B and the ordinary unit, then use the adjunction pinning
   of def-pc-relative-mv-maps. The equation of
   def-pc-derived-pullback-tensor-comparison represents the adjoint defining the
   projection morphism by the chain tensor comparison followed by the tensor of
   the ordinary adjoint of B to i_*A with the identity. Transposing back gives
   exactly the map of step 5 after the resolution B to i_*A, on every pure tensor.
7. Localization of that chain isomorphism is invertible, proving the last clause;
   step 1 proves the first two. No boundedness or quasi-coherence was used. -/
theorem closedImmersion_unbounded_projection_formula
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    PreservesFiniteLimits (RingedSpace.moduleDirectImage i.toLRSHom.toShHom) ∧
    PreservesFiniteColimits (RingedSpace.moduleDirectImage i.toLRSHom.toShHom) ∧
    (∀ A : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ,
      IsIso ((RingedSpace.moduleDirectImage i.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A))) ∧
    (∀ (E : schemeDerivedCategory Z) (Q : schemeDerivedCategory P),
      IsIso ((relativeMVAdj i).homEquiv
        ((schemeDerivedDirectImage i).obj E ⊗ Q)
        (E ⊗ (derivedPullback i).obj Q)
        ((Classical.choose (exists_canonicalPullbackTensorComparison i))
            ((schemeDerivedDirectImage i).obj E) Q ≫
          ((relativeMVAdj i).counit.app E ⊗ₘ 𝟙 ((derivedPullback i).obj Q))))) := by
  sorry

end AlgebraicGeometry
