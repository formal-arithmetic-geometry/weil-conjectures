module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Sheaf.AlgebraicGeometry.CurveEulerTensorGenericRank
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Euler characteristic of a tensor product pulled back to a proper integral curve

Source: Stacks Project, Varieties, Tags 0AYV and 0AYX; Modules, Tags 01CD and 01CT.
(blueprint: lem-trf-curve-pullback-tensor-euler).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pulling two invertible modules back to a proper integral curve gives the Euler
increment equal to the degree of the first pullback. The morphism `j` is arbitrary.

Source: Stacks Project, Varieties, Tag 0AYV, `lemma-degree-on-proper-curve`, with
generic rank one, and Tag 0AYX, `lemma-degree-tensor-product`; Modules, Tags 01CD,
`lemma-tensor-product-pullback`, and 01CT, `lemma-constructions-invertible`.
(blueprint: lem-trf-curve-pullback-tensor-euler).

Proof:
1. Put A = j*L and B = j*M, using tensor pullback. The pullback clause of
lem-weil-pbc-invertible-pullback-tensor makes both A and B invertible for any j.
The hypothesis supplies coherence of B.
2. At the generic point of the integral curve C, the local ring is its residue
field. A local rank-one trivialization of B induces an isomorphism of its generic
stalk with that field. The image of 1 is a singleton basis, so the generic rank
of B is one. Apply lem-trf-curve-euler-tensor-generic-rank to A and B; its rank
coefficient is therefore one, giving chi(A tensor B) = degree(A) + chi(B).
3. The tensor comparison of lem-weil-pbc-invertible-pullback-tensor identifies
j*(L tensor M) with A tensor B. Cohomology carries this isomorphism and its inverse
to inverse k-linear maps in each degree. Their dimensions and hence their Euler
characteristics agree. Substitution yields the displayed equality. -/
theorem eulerChar_tensorPullback_tensor
    (k : Type u) [Field k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = 1)
    (X : Scheme.{u}) (j : C ⟶ X)
    (L M : X.Modules) [L.IsInvertible] [M.IsInvertible]
    (hM : RingedSpace.IsCoherent C.toRingedSpace ((tensorPullback j).obj M)) :
    ((tensorPullback j).obj (L ⊗ M)).eulerChar k =
      ((tensorPullback j).obj L).degree k + ((tensorPullback j).obj M).eulerChar k := by
  sorry

end AlgebraicGeometry.Scheme.Modules
