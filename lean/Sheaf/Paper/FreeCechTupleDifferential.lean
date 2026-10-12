module

public import Sheaf.Paper.FreeCechTupleBasis
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Sheaf.Paper.PowerSetComplexContractible

/-! # Differential compatibility of the free Čech tuple map

Source: Stacks Project, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-free-cech-differential-compatibility)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- The tuple map commutes with the alternating differential.
Source: Stacks Project, Tags 03AT and 03F5, the direct-sum decomposition.
Proof: Both sides are linear maps on a direct sum of free modules. Check their
values on a generator DFinsupp.single φ (Finsupp.single x r). The tuple map sends
this generator to r times the coproduct injection of the free generator associated
with the compatible tuple x. The n-th differential is the sum over j in Fin (n+2)
of (-1)^j times the j-th face. A face reindexes the indices along Fin.succAbove j
and postcomposes the product map with the corresponding product projection.
The equations Pi.lift_π in Over U₀ identify that composite with the product map
for the tuple with its j-th entry omitted. Thus every summand is r times the
same generator with the same sign on both sides. The block index φ is preserved.
The integer sign action agrees with multiplication by the corresponding power
of -1 in O(W), including for noncommutative rings. Extend the equality by the
Finsupp and DFinsupp universal properties. Empty families and the zero ring
are included, since no basis element or nonzero scalar is required.
(blueprint: lem-weil-pbc-free-cech-differential-compatibility) -/
theorem freeCechDifferential_compatibility (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) :
    let M := freeCechModule X ι U₀ U f O
    let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj M))
    let b := freeCechTupleMap X ι U₀ U f O W
    let D := fun n ↦ DFinsupp.mapRange.linearMap
      (fun φ ↦ Algebra.powerSetComplexDifferential (O.obj (op W))
        (freeCechLifts X ι U₀ U f W φ) n)
    ∀ n, (K.d (n + 1) n).hom.comp (b (n + 1)) = (b n).comp (D n) := by
  sorry

end AlgebraicGeometry
