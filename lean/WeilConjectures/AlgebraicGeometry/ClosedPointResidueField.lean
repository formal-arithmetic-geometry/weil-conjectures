module

public import WeilConjectures.PointCount

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The residue field of a closed point of a scheme locally of finite type over an algebraically
closed field `k` is algebraically closed: it is a finite extension of `k`. -/
lemma Scheme.isAlgClosed_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) : IsAlgClosed (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
    (f := X.fromSpecResidueField x ≫ f)).mpr inferInstance
  rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff] at this
  have : Module.Finite k (X.residueField x) := this
  exact IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective (algebraMap k _)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)))


end AlgebraicGeometry
