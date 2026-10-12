/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.AlgebraicGeometry.InverseImageExactKFlat

/-! # Tensor pullback of quasi-isomorphisms between K-flat complexes

Source: Stacks Project, Cohomology, Tags 06YJ and 06YC.
(blueprint: lem-pc-tensor-pullback-kflat-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Tensor pullback preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks Project, Cohomology, Tags 06YJ and 06YC; Cohomology on Sites, Tag 06YT.

Proof: exact inverse image preserves the quasi-isomorphism and takes the two K-flat
complexes to K-flat complexes over g⁻¹ O_S. For the second complex, apply resolution
preservation to its identity morphism. Apply the quasi-isomorphism preservation clause
of derived change of rings to g⁻¹ O_S → O_T. One may choose standard derived categories
locally for this application; the conclusion is about complexes and does not retain
these choices. The object and map formulas for change of rings identify the composite
with the recorded tensor pullback, so its termwise map is a quasi-isomorphism.
For completeness the change-of-rings clause follows by resolving O_T by a K-flat
complex: tensoring that resolution with each source K-flat complex preserves the
augmentation quasi-isomorphism, while tensoring the inverse-image quasi-isomorphism
with the resolution preserves it by K-flatness. The commutative square and two-out-of-
three give the claim. The argument works for arbitrary g, including the empty scheme
and the identity, without any flatness of its structure-sheaf map. Additivity only
provides the termwise complex functor.
(blueprint: lem-pc-tensor-pullback-kflat-quasi-iso). -/
theorem tensorPullback_quasiIso_of_isKFlat {T S : Scheme.{u}} (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback g).Additive]
    {P Q : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
    (s : P ⟶ Q) (hP : CochainComplex.IsKFlat (R := S.sheaf) P)
    (hQ : CochainComplex.IsKFlat (R := S.sheaf) Q) (hs : QuasiIso s) :
    QuasiIso (((Scheme.Modules.tensorPullback g).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  sorry

end AlgebraicGeometry
