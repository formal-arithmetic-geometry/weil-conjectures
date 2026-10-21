/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import WeilConjectures.RingTheory.FlatCompletion
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion
import Sheaf.TraceFormula.MultipointedCurve
import Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Field descent of semistability and geometric stability

Source: Temkin, *Stable modification of relative curves*, §1.2, printed p. 2,
and Remark 3.1.1(i)(a),(ii), printed pp. 14--15
(blueprint: lem-trf-stable-modification-stability-field-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.MultipointedPair

/--
Semistability and geometric stability of a compatible proper morphism of multipointed curves
are invariant under extension of the ground field.

Source: Temkin, *Stable modification of relative curves*, §1.2, printed p. 2, and
Remark 3.1.1(i)(a),(ii), printed pp. 14--15
(blueprint: lem-trf-stable-modification-stability-field-descent).

Proof (deferred).  Regard the field extension as the faithfully flat morphism
`Spec k' ⟶ Spec k` induced by `algebraMap k k'`.  Choose algebraic closures `a` of `k`
and `L` of `k'`; embed `a` in `L` over `k` and use the associativity of pullbacks to
identify the scalar extension of the `a`-geometric fibre with the `L`-geometric fibre
of the base-changed pair.  This gives the independence of the chosen closure and
identifies all markings and pair maps.

For ascent, apply the arbitrary-base-change theorem for semistable multipointed pairs;
it preserves the node completed-local-ring condition, etale marking, and inclusion in
the relative smooth locus.  Its compatible-morphism clause preserves the forbidden
component condition, giving both forward implications.

For descent of nodality, use the Fitting-ideal criterion for the nonsmooth locus of a
pure one-dimensional finite-type curve.  Kähler differentials and their Fitting ideals
commute with scalar extension.  At a closed nonsmooth point, the completed local rings
form a faithfully flat local extension with residue-field extension `L/a`.  Flat-local
depth and faithful-flat ideal contraction reflect the Jacobian ideal and depth.  The
formal quadratic criterion therefore gives a nondegenerate quadratic equation over `a`,
which factors into two independent linear forms (also in characteristic two), hence
`a[[u,v]]/(uv)`.  Jacobson density and faithful-flatness show every nonsmooth point is
closed, so all points are nodes.

The etale marking descends by fpqc descent.  The Fitting description of the nonsmooth
locus and surjectivity of faithfully flat scalar extension show that the marking stays
in the smooth locus.  This proves reverse semistability.  Finally, for a semistable
pair the marking and singular subscheme are finite unions of rational points.  Under an
extension of algebraically closed fields, irreducible components correspond, projective
line components descend by approximation of an isomorphism and its inverse, and a
contracted projective line remains contracted.  The special-point union has the same
incidence and cardinality on corresponding components, so an exceptional component
exists after extension exactly when it existed before.  This proves reverse geometric
stability and all closure-independence assertions.
-/
theorem stable_modification_stability_field_descent
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (Y X : MultipointedCurve (Spec (.of k)))
    (f : Y.Hom X)
    [IsProper f.curve] [IsProper f.marking] :
    (let P := MultipointedPair.ofCurve Y
     let Q := MultipointedPair.ofCurve X
     let g : Spec (.of k') ⟶ Spec (.of k) :=
       Spec.map (CommRingCat.ofHom (algebraMap k k'))
     let φ : P.curve ⟶ Q.curve := Over.homMk f.curve f.curve_over
     (P.IsSemistable ↔ (P.baseChange g).IsSemistable) ∧
       ((P.IsSemistable ∧ P.HasGeometricStability Q φ) ↔
         ((P.baseChange g).IsSemistable ∧
           (P.baseChange g).HasGeometricStability (Q.baseChange g)
             ((Over.pullback g).map φ)))) := by
  sorry

end AlgebraicGeometry.MultipointedPair
