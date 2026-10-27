/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.RelativelyVeryAmple
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs

/-!
# Finite-type realization of a relatively very ample module

Source: Stacks Project, Morphisms, Tag 07RM, the finite-type approximation and immersion
construction in the proof of lemma-quasi-projective-open-projective, after choosing a
relatively very ample power (blueprint: lem-sfb-very-ample-finite-type-realization).

The normalized tautological quotient supplies the canonical degree-one twist on the
projective bundle of the finite-type quasi-coherent module.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A relatively very ample invertible module on a finite-type scheme over a qcqs base
is the pullback of the degree-one twist along an immersion into a projective bundle of
a finite-type quasi-coherent module. The twist is normalized by its tautological quotient.

Source: Stacks Project, Morphisms, Tag 07RM, proof of
lemma-quasi-projective-open-projective, finite-type realization before compactification
(blueprint: lem-sfb-very-ample-finite-type-realization).

Proof, following the node's nine steps:
1. Finite type makes f quasi-compact (def-weil-finite-type-morphism). Relative very
ampleness makes f quasi-separated by the independent final clause of
lem-trf-relative-ample-very-ample. Invertibility makes N quasi-coherent
(def-sc-invertible-module), so pqf-lem-pushforward-qcoh makes F = f_*N quasi-coherent.
2. Apply lem-weil-pbc-module-directed-colimit-finite-presentation on S to express F as a
nonempty directed colimit of finitely presented E_i. The stages are quasi-coherent by
lem-weil-pbc-quasi-coherent-finite-type-affine and finite type by pqf-def-coherent:
a finite presentation includes a finite generating surjection.
3. Choose a finite affine cover V_j of S by lem-weil-pbc-qcqs-finite-affine-open-cover.
Finite type restricts to each X_j = f^{-1}V_j. Restrict the very ample witness using
lem-weil-pbc-immersion-base-change-lft, the open compatibility of
lem-trf-projective-bundle-quotient-geometry, and def-pc-module-pullback.
4. Apply lem-sfb-very-ample-affine-finite-sections on each V_j. Obtain finitely many
sections s_{j,t} generating N on X_j and classifying an immersion into projective space.
They are sections of F on V_j by lem-pc-module-pullback-adjunction's pushforward.
5. Lift every s_{j,t}, including t = 0, by
lem-weil-pbc-quasi-coherent-module-colimit-affine-sections. Directedness and finiteness
put all lifts e_{j,t} in one stage E = E_i; nonemptiness handles an empty covering.
6. The adjoint of E to F is psi : f^*E to N, by lem-pc-module-pullback-adjunction.
Its local formula sends 1 tensor e_{j,t} to s_{j,t}; hence it is surjective on every
stalk. The quotient classification of lem-trf-projective-bundle-quotient-geometry gives
r over S and a quotient-compatible isomorphism from r^*O(1) to N.
7. On P(E)|V_j the finitely many e_{j,t} generate the tautological line on an open W_j:
in a frame the locus is the union of the principal opens of their coefficients. This
is independent of frame. The quotient geometry gives W_j to projective n_j-space.
8. The pulled-back quotient shows r(X_j) lies in W_j and r^{-1}(W_j) = X_j. Naturality
and injectivity in lem-trf-projective-bundle-quotient-geometry identify the composite
with the immersion of step 4. Apply lem-zl-immersion-cancellation to X_j to W_j.
9. The opens W_j cover the image of r. Apply lem-zl-immersion-near-image-locality to
get IsImmersion r. Step 2 gives the required finite-type quasi-coherent E, and step 6
gives the twist isomorphism. If S is empty, X is empty and the empty image cover works. -/
theorem veryAmple_finiteType_realization {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace S] [QuasiSeparatedSpace S]
    (N : X.Modules) [N.IsInvertible] (hN : IsRelativelyVeryAmple f N) :
    ∃ (E : S.Modules) (hE : E.IsQuasicoherent), E.IsFiniteType ∧
      ∃ (D : @ProjectiveBundleQuotientGeometry.TautologicalQuotient S E hE)
        (r : X ⟶ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProj),
        IsImmersion r ∧
        r ≫ (@SymmetricAlgebraSheaf.gradedAlgebraData S E hE).relProjHom = f ∧
        Nonempty ((tensorPullback r).obj D.line ≅ N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
