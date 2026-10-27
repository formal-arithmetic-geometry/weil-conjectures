/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.AlgebraicGeometry.PlaneHypersurfaceCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Geometric integrality and genus of a smooth plane hypersurface

Source: Stacks Project, Tags 0BYA and 0BYD, plane curves and lemma-genus-plane-curve;
Tag 056T, smooth geometric normality.
(blueprint: lem-sfb-smooth-plane-hypersurface-geometric-genus)

The scheme, its closed immersion, scalar map and module cohomology are the canonical
constructions of `PlaneHypersurfaceCohomology`. The coefficient-image hypersurface
is identified over the extension field with the scheme-theoretic base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PlaneHypersurface

/-- A smooth positive-degree plane hypersurface is geometrically integral. After every
field extension its coefficient-image equation presents its base change, its only global
functions are scalars, its local rings are integrally closed domains, and it is a smooth
H-projective geometrically integral curve of genus (d-1)(d-2)/2.
The displayed isomorphism is over Spec L; all subsequent clauses concern that explicit
closed hypersurface model of the base change. `ConnectedSpace` includes nonemptiness.
The genus is the recorded `Scheme.arithmeticGenus`, and the cardinal-valued dimension
also records that H^1 is finite-dimensional. No rational point is chosen.
Source: Stacks 0BYA, 0BYD (lemma-genus-plane-curve), and 056T.
(blueprint: lem-sfb-smooth-plane-hypersurface-geometric-genus)

Proof, following the six DAG steps:
1. For L/k, the coefficient image F_L is nonzero since k -> L is injective, and
   `hF.map` gives homogeneity of the same degree. Apply
   lemma-nagata-relative-proj-base-change-arbitrary to the graded quotient algebra.
   The graded algebra isomorphism L tensor_k (k[A,B,C]/(F)) -> L[A,B,C]/(F_L)
   sends l tensor P to l P_L. Its inverse sends scalars to l tensor 1 and each
   variable to 1 tensor its quotient class. It kills F_L, and both composites
   fix scalars and variables. Proj gives the displayed isomorphism over Spec L.
   The quotient closed immersion is that of
   lem-sfb-projective-hypersurface-structure-sequence, n=2, and the existing `ι`.
2. Apply lem-sfb-plane-hypersurface-cohomology over L. It gives bijectivity of
   the actual scalar ring map and the displayed H^1 dimension, without a point
   or algebraic closedness assumption.
3. The empty scheme has zero global ring, whereas the scalar map identifies it
   with the nonzero field L, so the hypersurface is nonempty. A decomposition
   into two nonempty disjoint opens gives a global idempotent by gluing 0 and 1.
   Its germs in the nonzero local rings show that it differs from 0 and 1.
   This contradicts the absence of nontrivial idempotents in L; hence connectedness.
4. Base change preserves smoothness of relative dimension one by
   lem-sbc-smooth-relative-dimension-permanence. For every M/L, iterated base
   change (def-pc-base-change) identifies this further base change with Z_M.
   Step 3 for M/k proves geometric connectedness over L.
5. Apply lem-sbc-smooth-connected-generic-geometry-core over Spec L. Its base
   is integral with integrally closed field local ring; steps 3 and 4 give
   nonemptiness, smoothness and geometrically connected fibre. The generic fibre
   is the hypersurface itself, so it is integral and its local rings are
   integrally closed domains. For arbitrary L/k this proves geometric integrality
   of Z, and for all composites M/k it proves geometric integrality over L.
6. The closed immersion is into Proj L[A,B,C]. Relative-Proj base change for
   Z[A,B,C] identifies this with the projective plane over Spec L, proving
   H-projectivity (def-kun-projective). By lem-kun-projective-implies-proper
   it is proper, hence separated and of finite type, and quasi-compact.
   Smooth relative dimension one and nonemptiness give dimension one, since
   Spec L has one point. With step 5 this is an integral smooth projective curve
   (def-pc-smooth-projective-curve). Its genus (def-pc-genus) is dim H^1(O),
   computed in step 2 using def-sc-ringed-space-module-cohomology. -/
theorem geometric_genus_of_smooth {k : Type u} [Field k]
    (d : ℕ) (hd : 1 ≤ d) (F : MvPolynomial (ULift.{u} (Fin 3)) k)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hsmooth : SmoothOfRelativeDimension 1 (π d F hF)) :
    GeometricallyIntegral (π d F hF) ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        ∃ e : pullback (π d F hF) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≅
            scheme d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L)),
          e.hom ≫ π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L)) =
              pullback.snd (π d F hF) (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧
          IsClosedImmersion
            (ι d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          Function.Bijective
            (scalarMap d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          ConnectedSpace
            (scheme d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          (∀ x : scheme d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L)),
            IsDomain ((scheme d (MvPolynomial.map (algebraMap k L) F)
              (hF.map (algebraMap k L))).presheaf.stalk x) ∧
            IsIntegrallyClosed ((scheme d (MvPolynomial.map (algebraMap k L) F)
              (hF.map (algebraMap k L))).presheaf.stalk x)) ∧
          SmoothOfRelativeDimension 1
            (π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          IsHProjective
            (π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          GeometricallyIntegral
            (π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          IsSmoothProjectiveCurve
            (π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))) ∧
          (@Scheme.arithmeticGenus L _
              (scheme d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L)))
              ⟨π d (MvPolynomial.map (algebraMap k L) F) (hF.map (algebraMap k L))⟩ :
            Cardinal.{u}) =
            Module.rank L
              (cohomology d (MvPolynomial.map (algebraMap k L) F)
                (hF.map (algebraMap k L)) 1) ∧
          Module.rank L
              (cohomology d (MvPolynomial.map (algebraMap k L) F)
                (hF.map (algebraMap k L)) 1) =
            (((d - 1) * (d - 2) / 2 : ℕ) : Cardinal.{u}) := by
  sorry

end AlgebraicGeometry.PlaneHypersurface
