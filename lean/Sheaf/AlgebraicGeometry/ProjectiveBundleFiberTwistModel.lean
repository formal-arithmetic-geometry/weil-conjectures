/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientData
public import Sheaf.AlgebraicGeometry.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# A standard model of a projective-bundle fibre with its tautological line

Source: Stacks Project, Constructions, Tags 01OA and 01OE;
EGA II, Remark 4.2.7, residue-field normalization.
(blueprint: lem-sfb-projective-bundle-fiber-twist-model)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

/-- A basis of E at s identifies the scheme-theoretic fibre with standard
projective space and the pulled-back normalized line with the standard degree-one
twist. There is no assertion about arbitrary invertible modules or other powers.

Source: Stacks Project, Constructions, Tags 01OA and 01OE; EGA II,
Remark 4.2.7, field normalization; the tensor-power convention is Tag 01CR.
(blueprint: lem-sfb-projective-bundle-fiber-twist-model)

Proof: Choose a trivializing neighbourhood of s for the rank-r module E. Pull
that frame back to Spec kappa(s), obtaining an ordered basis of its rank-r
vector space. Tensor pullback of the universal invertible quotient represents
quotients of this vector space: tensor-pullback adjunction, composition and the
quotient classification identify this representing scheme with the fibre.
The symmetric algebra of the ordered free module is kappa(s)[T_0,...,T_(r-1)].
The free comparison identifies its projective bundle with standard projective
space. On an affine base chart the normalization in D.chart and D.generator
identifies D.line with the degree-one polynomial twist, preserving the quotient.
These comparisons agree on the homogeneous standard charts and hence glue.
Compose their inverses to obtain e from standard projective space to the fibre.
A base point s ensures a nonempty residue
field spectrum; neither a reduced base nor a globally chosen frame is needed. -/
theorem exists_projective_bundle_fiber_twist_model (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E) (s : S) :
    ∃ e : ℙ(ULift.{u} (Fin r); Spec (.of (S.residueField s))) ≅
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiber s,
      Nonempty
        ((tensorPullback e.hom).obj
          ((tensorPullback
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj D.line) ≅
          ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of (S.residueField s))) 1) :=
  by sorry

end AlgebraicGeometry.ProjectiveBundlePicardClassification
