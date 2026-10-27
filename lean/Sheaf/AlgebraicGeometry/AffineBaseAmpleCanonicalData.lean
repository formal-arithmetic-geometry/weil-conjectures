/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.TraceFormula.SpaceLineModuleProjMap
public import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing
import Sheaf.AlgebraicGeometry.AmpleProjLocalChart
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.AmplePullback

/-! # Canonical section-algebra data for an ample module over an affine base

Source: Stacks Project, Morphisms, Tag 01VJ, affine-base part of (3) implies (5);
Tags 01VI and 0892(2) (blueprint: lem-trf-affine-base-ample-canonical-data).

`RelativeSectionAlgebra` is the published affine-basis presentation of the canonical
quasi-coherent graded algebra: its homogeneous pieces are the actual direct-image
sections, with the tensor-power multiplication, unit, scalars and restriction maps.
Its evaluation uses the section-normalized tensor-pullback adjunction. The predicate
`IsCanonicalMap` fixes the morphism by the usual homogeneous-section chart formula.
The condition U(psi) = X is written out: at every point some positive-degree section on
an affine base neighbourhood generates the rank-one stalk of its tensor power.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Absolute ampleness over an affine base supplies the separated canonical Proj data.
The existential section algebra is specified by its actual homogeneous sections, and
the morphism is required to be the canonical evaluation morphism.

Source: Stacks Project, Morphisms, Tag 01VJ, affine-base (3) implies (5), Tag 01VI,
and Tag 0892(2), affine specialization
(blueprint: lem-trf-affine-base-ample-canonical-data).

Proof, following the node's five steps:
1. For every affine open W of T, its inclusion in the affine scheme T is affine
(lem-weil-pbc-morphism-affine-schemes-affine). Its inverse-image inclusion in X is
therefore affine (lem-weil-pbc-affine-morphism-permanence). Affine pullback preserves
ampleness (lem-weil-pbc-pullback-ample-invertible), and module pullback along this open
inclusion is restriction (def-pc-module-pullback). This gives the first clause.
2. X is absolutely separated by lem-weil-pbc-ample-scheme-separated. Cancellation
against the structure map of T gives IsSeparated f (lem-weil-pbc-separated-cancellation),
then lem-pc-separated-quasi-separated gives QuasiSeparated f.
3. Apply lem-trf-qcqs-line-section-algebra-evaluation to form the quasi-coherent graded
section algebra and its adjunction evaluation. Its degree-d sections on W are precisely
Gamma(f inverse-image W, L^d). Over T itself the relative Proj is the ordinary Proj of
the global section ring. Its generation locus is the union of all positive-degree
nonvanishing section opens. Ampleness makes this union X. The affine identification
identifies its canonical morphism with the identity-section-ring morphism.
4. Positive-degree sections having affine nonvanishing locus cover X. By
lem-sc-ample-proj-local-chart the inverse image of D_+(s) is X_s for every positive-degree
section, and the restriction to an affine X_s is an isomorphism. Thus the image is the
union V of the corresponding standard opens in Proj of the section ring.
5. If two points have the same image, a covering chart containing one contains both;
its isomorphism makes them equal. The chart inverses agree on overlaps, since each
is the inverse to the same restricted canonical map. They glue by
lem-weil-pbc-scheme-morphism-gluing to an inverse V to X. The two inverse identities
hold on these covers and hence globally. Thus the canonical map identifies X with
the open subscheme V, so is an open immersion (def-weil-open-immersion). -/
theorem affine_base_ample_canonical_data {X T : Scheme.{u}} (f : X ⟶ T)
    [QuasiCompact f] [IsAffine T] (L : X.Modules) [L.IsInvertible] (hL : IsAmple X L) :
    (∀ W : T.Opens, IsAffineOpen W →
      ∃ h : ((tensorPullback (f ⁻¹ᵁ W).ι).obj L).IsInvertible,
        @IsAmple (f ⁻¹ᵁ W).toScheme ((tensorPullback (f ⁻¹ᵁ W).ι).obj L) h) ∧
    IsSeparated f ∧ QuasiSeparated f ∧
    ∃ A : RelativeSectionAlgebra f L,
      (∀ x : X, ∃ (V : T.affineOpens) (hx : x ∈ f ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
        ∃ a : A.data.grading V n,
          (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (f ⁻¹ᵁ V.1) x hx)
              (A.sectionEquiv V n a) ∉
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
              (⊤ : Submodule (X.presheaf.stalk x)
                ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))) ∧
      ∃ r : X ⟶ A.data.relProj, A.IsCanonicalMap r ∧ IsOpenImmersion r := by
  sorry

end AlgebraicGeometry.Scheme.Modules
