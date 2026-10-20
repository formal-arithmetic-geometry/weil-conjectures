/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
import Sheaf.CategoryTheory.SiteModuleSheafGluing
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree


/-! # Projective bundles on frame charts

Source: Stacks Project, Tags 01OB, 01O3, 01OE.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

/-- A symmetric-algebra projective bundle with its normalized quotient and charts for
all frames. Properness, invertibility, and base-change coherence are separate consequences.
Source: Stacks Project, Tags 01OB and 01OE
(blueprint: lem-pur-projective-bundle-frame-models). -/
structure ProjectiveBundleFrameModels (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e

/-- Existence of the frame models, without the properness or coherence conclusions.
Source: Stacks Project, Constructions, Tags 01OB, 01OE, 01NR, 01MN and 01MS;
steps 1--4 of lem-pur-projective-bundle-tautological-geometry.
(blueprint: lem-pur-projective-bundle-frame-models).

Proof: on every affine base open take the symmetric algebra of module sections.
Use the symmetric-degree grading and the coefficientwise restriction maps; the
symmetric-algebra base-change isomorphism gives quasi-coherence in every degree.
Relative Proj glues these affine Proj schemes. On each standard open D_+(f), glue
the degree-one localized modules by a/f^m mapping to the same homogeneous fraction
on refinements. The identity and triple-overlap equations follow by composing the
coefficient maps. The module-sheaf gluing theorem gives L and its affine twist charts.
The local maps sending v to iota(v)/1 agree with restriction and give the quotient
by pullback adjunction. Their generator equations hold by their definition.
For any frame on an open U, the symmetric universal property identifies its
algebra with the polynomial algebra, preserving every degree. Relative Proj
functoriality gives the relative and polynomial charts over U. The degree-one
fraction maps identify their twists and carry T_i to the frame quotient. On
D_+(T_i), multiplication by T_i identifies degree zero with degree one, and the
inverse divides by T_i. Thus the specified section is a free generator. On an
overlap T_i=(T_i/T_j)T_j, giving exactly the transition field. The constructions
agree on affine refinements of nonaffine overlaps, so apply to every frame on U.
Make these choices simultaneously for all B,F of the stipulated rank. The empty
base has empty charts and the same gluing argument applies. -/
theorem exists_projectiveBundleFrameModels (n : ℕ) :
    Nonempty (ProjectiveBundleFrameModels.{u} n) := by
  sorry

end AlgebraicGeometry
