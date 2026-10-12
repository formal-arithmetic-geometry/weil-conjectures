/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DescendFinite
import Sheaf.AlgebraicGeometry.DescendSurjective
import Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FinitePresentationApproximation
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Noetherian factor for a finite surjective affine morphism

This packages the approximation and descent part of the proof of Stacks Lemma 01ZT.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation).
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- The finite surjective affine stage obtained by Noetherian approximation.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation). -/
structure NoetherianAffineFactor {X Y : Scheme.{u}} (f : X ⟶ Y) where
  Z : Scheme.{u}
  q : Y ⟶ Z
  W : Scheme.{u}
  g : W ⟶ Z
  affine_q : IsAffineHom q
  noetherian_Z : AlgebraicGeometry.IsNoetherian Z
  finite_g : IsFinite g
  surjective_g : Surjective g
  affine_W : IsAffine W

/-- A finite surjective map from an affine scheme admits a Noetherian affine stage.

Proof (the approximation portion of Stacks Lemma 01ZT):
1. The structure maps to Spec ℤ compose uniquely. Since X is affine it is quasi-compact
   and separated; surjectivity makes Y quasi-compact. Finiteness implies integrality and
   universal closedness, so separatedness descends to Y. Its closed diagonal is affine
   and quasi-compact, hence Y is quasi-separated
   [lem-weil-pbc-morphism-into-affine-scheme, lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-qcqs-over-affine, def-weil-surjective-morphism,
   lem-weil-pbc-finite-iff-integral-lft, pqf-lem-integral-univclosed,
   lem-weil-pbc-surjective-universally-closed-separated,
   lem-weil-pbc-closed-immersion-integral-separated-uc, def-weil-pbc-scheme-conventions].
2. Express the integral f as a directed limit of finite, finitely presented Y-schemes
   with affine transitions. These schemes are qcqs; since their limit X is affine,
   some stage is affine. Its map to Y is surjective since f factors through it.
   Replace X and f by that stage to assume finite presentation
   [lem-weil-pbc-integral-morphism-limit-of-finite, def-weil-finite-integral-morphism,
   lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence,
   lem-weil-pbc-limit-affine-stage, def-weil-surjective-morphism].
3. Approximate qcqs Y by schemes Y_i of finite type over ℤ with affine transitions,
   and reindex by a nonempty directed set. Each Y_i is Noetherian and qcqs
   [prop-nagata-noetherian-inverse-system, def-nagata-noetherian-inverse-system,
   lem-weil-pbc-cofiltered-limit-directed-reindex, lem-weil-pbc-finite-type-over-noetherian,
   pqf-def-locnoeth, lem-weil-pbc-locally-noetherian-quasi-separated].
4. Descend f to a finitely presented g₀ : X₀ → Y₀. Restrict to the cofinal tail and
   set X_i = X₀ ×_{Y₀} Y_i. These are qcqs with affine transitions, and their limit
   is X, compatibly with f
   [thm-pd-spreading-out, def-sbc-locally-finite-presentation, def-pc-fibre-product,
   lem-weil-pbc-colimit-initial-full-subcategory, lem-weil-pbc-scheme-over-limit,
   lem-weil-pbc-qcqs-morphism-permanence].
5. Descend finiteness of f to some g_i; finite presentation supplies local finite type.
   All later g_i are finite by base change
   [def-sbc-locally-finite-presentation, def-weil-finite-type-morphism,
   lem-weil-pbc-descend-finite, def-pc-fibre-product,
   lem-weil-pbc-finite-morphism-permanence].
6. Descend surjectivity of f to some g_i using local finite presentation. All later
   g_i are surjective by base change. This supplies a step implicit in Stacks' proof
   [lem-weil-pbc-descend-surjective, lem-weil-pbc-surjective-base-change].
7. Since the limit X is affine, the qcqs X_i are affine for all sufficiently large i
   [def-pc-scheme, lem-weil-pbc-limit-affine-stage].
8. Choose a common upper bound of the finiteness, surjectivity and affineness
   stages. Put Z = Y_i, W = X_i and g = g_i. Then Z is Noetherian, W is affine,
   and g is finite and surjective. The limit projection q : Y → Z is affine because
   all transition maps are affine [lem-weil-pbc-limit-affine-transition]. These
   objects and properties supply the factor. No affineness of Z is used here.
(blueprint: lem-weil-pbc-finite-surjective-affine-target-approximation). -/
theorem exists_noetherian_affine_factor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X] :
    Nonempty (NoetherianAffineFactor f) := by
  sorry

end AlgebraicGeometry
