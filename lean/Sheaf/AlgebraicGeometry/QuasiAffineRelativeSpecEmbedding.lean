/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps

/-!
# Quasi-affine morphisms as open subschemes of relative spectra

Source: Stacks Project, Morphisms, Tag 01SM, lemma-characterize-quasi-affine, (1) iff (3)
(blueprint: lem-trf-quasi-affine-relative-spec-embedding).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme morphism is quasi-affine exactly when it embeds by a quasi-compact open
immersion into the relative spectrum of a quasi-coherent algebra.
Source: Stacks Project, Morphisms, Tag 01SM, lemma-characterize-quasi-affine, (1) iff (3)
(blueprint: lem-trf-quasi-affine-relative-spec-embedding).

The relative spectrum of `A` is specified by an affine morphism `π : Y ⟶ S` and an
isomorphism `A ≅ π_* 𝒪_Y` of commutative `𝒪_S`-algebras. This characterizes the relative
spectrum up to isomorphism over `S` by `affine_morphism_relative_spec`, parts (2) and (3).
Here `Under.mk ⟨π.c⟩` is precisely that direct-image algebra, including its structure map.

Proof:
1. For each affine open U of S, X_U is quasi-affine, hence quasi-compact and separated
   by lem-trf-quasi-affine-canonical-affine-embedding. Thus f is quasi-compact
   (def-weil-finite-type-morphism). The maps X_U → U are quasi-separated by
   lem-weil-pbc-qcqs-morphism-permanence. Their diagonals cover the diagonal of f;
   lem-pc-quasi-compact-local-on-target makes that diagonal quasi-compact, so f is
   quasi-separated (def-weil-quasi-separated-morphism).
2. Set A = f_* 𝒪_X. The structure sheaf is quasi-coherent (pqf-def-coherent), and
   pqf-lem-pushforward-qcoh makes A.toModule quasi-coherent. Part (2) of
   lem-weil-pbc-affine-morphism-relative-spec gives π : Y = Spec_S A → S and
   α : A ≅ π_* 𝒪_Y, with the specified affine charts.
3. Apply lem-weil-pbc-affine-algebra-local-maps to π and α⁻¹. Its maps X_U → Y agree
   on overlaps, hence glue by lem-weil-pbc-scheme-morphism-gluing to c : X → Y over S.
   On U the section formula identifies c with the canonical map of X_U into the
   spectrum of its global sections, using lem-weil-pbc-morphism-into-affine-scheme.
4. Each restricted canonical map is an open immersion by
   lem-trf-quasi-affine-canonical-affine-embedding. The resulting maps X_U → Y are
   open immersions (def-weil-open-immersion). If c(x) = c(x'), choose an affine U
   around their common image in S; injectivity on X_U gives x = x'. Therefore
   lem-weil-pbc-open-immersion-injective-local-source makes c an open immersion.
5. Over each U, Y_U is affine and X_U is quasi-compact. By
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-morphism-permanence the map
   X_U → Y_U is quasi-compact. Apply lem-pc-quasi-compact-local-on-target to get
   quasi-compactness of c, without assuming S quasi-compact. Take i = c.
6. Conversely, for affine U in S, affineness of π identifies Y_U with an affine
   scheme. The equation i ≫ π = f identifies X_U with i⁻¹(Y_U). Restricting the
   open immersion i makes X_U an open subscheme of Y_U (def-weil-open-immersion).
   Quasi-compactness of i makes X_U quasi-compact (def-weil-finite-type-morphism).
   Thus f is quasi-affine by def-nagata-quasi-affine-morphism. -/
theorem isQuasiAffineHom_iff_exists_relativeSpec_embedding
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsQuasiAffineHom f ↔
      ∃ A : S.CommAlgebraSheaf, A.toModule.IsQuasicoherent ∧
        ∃ (Y : Scheme.{u}) (π : Y ⟶ S), IsAffineHom π ∧
          Nonempty (A ≅ Under.mk (⟨π.c⟩ : S.sheaf ⟶
            (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj Y.sheaf)) ∧
          ∃ i : X ⟶ Y, IsOpenImmersion i ∧ QuasiCompact i ∧ i ≫ π = f := by
  sorry

end AlgebraicGeometry
