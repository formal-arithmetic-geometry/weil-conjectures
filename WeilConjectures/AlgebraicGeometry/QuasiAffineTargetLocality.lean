/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.CoherentFiniteType

/-!
# Quasi-affineness on an affine open cover of the target

Source: Stacks Project, Morphisms, Tag 01SM, lemma-characterize-quasi-affine, (1) iff (2)
(blueprint: lem-a1-quasi-affine-target-locality).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Quasi-affineness of a scheme morphism can be checked on any affine open cover of its target.
Source: Stacks Project, Morphisms, Tag 01SM, lemma-characterize-quasi-affine, (1) iff (2)
(blueprint: lem-a1-quasi-affine-target-locality).

Here `Scheme.IsQuasiAffine` includes quasi-compactness and is equivalent to being isomorphic
to a quasi-compact open subscheme of an affine scheme. The target need not be quasi-compact
or separated, and the morphism need not be of finite type.

Proof:
1. If h is quasi-affine, the inverse image of each affine open U a is quasi-affine by
   def-nagata-quasi-affine-morphism.
2. Conversely, set Z_a = h⁻¹(U a). Each Z_a is quasi-compact and quasi-separated by
   lem-trf-quasi-affine-canonical-affine-embedding. Since U a is affine, use
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qcqs-morphism-permanence to obtain
   quasi-compactness of Z_a → U a. Apply lem-pc-quasi-compact-local-on-target to h.
   The opens Z_a ×_(U a) Z_a cover Z ×_S Z (def-pc-fibre-product), and the restriction
   of the diagonal there is the diagonal of Z_a → U a. The maps Z_a → U a are
   quasi-separated by lem-weil-pbc-qcqs-morphism-permanence. Apply the same locality
   criterion to the diagonal to obtain quasi-separatedness of h
   (def-weil-quasi-separated-morphism). An empty cover forces S and Z to be empty.
3. The algebra A = h_* O_Z is quasi-coherent by pqf-lem-pushforward-qcoh, using the
   quasi-coherence of O_Z (pqf-def-coherent). Apply
   lem-weil-pbc-affine-morphism-relative-spec to obtain π : Y = Spec_S A → S, an
   isomorphism α : A ≅ π_* O_Y, and affine charts Y_a = π⁻¹(U a) = Spec A(U a).
4. Apply lem-weil-pbc-affine-algebra-local-maps to α⁻¹ to obtain maps Z_a → Y over S
   agreeing on overlaps. Glue them by lem-weil-pbc-scheme-morphism-gluing to c : Z → Y
   with c ≫ π = h. On U a, the induced global-sections map is α_a⁻¹ α_a = id, so
   lem-weil-pbc-morphism-into-affine-scheme identifies Z_a → Y_a with its canonical
   map into the spectrum of its global sections.
5. Each chart map is an open immersion by lem-trf-quasi-affine-canonical-affine-embedding
   and def-weil-open-immersion. If c(z) = c(z'), choose a chart U a containing π(c(z));
   both points lie in Z_a since c ≫ π = h, and injectivity on that chart gives z = z'.
   Thus lem-weil-pbc-open-immersion-injective-local-source makes c an open immersion.
   Each Z_a → Y_a is quasi-compact by lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-morphism-permanence. Apply lem-pc-quasi-compact-local-on-target
   to c and the affine cover Y_a to obtain quasi-compactness of c.
6. For any affine open V of S, lem-weil-pbc-affine-morphism-relative-spec makes Y_V
   affine. The equality c ≫ π = h identifies h⁻¹(V) with c⁻¹(Y_V), a quasi-compact
   open subscheme of Y_V (def-weil-open-immersion, def-weil-finite-type-morphism).
   By def-nagata-quasi-affine-morphism, h is quasi-affine. -/
theorem isQuasiAffineHom_iff_of_affine_open_cover
    {Z S : Scheme.{u}} (h : Z ⟶ S) {A : Type v} (U : A → S.Opens)
    (hU : ∀ a : A, IsAffineOpen (U a)) (hcover : iSup U = ⊤) :
    IsQuasiAffineHom h ↔ ∀ a : A, (h ⁻¹ᵁ U a).toScheme.IsQuasiAffine := by
  sorry

end AlgebraicGeometry
