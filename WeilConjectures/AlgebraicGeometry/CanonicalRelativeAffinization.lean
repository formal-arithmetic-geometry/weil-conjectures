/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Gluing

/-! # The canonical relative affinization morphism

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism
(blueprint: lem-sfb-canonical-relative-affinization).

The relative spectrum is expressed using its existing affine-morphism presentation:
an affine `g : Y ⟶ S` with an algebra isomorphism `α : f_* 𝒪_X ≅ g_* 𝒪_Y`.
The theorem applies to every such presentation, in particular the quasi-inverse and
counit of `affine_morphism_relative_spec`. Its canonical affine-base chart is
`(g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U))`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- For a qcqs morphism, the direct image structure algebra is quasi-coherent and
there is a unique morphism to its relative spectrum over the base whose expression
in every affine-base chart is the absolute affinization map.

Source: Stacks Project, Constructions, Tag 01LY, lemma-canonical-morphism
(blueprint: lem-sfb-canonical-relative-affinization).

Proof:
1. The structure module is quasi-coherent (pqf-def-coherent). Apply the qcqs
   pushforward theorem (pqf-lem-pushforward-qcoh) to obtain quasi-coherence of the
   algebra with sections Γ(f⁻¹ V, 𝒪_X) and structure map f♯. The relative-spectrum
   theorem (lem-weil-pbc-affine-morphism-relative-spec) supplies an affine g and α;
   its chart over each affine U is the map induced by α_U.
2. By morphisms into an affine scheme (lem-weil-pbc-morphism-into-affine-scheme),
   the identity of Γ(f⁻¹ U, 𝒪_X) gives the absolute affinization map. Compose with
   the inverse of the chart to get c_U. The algebra compatibility of α says that
   g c_U and f agree on sections, hence agree as maps to the affine U.
3. For nested affine opens W ⊆ U, naturality of α makes both local maps correspond
   to the restriction homomorphism A(U) → A(W), so the affine-target bijection
   identifies them. Refine the intersection of any two affine opens by affine
   opens W and use scheme-morphism gluing (lem-weil-pbc-scheme-morphism-gluing)
   to identify the two maps there; the intersection need not be affine.
4. Glue the c_U over all affine opens of S. Their composites to S are f, and their
   chart formulas are the required ones. Any other map with these formulas agrees
   on each f⁻¹ U, since the charts are isomorphisms, and hence agrees globally by
   uniqueness in the same gluing theorem. Empty schemes are included. -/
theorem canonical_relative_affinization
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    (Scheme.CommAlgebraSheaf.toModule
      (Under.mk (⟨f.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf))).IsQuasicoherent ∧
    ∀ {Y : Scheme.{u}} (g : Y ⟶ S) [IsAffineHom g]
      (α : (Under.mk (⟨f.c⟩ : S.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) :
            S.CommAlgebraSheaf) ≅
        (Under.mk (⟨g.c⟩ : S.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf) :
            S.CommAlgebraSheaf)),
      ∃! c : X ⟶ Y, ∃ hc : c ≫ g = f,
        ∀ U : S.Opens, IsAffineOpen U →
          c.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
              (by rw [← Scheme.Hom.comp_preimage, hc]) ≫
            (g ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (α.hom.right.hom.app (op U)) =
          (f ⁻¹ᵁ U).toSpecΓ := by
  sorry

end AlgebraicGeometry
