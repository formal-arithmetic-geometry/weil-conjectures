/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.SchemeLimitIsomorphismDescent
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting

/-! # Representable isomorphisms descend along algebraic-space limits

Source: Stacks Project, Limits of Algebraic Spaces, Tag 084S (lemma-descend-equality),
in Situation 084R (situation-descent)
(blueprint: lem-sfb-space-limit-representable-isomorphism).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finitely presented map between qcqs spaces representable over one stage
is an isomorphism at a later stage if its base change to the fppf sheaf limit is one.
The atlas conditions express quasi-compactness, and quasi-separatedness is absolute.

Source: Stacks Project, Limits of Algebraic Spaces, Tag 084S, Situation 084R
(blueprint: lem-sfb-space-limit-representable-isomorphism).

Proof:
1. Restrict to the cofinal directed tail above i₀. A compatible family on this tail
   extends uniquely to the whole system by projecting from a common upper bound;
   therefore the specified sheaf limit is unchanged. Choose an affine surjective
   etale chart U₀ of Xᵢ₀ by [lem-trf-space-qc-finite-affine-atlas-refinement]. Its
   pullbacks Uᵢ are affine schemes, by representability and affineness of transitions,
   and remain surjective etale charts by [lem-trf-space-fibre-products-etale-covers].
2. The affine-transition scheme limit L of the Uᵢ exists by
   [lem-weil-pbc-limit-affine-transition]. On every test scheme its points are exactly
   a compatible family in the Xᵢ together with a matching U₀-point. This identifies
   h_L naturally with X ×_{Xᵢ₀} U₀, respecting all specified projections.
3. Representability makes P₀ = Y₀ ×_{Xᵢ₀} U₀ and Q₀ = T₀ ×_{Xᵢ₀} U₀ schemes.
   They are qcqs by [lem-sfb-space-qcqs-source-products] and
   [lem-weil-pbc-affine-scheme-qcqs]. Apply [lem-sfb-space-local-properties-chart-test]
   with target chart Q₀ and identity source chart P₀ to see that P₀ → Q₀ is locally
   of finite presentation.
4. Its limit base change is an isomorphism, being a pullback of the assumed one.
   Apply [lem-sfb-scheme-limit-isomorphism-descent] to the qcqs affine system Uᵢ.
   It gives i ≥ i₀ where P₀ ×_{U₀} Uᵢ → Q₀ ×_{U₀} Uᵢ is an isomorphism.
   Pullback associativity identifies this with the pullback of gᵢ along Uᵢ → Xᵢ.
5. For every test scheme and every Tᵢ-section, use
   [lem-a1-representable-etale-fppf-local-lifting] to lift its Xᵢ-image to Uᵢ on an
   fppf cover. The local inverse gives a unique Yᵢ-lift there. On double overlaps
   compare both lifts using the same Uᵢ-lift; invertibility on that chart forces
   equality. The fppf sheaf condition glues the lift uniquely. Uniqueness makes
   these bijections natural in the test scheme, yielding the inverse of gᵢ.
-/
theorem exists_isIso_representable_stage_of_fppf_limit
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hqc : ∀ i : Iᵒᵖ, ∃ (U : Over S) (a : yoneda.obj U ⟶ (D.obj i).obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))
    (haff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map a).hom.hom)
    (c : Cone D) (hc : IsLimit ((ObjectProperty.ι _).mapCone c)) (i₀ : I)
    (Y₀ T₀ : Over (D.obj (op i₀))) (g₀ : Y₀ ⟶ T₀)
    (hYrep : IsRepresentable Y₀.hom.hom.hom)
    (hTrep : IsRepresentable T₀.hom.hom.hom)
    (hYqc : ∃ (U : Over S) (a : yoneda.obj U ⟶ Y₀.left.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hYqs : IsAbsolutelyQuasiSeparated Y₀.left)
    (hTqc : ∃ (U : Over S) (a : yoneda.obj U ⟶ T₀.left.obj.obj),
      CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a)
    (hTqs : IsAbsolutelyQuasiSeparated T₀.left)
    (hlfp : MapIsLocallyOfFinitePresentation g₀.left)
    (hX : IsIso (((Over.pullback (c.π.app (op i₀)).hom).map
      ((Over.post (ObjectProperty.ι _)).map g₀)).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      IsIso (((Over.pullback (D.map (homOfLE hi).op).hom).map
        ((Over.post (ObjectProperty.ι _)).map g₀)).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
