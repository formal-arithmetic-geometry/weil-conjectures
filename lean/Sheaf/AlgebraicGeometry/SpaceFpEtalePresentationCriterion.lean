/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover

/-! # Finite presentation detected by an étale scheme presentation

Source: Stacks Project, Spaces, Properties, Tag 03H6; Morphisms of Spaces, Tags 06G5,
073B, 0410(6), 084P; Properties of Spaces, Tag 07S4; Limits of Spaces, Tag 07SK,
first paragraph (blueprint: lem-sfb-fp-etale-presentation-criterion).

The relation scheme is specified by its actual Yoneda pullback square. Scheme finite
presentation is the conjunction of local finite presentation, quasi-compactness and
quasi-separatedness, as in Tag 01TP.

## Main statements

* `fp_iff_etale_scheme_presentation`: the equivalence for an arbitrary scheme atlas.
* `exists_affine_fp_etale_presentation`: the affine choice under finite presentation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over an affine scheme, finite presentation is equivalent to the existence of an
étale surjective scheme atlas whose source and relation are finitely presented over the base.
The square identifies `R` with `W ×_Y W`, and the map from `R` to `T` is induced by
its first projection; the pullback identity identifies it with that from the second.

Source: Stacks Project, Tags 03H6, 06G5, 073B, 0410(6), 084P, 07S4; Tag 07SK,
first paragraph (blueprint: lem-sfb-fp-etale-presentation-criterion).

Proof: (1) If Y → T is finitely presented, the affine base is qcqs
[lem-weil-pbc-affine-scheme-qcqs]. Hence Y is qcqs [lem-sfb-space-fp-qcqs-source].
Choose an affine surjective étale atlas W → Y [lem-sfb-qc-space-affine-etale-atlas].
The identity target chart gives local finite presentation of W → T
[lem-sfb-space-local-properties-chart-test]; affine scheme qcqs and morphism permanence
supply its quasi-compactness and quasi-separatedness
[lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-morphism-permanence].
(2) Representability of the diagonal makes R = W ×_Y W a scheme, and its projection
is étale [def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers].
R is qcqs [lem-sfb-qcqs-space-fibre-product]. Étaleness and composition give local
finite presentation of R → T [def-weil-etale-morphism,
lem-sbc-locally-finite-presentation-composition]; scheme permanence gives its other
finiteness conditions [lem-weil-pbc-qcqs-morphism-permanence].
(3) Conversely W and R are qcqs over the affine base [lem-weil-pbc-qcqs-over-affine].
The projection R → W is quasi-compact by scheme permanence
[lem-weil-pbc-qcqs-morphism-permanence], so Y is quasi-separated
[lem-sfb-space-qs-atlas-criterion].
(4) The atlas induces a continuous surjection on points
[lem-a1-space-affine-etale-cover, def-trf-algebraic-space]. Pull an open cover back
to W, take a finite subcover, and use surjectivity to see that it covers Y. Thus Y is qc.
(5) The identity target chart detects local finite presentation of Y → T
[lem-sfb-space-local-properties-chart-test]. Absolute qcqs and the affine target imply
relative qcqs [lem-sfb-space-qcqs-permanence]. These are precisely finite presentation. -/
theorem fp_iff_etale_scheme_presentation {S : Scheme.{u}}
    (T : Over S) [IsAffine T.left] (Y : AlgebraicSpace S)
    (f : Y.obj.obj ⟶ yoneda.obj T) :
    (MapIsQuasiCompact f ∧ MapIsQuasiCompact (pullback.diagonal f) ∧
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y T f) ↔
    ∃ (W : Over S) (q : yoneda.obj W ⟶ Y.obj.obj),
      IsEtale q ∧ IsSurjective q ∧
      (LocallyOfFinitePresentation (yoneda.preimage (q ≫ f)).left ∧
        QuasiCompact (yoneda.preimage (q ≫ f)).left ∧
        QuasiSeparated (yoneda.preimage (q ≫ f)).left) ∧
      ∃ (R : Over S) (p₁ p₂ : R ⟶ W),
        IsPullback (yoneda.map p₁) (yoneda.map p₂) q q ∧
        LocallyOfFinitePresentation (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) ∧
        QuasiCompact (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) ∧
        QuasiSeparated (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) := by
  sorry

/-- Under finite presentation the atlas in the presentation criterion can be chosen affine.
Source: Stacks Project, Tags 03H6, 06G5, 073B, 0410(6), 084P; Tag 07SK, first paragraph
(blueprint: lem-sfb-fp-etale-presentation-criterion).

Proof: apply steps (1) and (2) of the node's proof. The affine scheme T is qcqs
[lem-weil-pbc-affine-scheme-qcqs], hence Y is qcqs [lem-sfb-space-fp-qcqs-source].
The affine atlas is supplied by [lem-sfb-qc-space-affine-etale-atlas]. Its structure map
is locally finitely presented by the identity-target chart test
[lem-sfb-space-local-properties-chart-test] and is qcqs by affine scheme permanence
[lem-weil-pbc-qcqs-morphism-permanence]. Representability gives the actual scheme
R = W ×_Y W with étale first projection [def-trf-algebraic-space,
lem-trf-space-fibre-products-etale-covers]. It is qcqs
[lem-sfb-qcqs-space-fibre-product]. Étaleness followed by composition gives its local
finite presentation over T [def-weil-etale-morphism,
lem-sbc-locally-finite-presentation-composition]; scheme permanence supplies qcqs.
The same affine W therefore has both required finite-presentation properties. -/
theorem exists_affine_fp_etale_presentation {S : Scheme.{u}}
    (T : Over S) [IsAffine T.left] (Y : AlgebraicSpace S)
    (f : Y.obj.obj ⟶ yoneda.obj T)
    (hf : MapIsQuasiCompact f ∧ MapIsQuasiCompact (pullback.diagonal f) ∧
      MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y T f) :
    ∃ (W : Over S) (q : yoneda.obj W ⟶ Y.obj.obj),
      IsAffine W.left ∧ IsEtale q ∧ IsSurjective q ∧
      (LocallyOfFinitePresentation (yoneda.preimage (q ≫ f)).left ∧
        QuasiCompact (yoneda.preimage (q ≫ f)).left ∧
        QuasiSeparated (yoneda.preimage (q ≫ f)).left) ∧
      ∃ (R : Over S) (p₁ p₂ : R ⟶ W),
        IsPullback (yoneda.map p₁) (yoneda.map p₂) q q ∧
        LocallyOfFinitePresentation (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) ∧
        QuasiCompact (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) ∧
        QuasiSeparated (p₁.left ≫ (yoneda.preimage (q ≫ f)).left) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
