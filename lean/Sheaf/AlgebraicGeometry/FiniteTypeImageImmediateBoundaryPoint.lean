/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Constructible
import Mathlib.Topology.Spectral.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Maximal
import WeilConjectures.Topology.ProconstructibleClosureSpecialization
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
public import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso

/-! # Immediate generalizations in a nonclosed finite-type image

Source: Stacks Project, Limits, Tag 0GWV, proof, the paragraph beginning
"Assume S and Y affine" and the following definition of T, specialized to Spec k
(blueprint: lem-sfb-finite-type-image-immediate-boundary-point).

The ideal `I` in the conclusion is fixed by equality to the vanishing ideal of the
point closure. Thus `I.subscheme` is the actual reduced induced closed subscheme.
The factorization uses the inverse of its closed immersion's residue-field map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A nonclosed image of a closed subset has a missing closed boundary point with
an immediate generalization in the image and a finite residue-field lift.
Source: Stacks Project, Limits, Tag 0GWV, proof, the two paragraphs choosing y,t,x
and defining T, specialized to S = Spec k
(blueprint: lem-sfb-finite-type-image-immediate-boundary-point).

Proof plan:
1. The affine-pairs criterion (lem-weil-pbc-lft-affine-pairs) makes the affine
coordinate rings of X and Y finite type over k. Generators over k also generate
an X-chart over a Y-chart, since f is a k-morphism. Thus f is locally of finite
type, hence finite type by quasi-compactness. Both X and Y are finite type over
k, hence Noetherian by lem-weil-pbc-finite-type-over-noetherian. Consequently f
is locally of finite presentation (pqf-lem-lft-fp-locnoeth).
2. Noetherian coordinate rings (lem-weil-pbc-finite-type-algebra-noetherian) give
Noetherian affine spaces (lem-sc-affine-noetherian-underlying-space). A finite
cover makes X topologically Noetherian. Z is therefore constructible
(def-weil-constructible-subset); Chevalley (lem-weil-pbc-chevalley-constructible-image)
makes E = f(Z) constructible, since Y is affine and thus quasi-compact and quasi-separated.
3. The nonempty boundary closure(E) minus E is constructible. Choose a nonempty
locally closed piece. Jacobson density (lem-sc-lft-over-field-jacobson-space)
provides a closed point y in that piece, hence a missing closed boundary point.
4. Spectrality (lem-weil-pbc-qcqs-scheme-spectral) and
lem-weil-pbc-spectral-proconstructible-closure-specialization supply e in E
generalizing y. The canonical map from Spec O_{Y,y}
(lem-weil-pbc-spec-local-ring-canonical-morphism) identifies its image with the
generalizations of y. Localization is Noetherian and embeds its spectrum
(lem-weil-pbc-localization-noetherian, lem-weil-pbc-localization-spectrum-embedding).
5. Pull back E to this local spectrum and restrict to its punctured open
(lem-pur-scheme-constructible-preimage, lem-weil-pbc-constructible-open-restriction).
Its nonempty constructible subset contains a nonempty locally closed piece.
The punctured-local closed-point theorem
(lem-sfb-punctured-local-spectrum-closed-points) gives t in E closed in the
punctured spectrum. Every prime lies under the maximal ideal
(lem-weil-pbc-proper-ideal-contained-in-maximal), so t specializes immediately
to y. Any intervening point of Y would belong to the same local-spectrum image.
6. The point closure is V(p_t) (lem-weil-pbc-spec-irreducible-closed-subsets-primes).
Its reduced induced scheme is Spec(R/p_t)
(lem-weil-pbc-reduced-induced-closed-subscheme), integral
(def-pc-integral-scheme), affine and finite type over k, with generic point t.
The point y remains closed, and its only generalizations in T are t and y.
The stalk-dimension chain formula (lem-sc-scheme-stalk-dimension-generalization-chains)
therefore gives dimension one.
7. Give Z its reduced induced closed structure. Its nonempty fibre at t
(def-pc-scheme-fibre) is locally of finite type over kappa(t)
(lem-weil-pbc-lft-base-change). In a nonempty affine chart choose a maximal ideal
(lem-weil-pbc-proper-ideal-contained-in-maximal). The closed-point field theorem
(lem-kun-closed-point-field), applied to that chart, gives a finite residue extension.
8. The fibre-stalk quotient (lem-sbc-scheme-fibre-stalk-quotient) identifies its
residue field with that of its image in Z. Open-immersion naturality
(lem-weil-pbc-residue-field-point-naturality) and the closed-immersion residue
isomorphism (lem-weil-pbc-closed-immersion-residue-field-iso) identify it with
kappa(x). Finally the canonical point map has image x (def-pc-scheme-fibre).
Residue-field naturality gives its composite with f. Apply the same naturality
to T's closed immersion and invert its residue-field isomorphism to obtain the
displayed canonical factorization through the generic point of T. -/
theorem finiteTypeImage_immediateBoundaryPoint
    (k : Type u) [Field k] (X Y : Scheme.{u}) [IsAffine Y]
    (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) [QuasiCompact f] (hfk : f ≫ q = p)
    (Z : Set X) (hZ : IsClosed Z) (himage : ¬ IsClosed (f '' Z)) :
    ∃ (y t : Y) (x : X) (hxt : f x = t),
      x ∈ Z ∧ IsClosed ({y} : Set Y) ∧ y ∈ closure (f '' Z) ∧ y ∉ f '' Z ∧
      t ≠ y ∧ t ⤳ y ∧ (∀ z : Y, t ⤳ z → z ⤳ y → z = t ∨ z = y) ∧
      (f.residueFieldMap x).hom.Finite ∧
      ∃ I : Y.IdealSheafData,
        I = Scheme.IdealSheafData.vanishingIdeal ⟨closure ({t} : Set Y), isClosed_closure⟩ ∧
        IsIntegral I.subscheme ∧ IsAffine I.subscheme ∧
        LocallyOfFiniteType (I.subschemeι ≫ q) ∧ QuasiCompact (I.subschemeι ≫ q) ∧
        ∃ (tT yT : I.subscheme) (htT : I.subschemeι tT = t),
          I.subschemeι yT = y ∧ IsGenericPoint tT (Set.univ : Set I.subscheme) ∧
          IsClosed ({yT} : Set I.subscheme) ∧
          ringKrullDim (I.subscheme.presheaf.stalk yT) = 1 ∧
          Set.range (X.fromSpecResidueField x) = {x} ∧
          X.fromSpecResidueField x ≫ f =
            Spec.map (@inv _ _ _ _ (I.subschemeι.residueFieldMap tT)
              (Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion I.subschemeι tT) ≫
              (Y.residueFieldCongr (htT.trans hxt.symm)).hom ≫ f.residueFieldMap x) ≫
              I.subscheme.fromSpecResidueField tT ≫ I.subschemeι := by
  sorry

end AlgebraicGeometry
