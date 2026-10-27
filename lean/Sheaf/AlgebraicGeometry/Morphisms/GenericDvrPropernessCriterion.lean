module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.AlgebraicGeometry.FunctionField

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.ChowLemma
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Properness tested on discrete valuation subrings of the function field

Source: Stacks Project, Tag 0208, `limits-lemma-Noetherian-dvr-valuative-proper`,
(1) equivalent to (4), for an integral source; uniqueness follows from separatedness,
Tag 01L0 (blueprint: lem-sfb-generic-dvr-properness-criterion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite-type morphism from an integral scheme to a locally Noetherian
scheme is proper exactly when its canonical generic-point map extends over every DVR
subring of its function field with that fraction field. Any such extension is unique,
independently of whether existence has been established.

Source: Stacks Project, Tag 0208, `limits-lemma-Noetherian-dvr-valuative-proper`,
(1) equivalent to (4); Tag 01L0 for uniqueness.
(blueprint: lem-sfb-generic-dvr-properness-criterion)

Proof plan, following the nine steps of the node:
1. Work over affine Noetherian opens of S. Their nonempty inverse images are integral
   with the same function field. The extension property restricts to these opens, and
   universal closedness can be checked on this open cover of S.
2. By `lem-weil-pbc-finite-type-over-noetherian` and `lem-weil-pbc-chow-noetherian`,
   take a proper surjective Chow modification immersed in projective space and an
   isomorphism over a dense open of R. Take the reduced closure of the corresponding
   generic point using `lem-weil-pbc-reduced-induced-closed-subscheme`. This gives an
   integral Y, proper and surjective over R, with the same function field.
3. Take the reduced closure Z of Y in projective space. Uniqueness of reduced induced
   closed structures identifies Y with a dense open of Z. Projective properness and
   `lem-weil-pbc-proper-fp-permanence` make Z proper, hence Noetherian over this base.
4. If Y has a boundary point z in Z, its Noetherian local domain B is not a field and
   has fraction field R.functionField, by `lem-sc-integral-function-field-affine-fraction`
   and localization. Apply `lem-sfb-local-domain-same-field-dvr` to obtain a DVR A
   in that same field dominating B. Its closed point maps to z and its generic point
   maps to the generic point of Y.
5. The hypothesis supplies a map Spec A to R. Properness of Y over R lifts this to Y,
   using `lemma-nagata-proper-valuative-criterion-existence-api`. The resulting map
   to projective space agrees with the boundary-point map by
   `lemma-nagata-separated-valuation-lift-unique`, contradicting their closed-point images.
6. Thus the immersion of Y has closed image and is a closed immersion by
   `lem-weil-pbc-immersion-closed-image-closed-immersion`; hence Y is proper over S.
7. After every base change, pull back a closed subset of R to Y. Surjectivity survives
   base change by `lem-weil-pbc-surjective-base-change`, so the two images in the base
   agree. Properness of Y makes this image closed. This proves universal closedness
   of R over S; finite type and separatedness give properness.
8. Conversely properness supplies the required extensions by the valuative existence
   criterion, since a DVR is a valuation ring.
9. Separatedness alone gives uniqueness by the valuative uniqueness criterion.
-/
theorem isProper_iff_generic_dvr_extensions
    {R S : Scheme.{u}} [IsIntegral R] [IsLocallyNoetherian S]
    (f : R ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (IsProper f ↔
      ∀ (A : Subring R.functionField) [IsDiscreteValuationRing A]
        [IsFractionRing A R.functionField] (b : Spec (.of A) ⟶ S),
        Spec.map (CommRingCat.ofHom A.subtype) ≫ b =
          R.fromSpecStalk (genericPoint R) ≫ f →
        ∃ a : Spec (.of A) ⟶ R,
          Spec.map (CommRingCat.ofHom A.subtype) ≫ a = R.fromSpecStalk (genericPoint R) ∧
            a ≫ f = b) ∧
    (∀ (A : Subring R.functionField) [IsDiscreteValuationRing A]
      [IsFractionRing A R.functionField] (b : Spec (.of A) ⟶ S),
      Subsingleton {a : Spec (.of A) ⟶ R //
        Spec.map (CommRingCat.ofHom A.subtype) ≫ a = R.fromSpecStalk (genericPoint R) ∧
          a ≫ f = b}) := by
  sorry

end AlgebraicGeometry
