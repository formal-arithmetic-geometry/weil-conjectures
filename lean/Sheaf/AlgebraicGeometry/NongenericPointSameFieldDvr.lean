module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Sheaf.RingTheory.LocalDomainSameFieldDvr

/-!
# A same-function-field DVR centred at a nongeneric point

Source: Stacks Project, Properties, Tag 054F (2), with the identity field extension;
Limits, Tag 0208; Algebra, Tag 00PH.
(blueprint: lem-sfb-nongeneric-point-same-field-dvr).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Every nongeneric point of an integral locally Noetherian scheme is the centre of a
DVR inside its fixed function field, dominating its local ring. The generic restriction
is the canonical morphism from the generic stalk, with no automorphism of the field.
The subalgebra uses Mathlib's canonical `stalkFunctionFieldAlgebra`.

Source: Stacks Project, Properties, Tag 054F (2), identity extension; Limits, Tag 0208;
Algebra, Tag 00PH (blueprint: lem-sfb-nongeneric-point-same-field-dvr).

Proof:
1. Choose an affine Noetherian neighbourhood U = Spec R of z. The affine-stalk
   localization theorem identifies B = O_{Z,z} with R_p, so B is Noetherian by
   localization permanence. The integral-stalk theorem embeds B in the function
   field L via the canonical specialization map and makes L its fraction field.
2. The canonical morphism Spec B to Z has image all generalizations of z, including
   z and the generic point. If B were a field its spectrum would have one point,
   contradicting their distinctness. Thus its maximal ideal is nonzero.
3. Apply `lem-sfb-local-domain-same-field-dvr` to B inside L. Obtain a DVR
   subalgebra A with fraction field L whose maximal ideal contracts to that of B.
4. Compose Spec(B to A) with `Z.fromSpecStalk z` to obtain a. The contraction
   equality sends the closed point of Spec A to the closed point of Spec B,
   which maps to z by `lem-weil-pbc-spec-local-ring-canonical-morphism`.
5. The inverse image of U under Spec B to Z is the whole spectrum. On U the generic
   restriction is induced by R to B to A to L, sending r to its generic germ.
   The canonical generic-stalk morphism has the identical affine ring map, so
   the affine-spectrum correspondence identifies the two morphisms. Every
   fraction r_eta/s_eta is fixed, giving the identity of the prescribed L.
-/
theorem exists_dvr_subalgebra_at_nongeneric_point
    (Z : Scheme.{u}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (z : Z) (hz : z ≠ genericPoint Z) :
    ∃ (A : Subalgebra (Z.presheaf.stalk z) Z.functionField)
      (_ : IsDiscreteValuationRing A),
      IsFractionRing A Z.functionField ∧
      (IsLocalRing.maximalIdeal A).comap (algebraMap (Z.presheaf.stalk z) A) =
        IsLocalRing.maximalIdeal (Z.presheaf.stalk z) ∧
      ∃ a : Spec (CommRingCat.of A) ⟶ Z,
        a (IsLocalRing.closedPoint A) = z ∧
        Spec.map (CommRingCat.ofHom A.val.toRingHom) ≫ a =
          Z.fromSpecStalk (genericPoint Z) := by
  sorry

end AlgebraicGeometry.Scheme
