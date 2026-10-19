/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.RingTheory.StrictHenselizationPresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.EtaleHenselianRingLift
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples

/-! # Affine comparison of geometric and algebraic strict local rings

Source: Stacks Project, Etale Cohomology, Tag 04HX, and Algebra, Tag 04GW
(blueprint: lem-exc-affine-strict-local-ring-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The canonical chart leg into the affine pointed-neighbourhood ring colimit.
The chart with its lifted geometric point is itself an affine pointed neighbourhood.
The inverse of `ΓSpecIso` converts its global-section leg to a map out of `D`.
Source: Stacks Project, Tag 04HX
(blueprint: lem-exc-affine-strict-local-ring-comparison). -/
noncomputable def affineStrictLocalChartMap
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (D : CommRingCat.{u}) (i : Spec D ⟶ X) [IsOpenImmersion i]
    (xD : Spec (.of Ω) ⟶ Spec D) : D →+* strictHenselizationRing (xD ≫ i) :=
  let n : strictHenselizationNeighbourhoods (xD ≫ i) :=
    (AffineEtale.Spec X ⋙ (pointSmallEtale (xD ≫ i)).fiber).elementsMk
      (AffineEtale.mk i) (Over.homMk xD rfl)
  let E := equivSmallModel.{u} (strictHenselizationNeighbourhoods (xD ≫ i))
  ((ΓSpecIso D).inv ≫
    (strictHenselizationCoordinateRings (xD ≫ i)).map (E.unitIso.inv.app n).op ≫
      colimit.ι (strictHenselizationAffineDiagram (xD ≫ i)) (op (E.functor.obj n))).hom

/-- The chosen geometric strict local ring is the algebraic strict henselization of
`D_p`, with its specified residue map. The displayed base-map equation is the unbundled
`D`-algebra isomorphism condition. The last equation on quotient representatives says
that its induced residue-field isomorphism is the identity after both identifications
with the very same relative separable closure in `Ω`.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), and Algebra,
Tag 04GW (lemma-strict-henselization-different)
(blueprint: lem-exc-affine-strict-local-ring-comparison).

Proof:
1. The geometric point lifts uniquely through the open chart. `hxD` expresses its
prime and residue embedding, using `Spec.residueFieldIso` to identify the scheme
residue field with the residue field of `D_p`. Keep its relative separable closure K.
2. By `lem-weil-pbc-etale-local-ring-triples`, restrict the neighbourhood diagram to
the chart and identify its opposite with the etale residue triples over D, preserving
every coordinate-ring leg and pointing. The identity triple gives exactly
`affineStrictLocalChartMap` as the D-map of this colimit.
3. `lem-weil-pbc-strict-henselization-triples` makes this ring C strictly henselian,
and its evaluation epsilon to K is surjective with maximal-ideal kernel. The triple
pointings followed by K into Ω are the geometric evaluations. Colimit extensionality
therefore identifies their composite with `strictHenselizationPointEvaluation`.
4. The defining cocone in P is also the ring colimit of local-base residue triples:
a pointed map S to K factors uniquely through the residue field at its kernel, and
the inverse construction composes that residue embedding with evaluation. Both
constructions preserve the L-maps and pointings. Competing ring cocones acquire an
L-algebra structure from the identity object, so algebra universality gives ring
universality. Its induced evaluation is exactly `P.residueMap`.
5. Apply the triples theorem over L = D_p. Its colimit is strictly henselian, and
the specified map psi = P.residueMap is surjective with maximal-ideal kernel.
6. Elements of D outside p have nonzero residue in K, hence become units of C by
`lem-weil-pbc-local-ring-unit-criterion`. The localization universal property extends
the chart map uniquely to L to C, and epsilon composed with this map is L to K.
7. Apply `lem-sc-etale-henselian-ring-lift` at every pointed-etale L-algebra stage
of P, with target C and residue epsilon. Unique lifts commute with transitions;
the defining colimit gives f : H to C with its prescribed L-map and residue map.
8. Apply the same lifting lemma at every D-triple stage with target H and residue
psi. Its colimit gives g : C to H respecting the D-map and residue. Localization
uniqueness shows that g also respects the extended L-map.
9. The composites fg and gf are identities: on each defining etale stage the
single-etale uniqueness clause identifies them with the original leg, and colimit
extensionality finishes. Bundle g and f as theta. Its base-map equation gives the
D-algebra condition and psi theta = epsilon.
10. The structural map on the chart is Spec of its leg followed by i. Contravariance
of Spec gives the asserted scheme equation. Surjectivity and the maximal-ideal
kernels give both residue-field identifications, image K and kernel m_C for the
geometric evaluation. On each quotient representative c, both residue values are
epsilon(c) = psi(theta(c)); thus the map on residue fields is the identity of K. -/
theorem affine_strict_local_ring_comparison
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (D : CommRingCat.{u}) (i : Spec D ⟶ X) [IsOpenImmersion i]
    (xD : Spec (.of Ω) ⟶ Spec D) (p : Spec D)
    [Algebra p.asIdeal.ResidueField Ω]
    (hxD : xD = Spec.map ((Spec.residueFieldIso D p).hom ≫
      CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
        (Spec D).fromSpecResidueField p)
    (H : Type u) [CommRing H] [Algebra (Localization.AtPrime p.asIdeal) H]
    [Algebra (Localization.AtPrime p.asIdeal) (separableClosure p.asIdeal.ResidueField Ω)]
    [IsScalarTower (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
      (separableClosure p.asIdeal.ResidueField Ω)]
    (P : Algebra.StrictHenselizationPresentation (Localization.AtPrime p.asIdeal)
      (separableClosure p.asIdeal.ResidueField Ω) H) :
    ∃ θ : strictHenselizationRing (xD ≫ i) ≃+* H,
      θ.toRingHom.comp (affineStrictLocalChartMap D i xD) =
        (algebraMap (Localization.AtPrime p.asIdeal) H).comp
          (algebraMap D (Localization.AtPrime p.asIdeal)) ∧
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫
          strictHenselizationStructuralMap (xD ≫ i) =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (Localization.AtPrime p.asIdeal) H).comp
            (algebraMap D (Localization.AtPrime p.asIdeal)))) ≫ i ∧
      ∃ (_ : IsStrictlyHenselianLocalRing (strictHenselizationRing (xD ≫ i)))
        (_ : IsStrictlyHenselianLocalRing H),
        Function.Surjective P.residueMap ∧
        RingHom.ker P.residueMap = IsLocalRing.maximalIdeal H ∧
        (separableClosure p.asIdeal.ResidueField Ω).subtype.comp
            (P.residueMap.comp θ.toRingHom) = strictHenselizationPointEvaluation (xD ≫ i) ∧
        Set.range (strictHenselizationPointEvaluation (xD ≫ i)) =
          (separableClosure p.asIdeal.ResidueField Ω : Set Ω) ∧
        RingHom.ker (strictHenselizationPointEvaluation (xD ≫ i)) =
          IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i)) ∧
        ∃ (eC : (strictHenselizationRing (xD ≫ i) ⧸
            IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i))) ≃+*
              separableClosure p.asIdeal.ResidueField Ω)
          (eH : (H ⧸ IsLocalRing.maximalIdeal H) ≃+* separableClosure p.asIdeal.ResidueField Ω),
          eC.toRingHom.comp (Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i)))) =
            P.residueMap.comp θ.toRingHom ∧
          eH.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H)) = P.residueMap ∧
          ∀ c : strictHenselizationRing (xD ≫ i),
            eH (Ideal.Quotient.mk (IsLocalRing.maximalIdeal H) (θ c)) =
              eC (Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (strictHenselizationRing (xD ≫ i))) c) := by
  sorry

end AlgebraicGeometry.Scheme
