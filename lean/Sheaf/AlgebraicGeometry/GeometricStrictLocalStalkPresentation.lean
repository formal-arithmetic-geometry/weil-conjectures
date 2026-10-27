/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Sheaf.RingTheory.StrictHenselizationPresentationIn

/-! # A geometric strict localization as a strict henselization of its ordinary stalk

Source: Stacks Project, Tags 04HX and 01HV
(blueprint: lem-trf-geometric-strict-local-stalk-presentation).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Present the geometric strict local ring using the actual scheme stalk as base.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), and Tag 01HV
(lemma-spec-sheaves).
(blueprint: lem-trf-geometric-strict-local-stalk-presentation).

Proof: construct the strict henselization of the ordinary local ring using its
etale residue triples. A triple is equivalently an etale algebra pointed in the
specified separable closure: take the kernel of the pointing in one direction and
compose the residue embedding in the other. The equivalence preserves the base
algebra and evaluation, and hence its colimit gives the presentation P.
Choose an affine open Spec D containing the image x of the geometric point.
Lift the point through this open immersion and let p be its image in Spec D.
The affine-open stalk localization isomorphism identifies O_(X,x) with D_p;
it intertwines the germ maps and, after passage to residue fields, the embeddings
into Omega induced by the geometric point. Transport the pointed-etale diagram
along this ring isomorphism and the induced isomorphism of the relative separable
closures. Each transported object is an etale algebra with its original pointing,
and the inverse transport gives an inverse equivalence of diagrams. The colimit
therefore gives a strict henselization presentation over the actual stalk.
Apply affine_strict_local_ring_comparison on the affine chart, and transport its
comparison along these diagram isomorphisms. Its structural equation becomes the
composition with X.fromSpecStalk x, because the stalk localization isomorphism
preserves the germ of every section on the chart. Its evaluation equation is
preserved since the transported residue embedding is the specified one in Omega.
The local-ring structure is transported from the algebraic strict henselization.
This works for arbitrary schemes, without a Noetherian hypothesis. -/
theorem geometricStrictLocal_stalk_presentation
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω]
    (hΩ : algebraMap
      (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω =
        (descResidueField (stalkClosedPointTo x)).hom)
    [Algebra (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
      (separableClosure
        (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω)]
    [IsScalarTower (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
      (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))))
      (separableClosure
        (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω)] :
    ∃ (H : Type u) (_ : CommRing H)
      (_ : Algebra (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))) H)
      (P : Algebra.StrictHenselizationPresentationIn
        (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))
        (separableClosure
          (IsLocalRing.ResidueField (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω) H)
      (_ : IsLocalRing H) (θ : strictHenselizationRing x ≃+* H),
      Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ strictHenselizationStructuralMap x =
        Spec.map (CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω))) H)) ≫
            X.fromSpecStalk (x (IsLocalRing.closedPoint Ω)) ∧
      (separableClosure
        (IsLocalRing.ResidueField
          (X.presheaf.stalk (x (IsLocalRing.closedPoint Ω)))) Ω).subtype.comp
          (P.residueMap.comp θ.toRingHom) = strictHenselizationPointEvaluation x := by sorry

end AlgebraicGeometry.Scheme
