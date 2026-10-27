/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations


/-! # Simultaneous pointed strict-local chart models

Source: Stacks Project, Etale Cohomology, Tag 04HX; Algebra, Tag 04GW
(blueprint: lem-trf-strict-local-closed-chart-models).

This isolates the affine comparison step. It asserts no compatibility of the canonical
strict-local map and contains no structure on the quotient of the ambient strict-local ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The two pointed affine comparison models, before considering any map between them.
Source: Stacks Project, Tag 04HX and Algebra, Tag 04GW
(blueprint: lem-trf-strict-local-closed-chart-models). -/
structure StrictLocalClosedChartModels
    (A : Type u) [CommRing A] (I p : Ideal A) [p.IsPrime]
    (R S C D K Ω : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [CommRing S] [CommRing C] [CommRing D] [Field K] [Field Ω]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    (π : R →+* S) (α : A →+* C) (β : A ⧸ I →+* D)
    (ι : K →+* Ω) (εC : C →+* Ω) (εD : D →+* Ω) where
  /-- The local structure on the localized quotient. -/
  [localS : IsLocalRing S]
  /-- Its algebra structure from the affine quotient chart. -/
  [chartS : Algebra (A ⧸ I) S]
  /-- The quotient chart and local quotient have the same map from A. -/
  chartS_eq : (algebraMap (A ⧸ I) S).comp (Ideal.Quotient.mk I) =
    π.comp (algebraMap A R)
  /-- S is the localization of A/I at the image of the complement of p. -/
  localizationS : IsLocalization (p.primeCompl.map (Ideal.Quotient.mk I)) S
  /-- The local structure on the ambient strict-local ring. -/
  [localC : IsLocalRing C]
  /-- The local structure on the closed-subscheme strict-local ring. -/
  [localD : IsLocalRing D]
  /-- The ambient local-base algebra structure. -/
  [baseC : Algebra R C]
  /-- The closed-subscheme local-base algebra structure. -/
  [baseD : Algebra S D]
  /-- The first structure extends the actual ambient chart map. -/
  baseC_eq : (algebraMap R C).comp (algebraMap A R) = α
  /-- The second structure extends the actual quotient chart map. -/
  baseD_eq : (algebraMap S D).comp (algebraMap (A ⧸ I) S) = β
  /-- The ambient structure map is local. -/
  baseC_local : IsLocalHom (algebraMap R C)
  /-- The closed-subscheme structure map is local. -/
  baseD_local : IsLocalHom (algebraMap S D)
  /-- The ambient action on the common separable closure. -/
  [closureR : Algebra R K]
  /-- The ambient action factors through its given residue embedding. -/
  [towerR : IsScalarTower R (IsLocalRing.ResidueField R) K]
  /-- The common separable closure as an S-algebra. -/
  [closureS : Algebra S K]
  /-- Its algebra structure from the residue field of S. -/
  [residueS : Algebra (IsLocalRing.ResidueField S) K]
  /-- It is a separable closure of that residue field. -/
  [separableS : IsSepClosure (IsLocalRing.ResidueField S) K]
  /-- The S-action factors through its residue field. -/
  [towerS : IsScalarTower S (IsLocalRing.ResidueField S) K]
  /-- Both local bases act through the same embedding into K. -/
  closureS_eq : (algebraMap S K).comp π = algebraMap R K
  /-- The defining pointed-etale colimit of the ambient ring. -/
  presentationC : Algebra.StrictHenselizationPresentationIn.{u, u} R K C
  /-- The defining pointed-etale colimit of the closed-subscheme ring. -/
  presentationD : Algebra.StrictHenselizationPresentationIn.{u, u} S K D
  /-- Strict henselianity of the ambient ring. -/
  strictC : IsStrictlyHenselianLocalRing C
  /-- Strict henselianity of the closed-subscheme ring. -/
  strictD : IsStrictlyHenselianLocalRing D
  /-- Its specified residue identification with K. -/
  residueC : IsLocalRing.ResidueField C ≃+* K
  /-- The other specified residue identification with the same K. -/
  residueD : IsLocalRing.ResidueField D ≃+* K
  /-- The identification is induced by the ambient pointed colimit. -/
  residueC_eq : residueC.toRingHom.comp (IsLocalRing.residue C) = presentationC.residueMap
  /-- The other identification is induced by the closed pointed colimit. -/
  residueD_eq : residueD.toRingHom.comp (IsLocalRing.residue D) = presentationD.residueMap
  /-- The ambient geometric evaluation is the specified residue map into Ω. -/
  evaluationC : ι.comp presentationC.residueMap = εC
  /-- The closed geometric evaluation is the specified residue map into Ω. -/
  evaluationD : ι.comp presentationD.residueMap = εD
  /-- The base residue embedding is the specified one. -/
  residueC_base : presentationC.residueMap.comp (algebraMap R C) = algebraMap R K
  /-- The quotient-base residue embedding is the specified one. -/
  residueD_base : presentationD.residueMap.comp (algebraMap S D) = algebraMap S K

/-- Simultaneous affine comparison for the local base and its closed quotient.
Only the individual chart models are asserted: compatibility of the prescribed canonical
map, annihilation of the ideal and the local quotient factorization are separate arguments.
Source: Stacks Project, Etale Cohomology, Tag 04HX; Algebra, Tag 04GW
(blueprint: lem-trf-strict-local-closed-chart-models).

Proof:
1. The equation hx identifies the prime of the ambient geometric point and its specified
residue embedding. The quotient point determines the prime p/I; its residue field is
canonically the same as that of p. Localizing the quotient chart at this prime identifies
its local ring with S = R/IR and gives the displayed chart and localization equations.
The quotient map is local and identifies the two residue fields. Transport the given
relative separable closure through this identification, giving the compatible R- and
S-actions on the same K, factoring through their respective residue fields.
2. Apply strictHenselization_triples to each local base. A pointed etale algebra B to K
corresponds to its kernel prime together with the induced residue-field embedding into K.
Conversely a residue triple gives its pointing by composition with its residue map.
These operations are inverse on objects and arrows and preserve coordinate rings and
pointings. Transport the universal cocones to obtain the pointed-etale presentations.
3. Apply affine_strict_local_ring_comparison to the two open affine charts. Its equations
identify the geometric chart legs, structural maps and evaluations with these algebraic
models. Transport their local and strictly henselian structures, presentations, and residue
isomorphisms across the comparison isomorphisms. Elements outside p have nonzero residue
in K, hence are units; localization uniqueness extends the chart maps to R and S and
shows that the comparison isomorphisms respect these extensions. The composite from each
local base to K is its specified residue embedding. Its kernel is the maximal ideal,
which proves locality of the two base maps. All asserted equations are the transported
chart, localization and pointed-colimit equations. -/
theorem strictLocalClosedChartModels
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (A : CommRingCat.{u}) (I : Ideal A)
    (j : Spec A ⟶ W) [IsOpenImmersion j]
    (k : Spec (.of (A ⧸ I)) ⟶ Z) [IsOpenImmersion k]
    (hsquare : IsPullback k (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) i j)
    (x : Spec (.of Ω) ⟶ Spec (.of (A ⧸ I))) (p : Spec A)
    [Algebra p.asIdeal.ResidueField Ω]
    (hx : x ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      Spec.map ((Spec.residueFieldIso A p).hom ≫
        CommRingCat.ofHom (algebraMap p.asIdeal.ResidueField Ω)) ≫
          (Spec A).fromSpecResidueField p) :
    ∃ (α : A →+* strictHenselizationRing ((x ≫ k) ≫ i))
      (β : (A ⧸ I) →+* strictHenselizationRing (x ≫ k)),
      Spec.map (CommRingCat.ofHom α) ≫ j =
        strictHenselizationStructuralMap ((x ≫ k) ≫ i) ∧
      Spec.map (CommRingCat.ofHom β) ≫ k = strictHenselizationStructuralMap (x ≫ k) ∧
      Nonempty (StrictLocalClosedChartModels A I p.asIdeal
        (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap A
          (Localization.AtPrime p.asIdeal)))
        (strictHenselizationRing ((x ≫ k) ≫ i)) (strictHenselizationRing (x ≫ k))
        (separableClosure p.asIdeal.ResidueField Ω) Ω
        (Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p.asIdeal))))
        α β (separableClosure p.asIdeal.ResidueField Ω).subtype
        (strictHenselizationPointEvaluation ((x ≫ k) ≫ i))
        (strictHenselizationPointEvaluation (x ≫ k))) := by sorry

end AlgebraicGeometry.Scheme
