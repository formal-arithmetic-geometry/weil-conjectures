/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.ZetaSeries
/-!
# Tangent directions and normalization branches of a geometric node

Source: Stacks Project, curves.tex, Tags 0CBT (constructions (2) and (3)), 0CBU,
and 0CBW (blueprint: def-sfb-nodal-tangent-comparison-data).

The comparison is specified on every admissible standard chart by division in the actual
integral closure. This records its canonical character, including local-ring naturality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NodalLocal

/-- The local reduced normalization, as an actual integral closure in total fractions.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
abbrev Normalization (A : Type u) [CommRing A] : Type u :=
  integralClosure (A ⧸ nilradical A) (FractionRing (A ⧸ nilradical A))

/-- The structural map passes through reduction, without choosing a coefficient field.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
instance normalizationAlgebra (A : Type u) [CommRing A] : Algebra A (Normalization A) :=
  ((algebraMap (A ⧸ nilradical A) (Normalization A)).comp
    (Ideal.Quotient.mk (nilradical A))).toAlgebra

/-- The extended maximal ideal in the local reduced normalization.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def normalizationIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    Ideal (Normalization A) :=
  (IsLocalRing.maximalIdeal A).map (algebraMap A (Normalization A))

/-- The actual normalization residue algebra, not a separately chosen quadratic algebra.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
abbrev ResidueAlgebra (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  Normalization A ⧸ normalizationIdeal A

/-- The canonical residue-field action on the normalization residue algebra.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
instance residueAlgebra (A : Type u) [CommRing A] [IsLocalRing A] :
    Algebra (IsLocalRing.ResidueField A) (ResidueAlgebra A) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

/-- The same canonical action with the scheme residue-field wrapper unfolded.
Source: Stacks Project, curves.tex, Tag 0CBT(2)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
instance schemeResidueAlgebra (C : Scheme.{u}) (x : C) :
    Algebra (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)) :=
  residueAlgebra (C.presheaf.stalk x)

/-- The homogeneous pieces of the recorded associated graded ring, as additive subgroups.
Source: Stacks Project, curves.tex, Tag 0CBT(3)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def tangentGrading (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    AddSubgroup (Ideal.associatedGraded (IsLocalRing.maximalIdeal A)) :=
  (DirectSum.of (fun i : ℕ ↦
    Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A) i) n).range

/-- The homogeneous class of an element of the nth power of the maximal ideal.
Source: Stacks Project, curves.tex, Tag 0CBT(3)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def initialForm (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ)
    (a : ↥((IsLocalRing.maximalIdeal A) ^ n)) :
    Ideal.associatedGraded (IsLocalRing.maximalIdeal A) :=
  DirectSum.of (fun i : ℕ ↦
    Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal A) i) n
      (Submodule.Quotient.mk a)

/-- The normalization condition on all charts whose denominator generates the extended
maximal ideal and is regular. The equation with `b` means exactly `b = a / f^n` and avoids
any choice of fractions or coefficient field. The chart equation fixes the scheme map.
Source: Stacks Project, curves.tex, Tag 0CBT, omitted equivalence of (2) and (3)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def IsNormalized (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)]
    (i : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A))) : Prop :=
  ∀ (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hlinear : initialForm A 1 ⟨f, by simpa using hf⟩ ∈ tangentGrading A 1),
    algebraMap A (Normalization A) f ∈ nonZeroDivisors (Normalization A) →
    normalizationIdeal A = Ideal.span {algebraMap A (Normalization A) f} →
    ∃ θ : HomogeneousLocalization.Away (tangentGrading A)
        (initialForm A 1 ⟨f, by simpa using hf⟩) ≃+* ResidueAlgebra A,
      (∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n))
        (ha : initialForm A n a ∈ tangentGrading A (n • (1 : ℕ)))
        (b : Normalization A),
        algebraMap A (Normalization A) a.val =
          algebraMap A (Normalization A) f ^ n * b →
        θ (HomogeneousLocalization.Away.mk (tangentGrading A) hlinear n
          (initialForm A n a) ha) = Ideal.Quotient.mk (normalizationIdeal A) b) ∧
      (Proj.basicOpen (tangentGrading A)
        (initialForm A 1 ⟨f, by simpa using hf⟩)).ι ≫ i.hom =
        (Proj.basicOpenIsoSpec (tangentGrading A)
          (initialForm A 1 ⟨f, by simpa using hf⟩) hlinear (by decide)).hom ≫
            Spec.map (CommRingCat.ofHom θ.symm.toRingHom)

/-- All local conclusions, with explicit normalization of the canonical maps.
The grading is on the already defined homogeneous subgroups; its structure is unique.
Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU, 0CBW
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
structure Comparison (C : Scheme.{u}) (x : C)
    [GradedRing (tangentGrading (C.presheaf.stalk x))] where
  zeroIso : C.residueField x ≃+* tangentGrading (C.presheaf.stalk x) 0
  zeroIso_apply : ∀ a : C.presheaf.stalk x,
    (zeroIso (IsLocalRing.residue (C.presheaf.stalk x) a) :
      Ideal.associatedGraded (IsLocalRing.maximalIdeal (C.presheaf.stalk x))) =
        Ideal.associatedGradedRingHom (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) a
  iso : Proj (tangentGrading (C.presheaf.stalk x)) ≅
    Spec (.of (ResidueAlgebra (C.presheaf.stalk x)))
  over_residue : iso.hom ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)))) =
    Proj.toSpecZero (tangentGrading (C.presheaf.stalk x)) ≫
      Spec.map (CommRingCat.ofHom zeroIso.toRingHom)
  normalized : IsNormalized (C.presheaf.stalk x) iso
  unique : ∀ i : Proj (tangentGrading (C.presheaf.stalk x)) ≅
      Spec (.of (ResidueAlgebra (C.presheaf.stalk x))),
    IsNormalized (C.presheaf.stalk x) i → i = iso
  quadratic : Nonempty (ResidueAlgebra (C.presheaf.stalk x) ≃ₐ[C.residueField x]
      ((C.residueField x) × (C.residueField x))) ∨
    (IsField (ResidueAlgebra (C.presheaf.stalk x)) ∧
      Algebra.IsSeparable (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)) ∧
      Module.finrank (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)) = 2)
  normalizationLift : Spec (.of (Normalization (C.presheaf.stalk x))) ⟶ C.reducedNormalization
  normalizationLift_over : normalizationLift ≫ C.fromReducedNormalization =
    Spec.map (CommRingCat.ofHom
      (algebraMap (C.presheaf.stalk x) (Normalization (C.presheaf.stalk x)))) ≫
        C.fromSpecStalk x
  fiberIso : Spec (.of (ResidueAlgebra (C.presheaf.stalk x))) ≅
    pullback C.fromReducedNormalization (C.fromSpecResidueField x)
  fiberIso_fst : fiberIso.hom ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (normalizationIdeal (C.presheaf.stalk x)))) ≫ normalizationLift
  fiberIso_snd : fiberIso.hom ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom
      (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x))))

/-- Naturality for every isomorphism of pointed local rings. All transported maps are
specified on representatives; they are not arbitrary scheme isomorphisms. The Proj arrow
is Mathlib's functorial map on the induced graded homomorphism.
Source: Stacks Project, curves.tex, Tag 0CBT, intrinsic construction (3)
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def IsNaturalIso (A : Type u) [CommRing A] [IsLocalRing A]
    [GradedRing (tangentGrading A)]
    (i : Proj (tangentGrading A) ≅ Spec (.of (ResidueAlgebra A))) : Prop :=
  ∀ (A' : Type u) [CommRing A'] [IsLocalRing A'] [GradedRing (tangentGrading A')]
    (e : A ≃+* A')
    (i' : Proj (tangentGrading A') ≅ Spec (.of (ResidueAlgebra A'))),
    IsNormalized A' i' →
    ∃ (g : tangentGrading A →+*ᵍ tangentGrading A')
      (ν : Normalization A ≃+* Normalization A')
      (r : ResidueAlgebra A ≃+* ResidueAlgebra A')
      (hg : HomogeneousIdeal.irrelevant (tangentGrading A') ≤
        (HomogeneousIdeal.irrelevant (tangentGrading A)).map g),
      (∀ (n : ℕ) (a : ↥((IsLocalRing.maximalIdeal A) ^ n))
        (ha : e a.val ∈ (IsLocalRing.maximalIdeal A') ^ n),
        g (initialForm A n a) = initialForm A' n ⟨e a.val, ha⟩) ∧
      (∀ a : A,
        ν (algebraMap A (Normalization A) a) = algebraMap A' (Normalization A') (e a)) ∧
      (∀ b : Normalization A,
        r (Ideal.Quotient.mk (normalizationIdeal A) b) =
          Ideal.Quotient.mk (normalizationIdeal A') (ν b)) ∧
      Proj.map g hg ≫ i.hom = i'.hom ≫ Spec.map (CommRingCat.ofHom r.toRingHom)

/-- Naturality of the underlying normalized tangent comparison.
Source: Stacks Project, curves.tex, Tag 0CBT, intrinsic construction (3).
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def Comparison.IsNatural {C : Scheme.{u}} {x : C}
    [GradedRing (tangentGrading (C.presheaf.stalk x))] (D : Comparison C x) : Prop :=
  IsNaturalIso (C.presheaf.stalk x) D.iso

/-- The completed actual local ring at a geometric lift.
Source: Stacks Project, curves.tex, Tags 0C4D, 0CBW
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
abbrev CompletedLocalRing (X : Scheme.{u}) (y : X) : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (X.presheaf.stalk y)

/-- The stalk map into the normalization of its completion.
Source: Stacks Project, curves.tex, Tags 0C4A, 0CBT
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def toCompletedNormalization (X : Scheme.{u}) (y : X) :
    X.presheaf.stalk y →+* Normalization (CompletedLocalRing X y) :=
  (algebraMap (CompletedLocalRing X y) (Normalization (CompletedLocalRing X y))).comp
    (algebraMap (X.presheaf.stalk y) (CompletedLocalRing X y))

/-- The closed-fibre ideal of the normalization of the completed local ring.
Source: Stacks Project, curves.tex, Tags 0C4A, 0CBT
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def completedBranchIdeal (X : Scheme.{u}) (y : X) :
    Ideal (Normalization (CompletedLocalRing X y)) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).map (toCompletedNormalization X y)

/-- The scheme of branches of the normalized completed node is the spectrum of this
actual closed-fibre algebra. No ordering of the two branches is chosen.
Source: Stacks Project, curves.tex, Tags 0C4A, 0CBT, 0CBW
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
abbrev CompletedBranchAlgebra (X : Scheme.{u}) (y : X) : Type u :=
  Normalization (CompletedLocalRing X y) ⧸ completedBranchIdeal X y

/-- The structural field map to the actual stalk, via global sections and germs.
Source: Stacks Project, curves.tex, Tag 0C4D
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def stalkScalarMap {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of Ω)) (y : X) : Ω →+* X.presheaf.stalk y :=
  ((Scheme.ΓSpecIso (.of Ω)).inv ≫ g.appTop ≫ X.presheaf.Γgerm y).hom

/-- Structural scalars on the closed fibre of the normalized completed local ring.
Source: Stacks Project, curves.tex, Tags 0C4D, 0CBW
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def completedBranchScalars {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of Ω)) (y : X) : Ω →+* CompletedBranchAlgebra X y :=
  (Ideal.Quotient.mk (completedBranchIdeal X y)).comp
    ((toCompletedNormalization X y).comp (stalkScalarMap g y))

/-- The original pointed stalk maps canonically to the completed geometric stalk.
Source: Stacks Project, curves.tex, Tag 0C4D
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def geometricCompletionMap {C Y : Scheme.{u}} (p : Y ⟶ C)
    (x : C) (y : Y) (h : p y = x) : C.presheaf.stalk x →+* CompletedLocalRing Y y :=
  (algebraMap (Y.presheaf.stalk y) (CompletedLocalRing Y y)).comp
    (((C.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ p.stalkMap y).hom)

/-- The two points after scalar extension are precisely the branches of the normalized
completed geometric node. Both projections of the isomorphism are fixed, and the map on
normalizations extends the actual geometric completion map. This makes the correspondence
compatible with the original local ring and with its structural residue field.
Source: Stacks Project, curves.tex, Tags 0CBT, 0CBU, 0CBW
(blueprint: def-sfb-nodal-tangent-comparison-data). -/
def Comparison.GeometricBranches {C : Scheme.{u}} {x : C}
    [GradedRing (tangentGrading (C.presheaf.stalk x))] (D : Comparison C x)
    {Ω : Type u} [Field Ω] {Y : Scheme.{u}} (p : Y ⟶ C) (g : Y ⟶ Spec (.of Ω))
    (y : Y) (h : p y = x) : Prop :=
  ∃ (ω : Y.residueField y ≃+* Ω)
    (ρ : C.residueField x →+* Ω)
    (ν : Normalization (C.presheaf.stalk x) →+* Normalization (CompletedLocalRing Y y))
    (r : ResidueAlgebra (C.presheaf.stalk x) →+* CompletedBranchAlgebra Y y)
    (b : Spec (.of (CompletedBranchAlgebra Y y)) ≅
      pullback (D.iso.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (C.residueField x) (ResidueAlgebra (C.presheaf.stalk x)))))
        (Spec.map (CommRingCat.ofHom ρ))),
    (∀ c : Ω, ω (IsLocalRing.residue (Y.presheaf.stalk y) (stalkScalarMap g y c)) = c) ∧
    (∀ a : C.presheaf.stalk x,
      ρ (IsLocalRing.residue (C.presheaf.stalk x) a) =
        ω (IsLocalRing.residue (Y.presheaf.stalk y)
          (((C.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ p.stalkMap y).hom a))) ∧
    (∀ a : C.presheaf.stalk x,
      ν (algebraMap (C.presheaf.stalk x) (Normalization (C.presheaf.stalk x)) a) =
        algebraMap (CompletedLocalRing Y y) (Normalization (CompletedLocalRing Y y))
          (geometricCompletionMap p x y h a)) ∧
    (∀ a : Normalization (C.presheaf.stalk x),
      r (Ideal.Quotient.mk (normalizationIdeal (C.presheaf.stalk x)) a) =
        Ideal.Quotient.mk (completedBranchIdeal Y y) (ν a)) ∧
    b.hom ≫ pullback.fst _ _ ≫ D.iso.hom = Spec.map (CommRingCat.ofHom r) ∧
    b.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (completedBranchScalars g y)) ∧
    Nat.card (Spec (.of (CompletedBranchAlgebra Y y))) = 2

end AlgebraicGeometry.NodalLocal
