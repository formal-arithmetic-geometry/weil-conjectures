/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q128 and N4
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Sheaf.Paper.StrictHenselizationPointEvaluation

/-! # Rings and comparison data for affine coordinate strict-local models

Source: Stacks Project, Tags 04HX, 04GU, 05WS and 00T7.
(blueprint: def-trf-affine-coordinate-strict-local-data).

These explicit constructions and the `FibreModels` conclusion package are shared by
coordinate-zero geometry and its polynomial closed-fibre comparison.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal

/-- The finite coordinate set. Source: the coordinate comparison, Stacks 05WS and 04HX
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
abbrev Index (r : ℕ) := ULift.{u} (Fin r)

/-- The structural morphism in the specified affine coordinates. Source: Stacks 00T7
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def projection {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) : V ⟶ S :=
  e.hom ≫ AffineSpace (Index.{u} r) S ↘ S

/-- Functoriality on rings with an explicitly identified target geometric point.
Source: Stacks 04GU (blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def ringMap {X Y : Scheme.{u}} (g : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : y = x ≫ g) :
    strictHenselizationRing y →+* strictHenselizationRing x :=
  (Spec.preimage (strictHenselizationMap g x ≫
    eqToHom (congrArg strictHenselizationScheme h.symm))).hom

/-- The base strict local ring. Source: Stacks 04HX
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def Base {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :=
  strictHenselizationRing (v ≫ projection r e)

/-- The canonical base homomorphism. Source: Stacks 04GU
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def baseMap {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    Base r e v →+* strictHenselizationRing v :=
  ringMap (projection r e) v (v ≫ projection r e) rfl

/-- The images of the global affine coordinates in the ambient strict local ring.
Source: Stacks 04HX (blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def coordinate {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (i : Index.{u} r) : strictHenselizationRing v :=
  (ΓSpecIso (strictHenselizationRing v)).hom
    ((strictHenselizationStructuralMap v ≫ e.hom).appTop (AffineSpace.coord S i))

/-- The selected-coordinate ideal in the ambient strict local ring. Source: Stacks 05WS
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def coordinateIdeal {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (K : Set (Index.{u} r)) : Ideal (strictHenselizationRing v) :=
  Ideal.span (coordinate r e v '' K)

/-- Zero insertion realizes the coordinate-zero subscheme by its complementary variables.
Source: polynomial universal property, Stacks 00T7 and 01JB
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def inclusion {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) :
    AffineSpace {i : Index.{u} r // i ∉ K} S ⟶ V := by
  classical
  exact AffineSpace.homOfVector (AffineSpace {i : Index.{u} r // i ∉ K} S ↘ S)
    (fun i ↦ if h : i ∈ K then 0 else AffineSpace.coord S ⟨i, h⟩) ≫ e.inv

/-- The ideal of the base closed fibre in the ambient strict local ring. Source: Stacks 05WS
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def fibreIdeal {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    [IsLocalRing (Base r e v)] : Ideal (strictHenselizationRing v) :=
  (IsLocalRing.maximalIdeal (Base r e v)).map (baseMap r e v)

/-- The residue-coefficient polynomial ring. Source: Stacks 04HX
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def PolynomialRing {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    [IsLocalRing (Base r e v)] :=
  CommRingCat.of (MvPolynomial (Index.{u} r) (IsLocalRing.ResidueField (Base r e v)))

/-- The coordinate-zero ideal in the polynomial closed fibre. Source: Stacks 05WS
(blueprint: def-trf-affine-coordinate-strict-local-data). -/
noncomputable def polynomialIdeal {S V : Scheme.{u}} (r : ℕ)
    (e : V ≅ AffineSpace (Index.{u} r) S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    [IsLocalRing (Base r e v)] (K : Set (Index.{u} r)) : Ideal (PolynomialRing r e v) :=
  Ideal.span (MvPolynomial.X '' K)

/-- The polynomial part of the coordinate comparison, with explicit structural rings.
Source: Stacks 05WS, 04HX and 04GU
(blueprint: def-trf-affine-coordinate-strict-local-data).
The parameters are instantiated by the actual closed-fibre polynomials and ideals in Model;
they are parameters to a conclusion package, never additional hypotheses of exists_model. -/
structure FibreModels (A B P : CommRingCat.{u}) [IsLocalRing A]
    (E : Type u) (K : Set E) (I J : Ideal B) (L : Ideal P)
    (a : A →+* B) (c : A →+* P) (t : E → B) (x : E → P)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (εA : A →+* Ω) (εB : B →+* Ω) where
  /-- The residue field of A is embedded into the fixed geometric field. -/
  kappaPoint : IsLocalRing.ResidueField (A) →+* Ω
  kappaPoint_eq : kappaPoint.comp (IsLocalRing.residue (A)) =
    εA
  /-- Polynomial evaluation at the lifted closed-fibre geometric point. -/
  polynomialPoint : P →+* Ω
  polynomialPoint_coeff : ∀ z : A,
    polynomialPoint (c z) = εA z
  polynomialPoint_coord : ∀ i : E, polynomialPoint (x i) = εB (t i)
  /-- L is contained in the prime kernel q; q need not be maximal. -/
  ideal_le : L ≤ RingHom.ker polynomialPoint
  /-- The quotient point, whose kernel is q/L. -/
  quotientPoint : (P ⧸ L) →+* Ω
  quotientPoint_eq : quotientPoint.comp (Ideal.Quotient.mk (L)) =
    polynomialPoint
  prime_quotient : RingHom.ker quotientPoint =
    (RingHom.ker polynomialPoint).map (Ideal.Quotient.mk (L))
  /-- The geometric evaluations have prime kernels. -/
  [prime0 : (RingHom.ker polynomialPoint).IsPrime]
  [prime1 : (RingHom.ker quotientPoint).IsPrime]
  /-- The two strict henselization model rings and their local structures. -/
  H0 : Type u
  H1 : Type u
  [ring0 : CommRing H0]
  [ring1 : CommRing H1]
  [local0 : IsLocalRing H0]
  [local1 : IsLocalRing H1]
  /-- The residue embeddings on the polynomial prime localizations are the geometric ones. -/
  [residueAlgebra0 : Algebra (RingHom.ker polynomialPoint).ResidueField Ω]
  [residueAlgebra1 : Algebra (RingHom.ker quotientPoint).ResidueField Ω]
  residue0_eq : (algebraMap (RingHom.ker polynomialPoint).ResidueField Ω).comp
    ((IsLocalRing.residue (Localization.AtPrime (RingHom.ker polynomialPoint))).comp
      (algebraMap (P) (Localization.AtPrime (RingHom.ker polynomialPoint)))) =
    polynomialPoint
  residue1_eq : (algebraMap (RingHom.ker quotientPoint).ResidueField Ω).comp
    ((IsLocalRing.residue (Localization.AtPrime (RingHom.ker quotientPoint))).comp
      (algebraMap (P ⧸ L)
        (Localization.AtPrime (RingHom.ker quotientPoint)))) = quotientPoint
  [modelAlgebra0 : Algebra (Localization.AtPrime (RingHom.ker polynomialPoint)) H0]
  [modelAlgebra1 : Algebra (Localization.AtPrime (RingHom.ker quotientPoint)) H1]
  [closureAlgebra0 : Algebra (Localization.AtPrime (RingHom.ker polynomialPoint))
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω)]
  [closureAlgebra1 : Algebra (Localization.AtPrime (RingHom.ker quotientPoint))
    (separableClosure (RingHom.ker quotientPoint).ResidueField Ω)]
  [tower0 : IsScalarTower (Localization.AtPrime (RingHom.ker polynomialPoint))
    (RingHom.ker polynomialPoint).ResidueField
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω)]
  [tower1 : IsScalarTower (Localization.AtPrime (RingHom.ker quotientPoint))
    (RingHom.ker quotientPoint).ResidueField
    (separableClosure (RingHom.ker quotientPoint).ResidueField Ω)]
  /-- Exactly the recorded algebraic strict henselizations, relative to closures inside Ω. -/
  presentation0 : Algebra.StrictHenselizationPresentationIn.{u, u}
    (Localization.AtPrime (RingHom.ker polynomialPoint))
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω) H0
  presentation1 : Algebra.StrictHenselizationPresentationIn.{u, u}
    (Localization.AtPrime (RingHom.ker quotientPoint))
    (separableClosure (RingHom.ker quotientPoint).ResidueField Ω) H1
  /-- The two displayed local-ring isomorphisms. -/
  iso0 : (B ⧸ I) ≃+* H0
  iso1 : (B ⧸
    (I ⊔ J)) ≃+* H1
  /-- Coefficients and coordinates agree with the specified polynomial variables. -/
  coefficient0 : ∀ z : A,
    iso0 (Ideal.Quotient.mk (I) (a z)) =
      algebraMap (Localization.AtPrime (RingHom.ker polynomialPoint)) H0
        (algebraMap (P) (Localization.AtPrime (RingHom.ker polynomialPoint))
          (c z))
  coordinate0 : ∀ i : E,
    iso0 (Ideal.Quotient.mk (I) (t i)) =
      algebraMap (Localization.AtPrime (RingHom.ker polynomialPoint)) H0
        (algebraMap (P) (Localization.AtPrime (RingHom.ker polynomialPoint))
          (x i))
  coefficient1 : ∀ z : A,
    iso1 (Ideal.Quotient.mk (I ⊔ J)
      (a z)) =
      algebraMap (Localization.AtPrime (RingHom.ker quotientPoint)) H1
        (algebraMap (P ⧸ L)
          (Localization.AtPrime (RingHom.ker quotientPoint))
          (Ideal.Quotient.mk (L)
            (c z)))
  coordinate1 : ∀ i : E, i ∉ K →
    iso1 (Ideal.Quotient.mk (I ⊔ J)
      (t i)) =
      algebraMap (Localization.AtPrime (RingHom.ker quotientPoint)) H1
        (algebraMap (P ⧸ L)
          (Localization.AtPrime (RingHom.ker quotientPoint))
          (Ideal.Quotient.mk (L) (x i)))
  /-- The isomorphisms preserve the chosen geometric residue evaluation. -/
  evaluation0 : ∀ b : B,
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω).subtype
      (presentation0.residueMap (iso0 (Ideal.Quotient.mk (I) b))) =
      εB b
  evaluation1 : ∀ b : B,
    (separableClosure (RingHom.ker quotientPoint).ResidueField Ω).subtype
      (presentation1.residueMap (iso1
        (Ideal.Quotient.mk (I ⊔ J) b))) =
      εB b
  /-- The induced strict-local map, identified below with the quotient map. -/
  comparison : H0 →+* H1
  comparison_local : IsLocalHom comparison
  comparison_quotient : comparison.comp iso0.toRingHom = iso1.toRingHom.comp
    (Ideal.Quotient.factor (le_sup_left : I ≤
      I ⊔ J))
  comparison_polynomial : ∀ p : P,
    comparison (algebraMap (Localization.AtPrime (RingHom.ker polynomialPoint)) H0
      (algebraMap (P) (Localization.AtPrime (RingHom.ker polynomialPoint)) p)) =
    algebraMap (Localization.AtPrime (RingHom.ker quotientPoint)) H1
      (algebraMap (P ⧸ L)
        (Localization.AtPrime (RingHom.ker quotientPoint))
        (Ideal.Quotient.mk (L) p))
  comparison_residue :
    ((separableClosure (RingHom.ker quotientPoint).ResidueField Ω).subtype.comp
      presentation1.residueMap).comp comparison =
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω).subtype.comp
      presentation0.residueMap
  /-- Uniqueness with the fixed polynomial and residue maps specifies the canonical map. -/
  comparison_unique : ∀ d : H0 →+* H1, IsLocalHom d →
    (∀ p : P,
      d (algebraMap (Localization.AtPrime (RingHom.ker polynomialPoint)) H0
        (algebraMap (P)
          (Localization.AtPrime (RingHom.ker polynomialPoint)) p)) =
      algebraMap (Localization.AtPrime (RingHom.ker quotientPoint)) H1
        (algebraMap (P ⧸ L)
          (Localization.AtPrime (RingHom.ker quotientPoint))
          (Ideal.Quotient.mk (L) p))) →
    ((separableClosure (RingHom.ker quotientPoint).ResidueField Ω).subtype.comp
      presentation1.residueMap).comp d =
    (separableClosure (RingHom.ker polynomialPoint).ResidueField Ω).subtype.comp
      presentation0.residueMap → d = comparison


end AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal
