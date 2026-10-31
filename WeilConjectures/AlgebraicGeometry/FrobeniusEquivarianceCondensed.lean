/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperators
public import WeilConjectures.SixFunctors.SfIdentification
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
import WeilConjectures.AlgebraicGeometry.SixFunctorOrientation
import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent
import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability
import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology
import WeilConjectures.AlgebraicGeometry.CoefficientFrobenius
import WeilConjectures.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.ZetaLinearAlgebra.Pairing

/-! # Equivariance and reciprocal eigenvalues in condensed coefficients

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius, statement and
both proof paragraphs (blueprint: sk-thm-frobenius).

All returns below are the pullback-square mates followed by the given strict
Weil isomorphism. In particular the dual return uses `StrictWeil.dualDatum`,
not an independently supplied endomorphism. The pairing is the recorded
`derivedPoincarePairing`, transported only through identity coefficient change.
The untwisted pairing is written in every Tate frame pulled back from the
geometric point. These scalar formulas express the line-valued formula in
Lambda(-d), independently of a choice of frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.SixFunctors.CondensedFrobenius

open ModelSemilinearComparison

/-- Residue-field invertibility follows from ell different from the finite-field
characteristic. Source: standing setting (blueprint: sk-thm-frobenius). -/
abbrev primeInvertible (ell : ℕ) [Fact ell.Prime]
    (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (X : Over (Spec (.of D.k))) (x : X.left) :
    Invertible (ell : X.left.residueField x) :=
  (by simpa only [map_natCast] using
    (PurityTransport.primeUnit D ell hEll).map (X.hom.residueFieldAlgebraMap x) :
    IsUnit (ell : X.left.residueField x)).invertible

/-- Ordinary scalar sections of the canonical semilinear return. The first map
is point reparametrization, the second the pullback-square mate, and the last
is the direct image of the supplied Weil structure.
Source: cohomology F (blueprint: sk-thm-frobenius). -/
def ordinaryReturn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    (g : X ≅ X) (w : g.hom ≫ a = a ≫ (StrictWeil.pointFrobenius D).hom)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (phi : (StrictWeil.action Λ g).obj K ⟶ K) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.map
    ((pointReparametrization Λ (StrictWeil.pointFrobenius D).hom).inv.app _ ≫
      (properExchange Λ a g.hom (StrictWeil.pointFrobenius D).hom w).app K ≫
      (lowerStar Λ a).rightDerivedFunctor.map phi)

/-- Compact scalar sections of the canonical proper/open return in a model
compactification. Source: cohomology F (blueprint: sk-thm-frobenius). -/
def compactScalarReturn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (cf : Compactification a)
    (g : X ≅ X) (gz : cf.Z ≅ cf.Z)
    (wj : g.hom ≫ cf.i = cf.i ≫ gz.hom)
    (wp : gz.hom ≫ cf.g = cf.g ≫ (StrictWeil.pointFrobenius D).hom)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (phi : (StrictWeil.action Λ g).obj K ⟶ K) :=
  (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.map
    (compactReturn Λ cf.i cf.g g.hom gz.hom
      (StrictWeil.pointFrobenius D).hom wj wp phi)

/-- Identity coefficient extension identifies the published trace line with
StrictWeil's actual positive Tate line; no new orientation is chosen.
Source: beta_K and orientation normalization (blueprint: sk-thm-frobenius). -/
def traceLineIso (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    (X : Scheme.{u}) (d : ℕ) :
    smoothTraceCoefficientLine ell (c.bundled ell) c (Iso.refl _) X d ≅
      StrictWeil.derivedTateLine ell c X (d : ℤ) :=
  (condensedFrobeniusScalarId (c.bundled ell) X).app _

/-- The recorded beta_K in native StrictWeil Tate coordinates. Identity scalar
extension is the only comparison; cup, evaluation, shift and normalized trace
are exactly those of sk-def-pairing and sk-thm-sf-identification.
Source: beta_K (blueprint: sk-thm-frobenius). -/
def beta (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor (c.obj ell) X.left)
    (hK : IsPerfectOnCoefficientSite (c.obj ell) X.left K.obj) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let Q := pairingOrdinarySections (c.obj ell) D.k X.hom
  let e := Q.mapIso (tensorIso (Iso.refl (StrictWeil.dual (c.obj ell) K.obj))
    (traceLineIso ell c X.left d).symm)
  (𝟙 ((pairingCompactSections (c.obj ell) D.k cf).obj K.obj) ⊗ₘ
    (shiftFunctor _ (2 * (d : ℤ))).map e.hom) ≫
      derivedPoincarePairing ell D hEll (c.bundled ell) c (Iso.refl _) X d cf K hK

/-- The point Tate frame pulled back to X through the root-normalized Cartesian
line comparison, then placed in degree zero. Only point frames occur here;
a frame varying between geometric components of X is not substituted.
Source: removal of the twist (blueprint: sk-thm-frobenius). -/
def pulledFrame (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell) (X : Over (Spec (.of D.k)))
    (d : ℕ) (e : c.line ell (Spec (.of D.k)) d ≅ 𝟙_ _) :
    StrictWeil.derivedTateLine ell c X.left (d : ℤ) ≅ 𝟙_ (c.derived ell X.left) :=
  letI := primeInvertible ell D hEll X
  letI := primeInvertible ell D hEll (Over.mk (𝟙 (Spec (.of D.k))))
  let p := Classical.choice (linePullCoordinates_nonempty ell c X.hom)
  (DerivedCategory.singleFunctor _ 0).mapIso
    ((p.power d).symm ≪≫ (upperStar (c.obj ell) X.hom).mapIso e ≪≫
      (Functor.Monoidal.εIso (upperStar (c.obj ell) X.hom)).symm) ≪≫
        DerivedCategory.singleFunctorObjUnitIso _

/-- The map induced on H^i, written as Hom from the regular unit to P[i].
Source: cohomology operators (blueprint: sk-thm-frobenius). -/
def onDegree {R : Type (u + 1)} [CommRing R]
    {P : DerivedCategory (ModuleCat.{u + 1} R)} (F : End P) (i : ℤ) :
    (𝟙_ _ ⟶ P⟦i⟧) →ₗ[R] (𝟙_ _ ⟶ P⟦i⟧) :=
  Linear.rightComp R _ ((shiftFunctor _ i).map F)

/-- Algebraic multiplicities are retained by equality of root multisets over
any algebraically closed extension of the coefficient field. Finiteness is a
conclusion, not an extra assumption on the Weil complex.
Source: last sentence (blueprint: sk-thm-frobenius). -/
def ReciprocalSpectrum {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)}
    (A : End P) (B : End Q) (q d : ℕ) : Prop :=
  ∀ hR : IsField R,
    letI : Field R := hR.toField
    ∀ i : ℤ,
      ∃ hP : Module.Finite R (𝟙_ _ ⟶ P⟦i⟧),
      ∃ hQ : Module.Finite R (𝟙_ _ ⟶ Q⟦-i⟧),
        letI := hP
        letI := hQ
        ∀ (Ω : Type (max (u + 1) v)) [Field Ω] [IsAlgClosed Ω] (j : R →+* Ω),
          ((onDegree B (-i)).charpoly.map j).roots =
            (((onDegree A i).charpoly.map j).roots.map (fun α ↦ (q : Ω) ^ d / α))

/-- All three clauses of Frobenius equivariance for the actual condensed pairing.
The commuting-square witnesses certify equations of specified geometric maps;
none is an assumption or a choice of a Frobenius operator.
Source: entire statement (blueprint: sk-thm-frobenius). -/
def Assertion (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (c : Coefficient ell)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom]
    (cf₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D X₀))
    (hK : IsPerfectOnCoefficientSite (c.obj ell) (D.geometricFiber X₀).left K.carrier.obj) : Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let X := D.geometricFiber X₀
  letI : SmoothOfRelativeDimension d X.hom :=
    inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI := primeInvertible ell D hEll X
  let cf := geometricCompactification D X₀ cf₀
  let g := StrictWeil.modelFrobenius D X₀
  let gz := StrictWeil.modelFrobenius D (Over.mk cf₀.g)
  let phi := ambientStructure (c.obj ell) K
  ∃ wj : g.hom ≫ cf.i = cf.i ≫ gz.hom,
  ∃ wp : gz.hom ≫ cf.g = cf.g ≫ (StrictWeil.pointFrobenius D).hom,
  ∃ wa : g.hom ≫ X.hom = X.hom ≫ (StrictWeil.pointFrobenius D).hom,
  let P := (pairingCompactSections (c.obj ell) D.k cf).obj K.carrier.obj
  let O := pairingOrdinarySections (c.obj ell) D.k X.hom
  let U := StrictWeil.dual (c.obj ell) K.carrier.obj
  let Q := (O.obj (U ⊗ StrictWeil.derivedTateLine ell c X.left (d : ℤ))) ⟦2 * (d : ℤ)⟧
  let Q₀ := (O.obj U) ⟦2 * (d : ℤ)⟧
  let F := compactScalarReturn (c.obj ell) D cf g gz wj wp phi.hom
  let F₀ := (shiftFunctor _ (2 * (d : ℤ))).map
    (ordinaryReturn (c.obj ell) D X.hom g wa
      (StrictWeil.dualDatum (c.obj ell) g K.carrier.obj phi).hom)
  let Ft := (shiftFunctor _ (2 * (d : ℤ))).map
    (ordinaryReturn (c.obj ell) D X.hom g wa
      (StrictWeil.twistedDualDatum ell c g K.carrier.obj phi (d : ℤ)).hom)
  let b : P ⊗ Q ⟶ 𝟙_ _ := beta ell D hEll c X d cf K.carrier hK
  (constantModelBoundedConstructible (c.obj ell) X.left ⊓
    DerivedCategory.finiteTorAmplitude _) U ∧
  (constantModelBoundedConstructible (c.obj ell) X.left ⊓
    DerivedCategory.finiteTorAmplitude _)
      (U ⊗ StrictWeil.derivedTateLine ell c X.left (d : ℤ)) ∧
  ∃ hF : IsIso F, ∃ hF₀ : IsIso F₀, ∃ hFt : IsIso Ft,
  letI := hF
  letI := hF₀
  letI := hFt
  (∃ f : Endofunctor.IsoAlgebra.mk (F := 𝟭 _) (P ⊗ Q) (asIso (F ⊗ₘ Ft)) ⟶
      Endofunctor.IsoAlgebra.mk (F := 𝟭 _) (𝟙_ _) (Iso.refl _), f.hom.f = b) ∧
  ((F ⊗ₘ Ft) ≫ b = b) ∧
  (∀ (i : ℤ) (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q⟦-i⟧),
    identificationDegreeValue b i (onDegree F i x) (onDegree Ft (-i) y) =
      identificationDegreeValue b i x y) ∧
  Nonempty (c.line ell (Spec (.of D.k)) d ≅ 𝟙_ _) ∧
  (∀ e : c.line ell (Spec (.of D.k)) d ≅ 𝟙_ _,
    let eQ : Q ≅ Q₀ := (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (O.mapIso (tensorIso (Iso.refl U) (pulledFrame ell D hEll c X d e)) ≪≫
        O.mapIso (ρ_ U))
    let bu : P ⊗ Q₀ ⟶ 𝟙_ _ := (𝟙 P ⊗ₘ eQ.inv) ≫ b
    ((F ⊗ₘ F₀) ≫ bu = (D.q ^ d) • bu) ∧
    ∀ (i : ℤ) (x : 𝟙_ _ ⟶ P⟦i⟧) (y : 𝟙_ _ ⟶ Q₀⟦-i⟧),
      identificationDegreeValue bu i (onDegree F i x) (onDegree F₀ (-i) y) =
        (D.q ^ d) • identificationDegreeValue bu i x y) ∧
  ReciprocalSpectrum.{u, v} F F₀ D.q d

/-- Frobenius equivariance and reciprocal eigenvalues for every one of the four
admissible condensed coefficient stages, with no equivariance or perfect-pairing
assumptions on the conclusions.

Source: latest blueprint sec-poincare-duality/sk-thm-frobenius, entire statement
(blueprint: sk-thm-frobenius).
Proof: the inverse in StrictWeil.dualDatum makes evaluation equivariant by
extranaturality of internal Hom and the unit comparison. Proper/open mates and
exact point sections transport mixed-support cup equivariantly. Smooth purity
and its normalized counit are equivariant, so their recorded composite beta_K
intertwines the tensor of the compact and twisted-dual returns with the unit.
Postcomposition on Hom-from-unit cohomology gives the twisted identity. Pull
any point Tate frame back through the normalized root comparison; geometric
Frobenius on its dth power is q^(-d), giving the untwisted q^d identity. The
field-stage part of sf_identification identifies complementary cohomology with
the vector-space dual. Finite constructible cohomology is finite dimensional;
the strict structures induce invertible returns. The untwisted identity then
conjugates F₀ to q^d times the transpose of F inverse. Transpose preserves the
characteristic polynomial and inverse reciprocates its roots with algebraic
multiplicity, which gives the asserted multiset equality. The construction and
identities also apply in dimension zero and on disconnected or empty schemes. -/
theorem frobenius_equivariance (ell : ℕ) [Fact ell.Prime]
    (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (c : Coefficient ell) (E : PadicAlgCl.FiniteIntermediateField ell)
    (_hΛ : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom]
    (cf₀ : Compactification X₀.hom)
    (K : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D X₀))
    (hK : IsPerfectOnCoefficientSite (c.obj ell) (D.geometricFiber X₀).left K.carrier.obj) :
    Assertion.{u, v} ell D hEll c X₀ d cf₀ K hK := by
  sorry

end WeilConjectures.SixFunctors.CondensedFrobenius
