/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.CharP.Basic

import WeilConjectures.AlgebraicGeometry.PointScalarSectionsExact
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Global cohomology and Tate-twist interchange

The four coefficient presentations, their actual positive Tate lines, canonical
signed pullback comparisons, and the two uniquely normalized section maps.
Source: latest blueprint, prop-pod-degree-of-the-pairing.proof.md, last sentence.
(blueprint: lem-pod-global-twist-interchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.GlobalTwistInterchange

/-- The four coefficient cases; finite level `n` means exponent `n+1`.
Source: the coefficient list (blueprint: lem-pod-global-twist-interchange). -/
inductive CoefficientKind
  | finite (n : ℕ)
  | integral
  | rational
  | closure

/-- The published finite, integral, rational, and finite-subextension closure coefficients.
Source: the coefficient list (blueprint: lem-pod-global-twist-interchange). -/
def coefficient (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    CoefficientKind → Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  | .finite n =>
    letI : TopologicalSpace (Padic.coefficientExtensionRing ell E (n + 1)) := ⊥
    letI : DiscreteTopology (Padic.coefficientExtensionRing ell E (n + 1)) :=
      discreteTopology_bot _
    Profinite.continuousMapRingObj (Padic.coefficientExtensionRing ell E (n + 1))
  | .integral => Profinite.padicIntegersRingObj ell E.1
  | .rational => Profinite.continuousMapRingObj E.1
  | .closure => Profinite.padicAlgClRingObj ell

/-- The coefficient family inherits its published ring-object multiplication.
Source: coefficient family (blueprint: lem-pod-global-twist-interchange). -/
instance coefficientMon (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : CoefficientKind) :
    MonObj (coefficient.{u} ell E c) := by
  cases c <;> dsimp only [coefficient] <;> infer_instance

/-- Commutativity is inherited from each of the four published coefficient rings.
Source: coefficient family (blueprint: lem-pod-global-twist-interchange). -/
instance coefficientComm (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : CoefficientKind) :
    IsCommMonObj (coefficient.{u} ell E c) := by
  cases c <;> dsimp only [coefficient] <;> infer_instance

/-- The actual scalar ring and internal-module categories, with no replacement data.
Source: scalar sections (blueprint: lem-pod-global-twist-interchange). -/
abbrev Scalar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] := condensedScalarRing Λ

/-- Internal modules over the pulled-back condensed coefficient ring.
Source: coefficient and derived conventions (blueprint: lem-pod-global-twist-interchange). -/
abbrev Modules (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The existing ordinary unbounded derived category of internal modules.
Source: coefficient and derived conventions (blueprint: lem-pod-global-twist-interchange). -/
abbrev D (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) := DerivedCategory (Modules Λ X)

/-- The genuine positive Tate lines: root tensor, inverse limit, localization, and colimit.
The finite free internal module is exactly the coefficient tensor with the root sheaf;
its root exponent `n+1` annihilates the coefficient quotient by the uniformizer power.
Source: sk-def-sp-tate-twist (blueprint: lem-pod-global-twist-interchange). -/
def positiveLine (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (X : Scheme.{u}) (c : CoefficientKind) : Modules (coefficient ell E c) X :=
  match c with
  | .finite n => (CategoryTheory.Mod.free (condensedRingObj (coefficient ell E (.finite n)) X)).obj
      (Scheme.proEtaleRootsOfUnitySheaf X (ell ^ (n + 1)))
  | .integral => spIntegralTwist X ell E
  | .rational => spRationalTwist X ell E
  | .closure => spQbarTwist X ell

/-- Signed twists use the recorded internal signed powers and internal Hom duals.
Source: sk-def-sp-tate-twist (blueprint: lem-pod-global-twist-interchange). -/
abbrev Line (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) (m : ℤ) :=
  spInternalSignedTwist X (condensedRingObj Λ X) L m

/-- The recorded terminal-section module with its condensed scalar action.
Source: coefficient and derived conventions (blueprint: lem-pod-global-twist-interchange). -/
abbrev Sections (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) :=
  (CondensedRing.CohomologyTransport.sections Λ X).obj L

/-- The recorded derived tensor with the signed Tate line in degree zero.
Source: coefficient and derived conventions (blueprint: lem-pod-global-twist-interchange). -/
abbrev Twist (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X) (M : D Λ X) (m : ℤ) :=
  spInternalComplexTwist X (condensedRingObj Λ X) L M m

/-- Exact point sections on the derived pushforward, followed by homology.
Source: the displayed H^r convention (blueprint: lem-pod-global-twist-interchange). -/
abbrev H (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s) (r : ℤ) :
    D Λ Y ⥤ ModuleCat.{u + 1} (Scalar Λ) :=
  CondensedRing.moduleObjectDerivedPushforward Λ a ⋙
    CondensedRing.CohomologyTransport.Γ Λ s ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Scalar Λ)) r

/-- Convert a section into its regular-module morphism using the terminal-object equivalence.
Source: the definition of t (blueprint: lem-pod-global-twist-interchange). -/
def sectionArrow (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u}) (L : Modules Λ s) (t : Sections Λ s L) :
    CategoryTheory.Mod.regular (condensedRingObj Λ s) ⟶ L :=
  (CategoryTheory.Mod.regularHomAddEquiv L).symm
    ((Sheaf.unitHomEvalAddEquiv (Scheme.ProEt.isTerminalMkId s) L.X).symm t)

/-- Pullback of that morphism, using the cartesian regular-module identification and
specified signed comparison, followed by the derived right-unitor/tensor construction.
Source: the displayed formula (blueprint: lem-pod-global-twist-interchange). -/
def twistArrow (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s)
    (Ls : Modules Λ s) (LY : Modules Λ Y) (M : D Λ Y) (m : ℤ)
    (e : (CondensedRing.upperStar Λ a).obj (Line Λ s Ls m) ≅ Line Λ Y LY m)
    (t : Sections Λ s (Line Λ s Ls m)) : M ⟶ Twist Λ Y LY M m :=
  (ρ_ M).inv ≫ M ◁ (DerivedCategory.singleFunctor _ 0).map
    ((CondensedRing.upperStarObjRegularIso Λ a).inv ≫
      (CondensedRing.upperStar Λ a).map (sectionArrow Λ s (Line Λ s Ls m) t) ≫ e.hom)

/-- The existing sectionwise encoding and its signed powers.
Source: internal/sectionwise comparison (blueprint: lem-pod-global-twist-interchange). -/
abbrev encoding (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)

/-- The canonical counit converts internal signed-line sections to sectionwise signed sections.
Source: internal/sectionwise comparison (blueprint: lem-pod-global-twist-interchange). -/
def signedSection (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (L : Modules Λ X)
    (m : ℤ) (V : X.ProEtᵒᵖ) (x : (Line Λ X L m).X.obj.obj V) :
    (spSignedTwist X (condensedRingObj Λ X) L m).val.obj V :=
  ((encoding Λ X).counitIso.hom.app
    (spSignedTwist X (condensedRingObj Λ X) L m)).val.app V x

/-- Multiplication of actual coefficient sections, with its ring instance explicit.
Source: unit case of evaluation (blueprint: lem-pod-global-twist-interchange). -/
def sectionProduct (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u})
    (x y : (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology s) (condensedRingObj Λ s)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 s)))) := x * y

/-- Evaluation of opposite signed powers, including the unit and reversed negative case.
Source: clause (1) and proof step 1 (blueprint: lem-pod-global-twist-interchange). -/
def signedEvaluation (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u}) (L : Modules Λ s) :
    (m : ℤ) → Sections Λ s (Line Λ s L (-m)) → Sections Λ s (Line Λ s L m) →
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology s)
        (condensedRingObj Λ s)).obj.obj (op (Scheme.ProEt.mk (𝟙 s)))
  | 0, x, y => sectionProduct Λ s (signedSection Λ s L 0 _ x)
      (signedSection Λ s L 0 _ y)
  | .ofNat (n + 1), x, y =>
    (signedSection Λ s L (Int.negSucc n) _ x).app
      (op (Over.mk (𝟙 (Scheme.ProEt.mk (𝟙 s)))))
        (signedSection Λ s L (Int.ofNat (n + 1)) _ y)
  | .negSucc n, x, y =>
    (signedSection Λ s L (Int.negSucc n) _ y).app
      (op (Over.mk (𝟙 (Scheme.ProEt.mk (𝟙 s)))))
        (signedSection Λ s L (Int.ofNat (n + 1)) _ x)

/-- The normalized signed comparison from the recorded cartesian coefficient statement.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: lem-pod-global-twist-interchange). -/
abbrev SignedComparison (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s)
    (Ls : Modules Λ s) (LY : Modules Λ Y) :=
  SpSignedComparison a
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology s) (condensedRingObj Λ s))
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) (condensedRingObj Λ Y))
    (spCoefficientIso a Λ) ((encoding Λ s).functor.obj Ls) ((encoding Λ Y).functor.obj LY)

/-- The published adic comparison retains finite projections, scalar extension and
finite-subfield coprojection equations; those equations determine its component maps.
Source: CartesianAdicComparison (blueprint: lem-pod-global-twist-interchange). -/
def adicComparison (ell : ℕ) [Fact ell.Prime] {Y s : Scheme.{u}} (a : Y ⟶ s)
    [∀ x : Y, Invertible (ell : Y.residueField x)]
    [∀ x : s, Invertible (ell : s.residueField x)] : CartesianAdicComparison ell a :=
  Classical.choice (((cartesianCoefficients ell a).2.1 inferInstance inferInstance).2.2)

/-- The specified inverse-image map on the coefficient tensor with a root sheaf.
Source: finite twist comparison (blueprint: lem-pod-global-twist-interchange). -/
def rootTensorComparison (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s) (n : ℕ) :
    (Scheme.proEtaleSheafInverseImage a Ab.{u + 1}).obj
      (condensedRingObj Λ s ⊗ Scheme.proEtaleRootsOfUnitySheaf s n) ⟶
        condensedRingObj Λ Y ⊗ Scheme.proEtaleRootsOfUnitySheaf Y n :=
  Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} a)
    (condensedRingObj Λ s) (Scheme.proEtaleRootsOfUnitySheaf s n) ≫
      (condensedPullbackHom Λ a ⊗ₘ Scheme.proEtaleRootsOfUnityInverseImageMap a n)

/-- The unique rational comparison normalized by extension of the integral map.
Source: CartesianAdicComparison.rational_scalar (blueprint: lem-pod-global-twist-interchange). -/
def rationalComparison (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) {Y s : Scheme.{u}} (a : Y ⟶ s)
    [∀ x : Y, Invertible (ell : Y.residueField x)]
    [∀ x : s, Invertible (ell : s.residueField x)] :
    (Scheme.proEtaleSheafInverseImage a Ab.{u + 1}).obj (spRationalTwist s ell E).X ⟶
      (spRationalTwist Y ell E).X :=
  (adicComparison ell a).rational E

/-- The actual first comparison: root-tensor transport, inverse-limit projections,
scalar extension, or finite-subfield coprojections. The chosen adic comparison is
normalized by those equations in the recorded cartesian theorem.
Source: sk-prop-sfb-cartesian-coefficients (blueprint: lem-pod-global-twist-interchange). -/
def firstComparison (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : CoefficientKind)
    {Y s : Scheme.{u}} (a : Y ⟶ s)
    [∀ x : Y, Invertible (ell : Y.residueField x)]
    [∀ x : s, Invertible (ell : s.residueField x)] :
    (Scheme.proEtaleSheafInverseImage a Ab.{u + 1}).obj (positiveLine ell E s c).X ⟶
      (positiveLine ell E Y c).X :=
  match c with
  | .finite n =>
    rootTensorComparison (coefficient ell E (.finite n)) a (ell ^ (n + 1))
  | .integral => spIntegralComparison a ell E
  | .rational => rationalComparison ell E a
  | .closure =>
    (adicComparison ell a).qbar

/-- Fix the first signed comparison to the actual coefficient-specific map.
The remaining powers and duals are normalized in `SpSignedComparison` itself.
Source: SpInternalCartesian (blueprint: lem-pod-global-twist-interchange). -/
def FirstNormalized (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s)
    (Ls : Modules Λ s) (LY : Modules Λ Y) (β : SignedComparison Λ a Ls LY)
    (τ : (Scheme.proEtaleSheafInverseImage a Ab.{u + 1}).obj Ls.X ⟶ LY.X) : Prop :=
  ∀ (V : s.ProEtᵒᵖ) (x : Ls.X.obj.obj V),
    (((Scheme.proEtaleRingModuleAdjunction a _ _ (spCoefficientIso a Λ)).homEquiv _ _)
      (β.signed 1).hom).val.app V x =
        (((Scheme.proEtaleSheafAdjunction a Ab.{u + 1}).homEquiv _ _) τ).hom.app V x

/-- The internal pullback isomorphism is fixed by the published sectionwise adjunction.
This equation specifies every local section, rather than only global generators.
Source: cartesian signed comparisons (blueprint: lem-pod-global-twist-interchange). -/
def PullbackNormalized (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s)
    (Ls : Modules Λ s) (LY : Modules Λ Y) (β : SignedComparison Λ a Ls LY) (m : ℤ)
    (e : (CondensedRing.upperStar Λ a).obj (Line Λ s Ls m) ≅ Line Λ Y LY m) : Prop :=
  ∀ (V : s.ProEtᵒᵖ) (x : (Line Λ s Ls m).X.obj.obj V),
    (((CondensedRing.upperStarLowerStarAdjunction Λ a).homEquiv _ _) e.hom).hom.hom.app V x =
      ((encoding Λ Y).counitIso.inv.app
        (spSignedTwist Y (condensedRingObj Λ Y) LY m)).val.app
          ((Scheme.proEtaleBaseChange a).op.obj V)
            ((((Scheme.proEtaleRingModuleAdjunction a _ _ (spCoefficientIso a Λ)).homEquiv _ _)
              (β.signed m).hom).val.app V (signedSection Λ s Ls m V x))

/-- Both clauses with their uniquely specified maps. No bilinear action is supplied as data:
its pure-tensor values are the images of the constructed derived morphism `twistArrow`.
The dual is specified by the actual internal-Hom evaluation in every signed degree.
Source: the two clauses (blueprint: lem-pod-global-twist-interchange). -/
def Assertions (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y s : Scheme.{u}} (a : Y ⟶ s)
    (Ls : Modules Λ s) (LY : Modules Λ Y) (M : D Λ Y)
    (β : SignedComparison Λ a Ls LY) : Prop :=
  ∀ m : ℤ,
    Nonempty (Module.Basis (Fin 1) (Scalar Λ) (Sections Λ s (Line Λ s Ls m))) ∧
    (∃! d : Sections Λ s (Line Λ s Ls (-m)) →ₗ[Scalar Λ]
        (Sections Λ s (Line Λ s Ls m) →ₗ[Scalar Λ] Scalar Λ),
      (∀ x y, CondensedRing.CohomologyTransport.scalarMap Λ s (d x y) =
        signedEvaluation Λ s Ls m x y) ∧ Function.Bijective d) ∧
    (∃! e : (CondensedRing.upperStar Λ a).obj (Line Λ s Ls m) ≅ Line Λ Y LY m,
      PullbackNormalized Λ a Ls LY β m e ∧
      ∀ r : ℤ, ∃! f :
          ModuleCat.of (Scalar Λ)
            (TensorProduct (Scalar Λ) ((H Λ a r).obj M) (Sections Λ s (Line Λ s Ls m))) ⟶
          (H Λ a r).obj (Twist Λ Y LY M m),
        (∀ (h : (H Λ a r).obj M) (t : Sections Λ s (Line Λ s Ls m)),
          f.hom (h ⊗ₜ[Scalar Λ] t) = ((H Λ a r).map (twistArrow Λ a Ls LY M m e t)).hom h) ∧
        IsIso f)

/-- The residue-field unit is obtained from the base-field unit through the structure map.
Source: prime invertibility convention (blueprint: lem-pod-global-twist-interchange). -/
@[instance_reducible] def residueInvertible {k : Type u} [Field k]
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ ringChar k)
    (W : Over (Spec (.of k))) (x : W.left) : Invertible (ell : W.left.residueField x) :=
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ W.hom.appTop ≫ W.left.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ ell))
    ((isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ell.Prime) hell.symm)).map φ)).invertible

/-- Global cohomology commutes with every signed Tate twist, with the canonical maps.
Source: latest blueprint, prop-pod-degree-of-the-pairing.proof.md, final sentence
(blueprint: lem-pod-global-twist-interchange).

Proof (the four DAG steps).
1. Exact point sections identify H⁰ of the detailed point twist with its sections.
The point twist rank-one theorem and the twist-model comparison give a basis of L_m.
The map on the dual is global sections of internal-Hom evaluation. It is bijective
by a point-line trivialization, reducing it to evaluation at 1 on the regular module.
For m=0 use the unit; for m<0 use bidual evaluation on the trivialized positive line.
2. Choose a basis t₀ of L_m. The point twist trivialization and model comparison give
an isomorphism Λ_s → Λ_s(m) with value t₀ at 1. Pull it back through the normalized
coefficient and signed-twist comparisons. Its result is exactly t₀,Y and is an iso.
3. Tensor that isomorphism with M and precompose the inverse right unitor. This is
an isomorphism M → M(m). Apply the actual derived pushforward, exact point sections,
and degree-r homology. Under the basis identification with H^r(Y,M), the displayed
pure-tensor map is this cohomology isomorphism.
4. Write t=a t₀. Pullback, tensor, and cohomology are linear over the central scalar
ring, so the displayed assignment is bilinear. The tensor universal property gives
the unique map f; the basis identification shows it is an isomorphism. These steps
apply to arbitrary unbounded M, every r, and all signed m. Normalization on local
sections makes the internal cartesian isomorphism unique and identifies t_Y with
the source's canonical pullback, independently of the chosen basis. -/
theorem globalTwistInterchange (F : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ ringChar F.k)
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : CoefficientKind)
    (_hΛ : CondensedRing.IsAdmissibleCoefficient (coefficient.{u} ell E c))
    (Y : Over (Spec (.of F.k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y.hom] (M : D (coefficient ell E c) Y.left) :
    ∃ β : SignedComparison (coefficient ell E c) Y.hom
        (positiveLine ell E (Spec (.of F.k)) c) (positiveLine ell E Y.left c),
      FirstNormalized (coefficient ell E c) Y.hom
        (positiveLine ell E (Spec (.of F.k)) c) (positiveLine ell E Y.left c) β
        (@firstComparison ell _ E c Y.left (Spec (.of F.k)) Y.hom
          (residueInvertible ell hell Y)
          (residueInvertible ell hell (Over.mk (𝟙 (Spec (.of F.k)))))) ∧
      Assertions (coefficient ell E c) Y.hom
        (positiveLine ell E (Spec (.of F.k)) c) (positiveLine ell E Y.left c) M β := by
  sorry

end WeilConjectures.GlobalTwistInterchange
