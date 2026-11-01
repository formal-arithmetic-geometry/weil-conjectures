/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.CharP.Basic

import all WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRootBasis
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator
import all WeilConjectures.AlgebraicGeometry.Sp.SpSliceNormalizedScalarExtensionBasis

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

attribute [local irreducible] adicComparison spIntegralTwist spRationalTwist spQbarTwist

set_option maxHeartbeats 2000000 in
-- Allow the coefficient-case typeclass and section-module encoding comparisons to elaborate.
end WeilConjectures.GlobalTwistInterchange
