/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurity
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.KummerClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.SupportedCohomologyHomSpecified
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFramePrincipalBoundary
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars

/-!
# Signed zero-section purity in affine space

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`
(blueprint: cor-pur-affine-space-zero-section-purity).

The existing affine-space construction `thom` is the ordered product of the
coordinate Cartier classes, while `kummerThom` below is built independently from
the actual principal-open Kummer support boundaries and their canonical Tate-line transport.
The theorem states the complete signed zero-section purity assertion: the
Kummer orientation is invertible with both composites equal to `(-1)^c`, the
Cartier product integrates to one, the negative-twist form exists, and the
ordered Kummer product is preserved by arbitrary base change.

Proof route from the current blueprint:

1. On the ordinary étale site, iterate the affine-line adjunction and use
   `p_c ≫ z = id` to identify the exceptional target with the coefficient unit.
2. Compute the rank-one sign on the projective-line compactification: the
   Cartier class integrates to `1`, while [lem-pur-divisor-class](b) identifies
   the Kummer boundary with its negative, hence the Kummer integral is `-1`.
3. Iterate the normalized rank-one calculation with the ordered supported cup;
   the Kummer product is `(-1)^c` times the Cartier product, and the Cartier
   product is the inverse of the affine-space comparison.
4. Transport the construction through the finite étale-origin comparison and
   the specified Tate twists, retaining the actual Kummer product at every
   coefficient level.
5. Pullback of the coordinate equations, boundaries, cup operations, and the
   unique support identification gives arbitrary base-change compatibility;
   moving the invertible negative twist through the closed exceptional functor
   gives the untwisted conjunct.
-/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

/-- Extending scalars from a `ZMod N`-module agrees with extending its underlying
abelian group: all additive maps between `ZMod N`-modules are automatically linear.
This is the adjoint-uniqueness comparison, not a choice of a coefficient generator.
Source: finite coefficient transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
noncomputable def kummerZmodScalarExtensionIso
    (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA) ≅
      forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
        ModuleCat.extendScalarsAddCommGrp A := by
  let f := Scheme.finiteEtaleTwistScalar N A hA
  let adj := ModuleCat.extendScalarsAddCommGrpAdj A
  let e (M : ModuleCat.{u + 1} (ZMod N)) (P : ModuleCat.{u + 1} A) :
      ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).obj M ⟶
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat).obj P) ≃
        (M ⟶ (ModuleCat.restrictScalars f).obj P) :=
    { toFun := fun g ↦ ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars f).obj P)
        (AddMonoidHom.toZModLinearMap N (M := M)
          (M₁ := (ModuleCat.restrictScalars f).obj P) g.hom)
      invFun := fun g ↦ AddCommGrpCat.ofHom g.hom.toAddMonoidHom
      left_inv := fun g ↦ rfl
      right_inv := fun g ↦ by ext; rfl }
  let adj' : (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat ⋙
      ModuleCat.extendScalarsAddCommGrp A) ⊣ ModuleCat.restrictScalars f :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun M P ↦ (adj.homEquiv _ _).trans (e M P)
        homEquiv_naturality_left_symm := by
          intro M' M P g k
          change (adj.homEquiv _ _).symm
            ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat).map g ≫
              (e M P).symm k) = _
          exact adj.homEquiv_naturality_left_symm _ _
        homEquiv_naturality_right := by
          intro M P P' g k
          change e M P' (adj.homEquiv _ _ (g ≫ k)) = _
          rw [adj.homEquiv_naturality_right]
          rfl }
  exact (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} f).leftAdjointUniq adj'

/-- The published finite twist line as the existing abelian-sheaf scalar extension.
Sheafify the preceding canonical scalar comparison, retaining the same roots of unity.
Source: finite coefficient transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
noncomputable def kummerFiniteEtaleLineAbIso
    (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0) :
    Scheme.finiteEtaleTateLine T N A hA ≅
      (AlgebraicGeometry.Etale.extendScalars A T).obj (T.rootsOfUnitySheaf N) :=
  (presheafToSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).mapIso
    (Functor.isoWhiskerLeft (Scheme.finiteEtaleMuModulePresheaf T N)
      (kummerZmodScalarExtensionIso N A hA))

/-- The root-normalized identification of the actual finite Tate boundary target
with the shifted line used by the affine-space comparison. The power map on roots
of unity supplies exponent independence; it fixes the Kummer normalization.
Source: finite etale-origin transport in the corollary proof
(blueprint: cor-pur-affine-space-zero-section-purity). -/
def kummerBoundaryTargetIso (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    ((setting P n).principalSupportTate X)⟦(2 : ℤ)⟧ ≅
      AffineSpacePurity.shiftedLine (setting P n) X := by
  let Q := setting P n
  letI := Q.coefficientNeZero
  letI := Q.coefficientHasInvertibleExponent X aX
  let N := P.coefficients.l ^ (n + 1 + 1)
  let e := kummerFiniteEtaleLineAbIso X N Q.Coefficient
      (AffineSpacePurity.annihilates Q) ≪≫
    Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf Q.Coefficient N
      (AffineSpacePurity.annihilates Q) (AffineSpacePurity.exponentUnit Q X aX)
  let F := VectorIntegrationSite.comparison Q.Coefficient X
  exact ((F.commShiftIso (2 : ℤ)).app _).symm ≪≫
    F.mapIso ((shiftFunctor _ (2 : ℤ)).mapIso
      (Etale.tateTwistObjectIsoSingleFunctor Q.Coefficient X 1 ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e.symm))

/-- The actual coordinate Kummer support boundary, before the ordered supported cup.
It is the connecting morphism of the finite coefficient sequence on the principal
open, followed by the Kummer class of the coordinate unit; no Cartier class is
chosen. Source: the principal-support boundary construction
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerBoundaryPro (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient)
        (inclusion B c i)).obj ((setting P n).constant (divisor B c i))) ⟶
      AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c) :=
  (setting P n).principalSupportBoundary (iteratedAffineLine B c)
    (AffineSpacePurity.towerBase aB c) (iteratedAffineLine.coord B c i) ≫
      (kummerBoundaryTargetIso P n (iteratedAffineLine B c)
        (AffineSpacePurity.towerBase aB c)).hom

/-- The ordered supported cup product of the coordinate Kummer boundaries.
The recursion is the same canonical support intersection and cup transport as
`product`, but every factor is `kummerBoundaryPro`; thus this is a genuine
construction of `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_c)`, including the empty product.
Source: the ordered product of the coordinate Kummer boundaries in the corollary statement
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerProduct (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (is : List (Fin c)) →
    classSource P n B c is ⟶ target P n (iteratedAffineLine B c) is.length :=
  coordinateProductFold (classSource P n B c) (target P n (iteratedAffineLine B c))
    (coordinateProductStart (classSource_nil P n B c)
      ((cupSingle (setting P n) (iteratedAffineLine B c)).map
        ((lowerStarId (ModuleCat.{u + 1} (setting P n).Coefficient)
          (iteratedAffineLine B c)).hom.app
            ((setting P n).constant (iteratedAffineLine B c)))))
    (fun i is previous ↦ coordinateProductTransport (classSource_cons P n B c i is)
      (cupZero (setting P n) (AffineSpacePurity.towerBase aB c)
        (supportMap B c is) (inclusion B c i)
        ⟨target P n (iteratedAffineLine B c) is.length,
          target_plus P n _ (AffineSpacePurity.towerBase aB c) is.length⟩
        ⟨AffineSpacePurity.shiftedLine (setting P n) (iteratedAffineLine B c),
          boundary_plus P n _⟩
        (coordinateProductStart (classSource_eq P n B c is).symm previous)
        (kummerBoundaryPro P n B aB c i))
      (target_succ P n (iteratedAffineLine B c) is.length))

/-- The Kummer product transported from its literal intersection support to the
zero section by the unique support identification. Source: the class of the zero section
in the corollary statement (blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerSupportedClass (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c :=
  coordinateSupportedCompose ((cupSingle (setting P n) (iteratedAffineLine B c)).map
      ((setting P n).functorialCupSupportMap true (zero B c)
        (supportMap B c (List.finRange c)) (supportIso B c).hom
        (supportIso_existsUnique B c).exists.choose_spec))
    (classSource_eq P n B c (List.finRange c)).symm
    (kummerProduct P n B aB c (List.finRange c))
    (congrArg (target P n (iteratedAffineLine B c)) (@List.length_finRange c))

/-- The closed exceptional adjunct of the actual ordered Kummer product.
Source: the isomorphism `Λ_B → Rz^!Λ(c)[2c]` of the corollary statement
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerThom (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    unit P n B ⟶
      (rightDerivedUpperShriek (setting P n).Coefficient (zero B c)).obj
        (target P n (iteratedAffineLine B c) c) :=
  letI := zero_exact P n B aB c
  letI : IsNoetherian (iteratedAffineLine B c) :=
    AffineSpacePurity.tower_noetherian (setting P n) B aB c
  coordinateThomAdjunct (setting P n).Coefficient (zero B c)
      (unit P n B) (target P n (iteratedAffineLine B c) c)
      (unit_origin P n B)
      (target_plus P n (iteratedAffineLine B c) (AffineSpacePurity.towerBase aB c) c) _
      (closedSingleIso (setting P n).Coefficient (zero B c) ((setting P n).constant B))
      (kummerSupportedClass P n B aB c)

/-- The canonical closed exceptional base-change transport for the Kummer
product.  This local interface records the construction needed here because
the older generic `classBaseChange` declaration has no surviving DAG owner.
Source: base-change compatibility in the corollary statement and proof step 5
(blueprint: cor-pur-affine-space-zero-section-purity). -/
@[irreducible]
def kummerClassBaseChange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B c) c) :
    (cupSingle (setting P n) (iteratedAffineLine B' c)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B' c)).obj
        ((setting P n).constant B')) ⟶ target P n (iteratedAffineLine B' c) c :=
  classBaseChange P n g aB c α

/-- The signed, base-change-compatible zero-section purity statement.

Source: the complete statement of
`literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
cor-pur-affine-space-zero-section-purity.md`
(blueprint: cor-pur-affine-space-zero-section-purity).

The first three conjuncts render the canonical Kummer orientation, the signed
inverse normalization, and both inverse equations.  The next two conjuncts
render the Cartier product normalization.  The sixth conjunct is the
untwisted form.  The final universal conjunct renders arbitrary base change of
the actual ordered Kummer product through `kummerClassBaseChange`.

The postponed proof follows the five blueprint steps recorded in the module
docstring: ordinary affine-line adjunction and the zero-section composition;
the projective-line rank-one calculation with the divisor-class sign;
iteration of the ordered supported cup and the comparison inverse; transport
to the finite étale-origin coefficient objects; and arbitrary base change of
all coordinate maps, support maps, and cup operations.  The base-change mate
is written as a separate concrete definition because the older generic
`classBaseChange` declaration has no surviving DAG owner.
-/
theorem zeroSection_purity_signed_statement (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (c : ℕ) :
    let n := P.level - 1
    IsIso (kummerThom P n B aB c) ∧
      kummerThom P n B aB c ≫ normalization P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ ∧
      normalization P n B aB c ≫ kummerThom P n B aB c =
        ((-1 : ℤ) ^ c) • 𝟙 _ ∧
      thom P n B aB c ≫ normalization P n B aB c = 𝟙 _ ∧
      normalization P n B aB c ≫ thom P n B aB c = 𝟙 _ ∧
      Nonempty
        ((rightDerivedUpperShriek (setting P n).Coefficient (zero B c)).obj
            (unit P n (iteratedAffineLine B c)) ≅
          ((setting P n).functorialCupSingle true B).obj
            ((setting P n).functorialCupTwist true B (-(c : ℤ)))⟦-(2 * (c : ℤ))⟧) ∧
      (∀ {B' B₀ : Scheme.{u}} (g : B' ⟶ B₀)
          (aB₀ : B₀ ⟶ Spec (.of P.field.k))
          (aB' : B' ⟶ Spec (.of P.field.k))
          [LocallyOfFiniteType aB₀] [QuasiCompact aB₀] [IsSeparated aB₀]
          [LocallyOfFiniteType aB'] [QuasiCompact aB'] [IsSeparated aB']
          (hg : g ≫ aB₀ = aB') ,
          kummerClassBaseChange P n g aB₀ c (kummerSupportedClass P n B₀ aB₀ c) =
            kummerSupportedClass P n B' aB' c)
    := by
  sorry

end AlgebraicGeometry.ProEtale.AffineZeroPurity
