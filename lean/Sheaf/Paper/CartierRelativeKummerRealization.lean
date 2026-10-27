module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.PurityFrameClass
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.Paper.PurityDivisorClass
public import Sheaf.Paper.CartierClassAgreement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.CartierKummerData
public import Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization
import Sheaf.Paper.FiniteTateSiteDescent
import all Sheaf.Paper.P1KummerScalarEndpointExistence
import Sheaf.Paper.FiniteTateLocalRootTensorsExt

/-! # Relative Cartier Kummer realization

Source: blueprint main-20261015, thm-pur-rank-one-thom.proof.md, Step 1
(blueprint: lem-pur-cartier-relative-kummer-realization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

set_option allowUnsafeReducibility true in
attribute [local irreducible] functorialCupHasDerived functorialCupCategory
  functorialCupAbelian functorialCupSheaves functorialCupSingle
  functorialCupTwist functorialCupSource functorialCupPullback
  generalDivisorClass agreementCartierMap frameBoundary


private theorem positive_induction (p : PurityFiniteSetting.{u} → Prop)
    (h : ∀ (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
      (E : IntermediateField (Padic C.l) C.Qbar)
      (hE : FiniteDimensional (Padic C.l) E) (n : ℕ) (hlevel : 1 ≤ n + 1),
      p (@PurityFiniteSetting.mk F C E hE (n + 1) hlevel))
    (P : PurityFiniteSetting.{u}) : p P := by
  cases P with
  | @mk F C E hE level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n => exact h F C E hE n hlevel

/-- Z/N with the standard coefficient size lift. Source: the finite-root realization
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
abbrev relativeCartierRootRing (P : PurityFiniteSetting.{u}) :=
  ULift.{u + 1} (ZMod P.diagonalExponent)

/-- The defining zero relation in Z/N, transported by the coefficient size lift.
Proof: ZMod.natCast_self gives N=0; apply ULift.up to this equality.
Source: the finite-root realization (blueprint: lem-pur-cartier-relative-kummer-realization). -/
theorem relativeCartierRootZero (P : PurityFiniteSetting.{u}) :
    (P.diagonalExponent : P.relativeCartierRootRing) = 0 :=
  congrArg (ULift.up : ZMod P.diagonalExponent → P.relativeCartierRootRing)
    (ZMod.natCast_self P.diagonalExponent)

/-- The roots sheaf in the existing R-tensor-roots presentation, canonically R tensor_R mu.
Source: finite-root realization, first paragraph
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
abbrev relativeCartierRoots (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  Scheme.finiteEtaleTateLine S P.diagonalExponent
    P.relativeCartierRootRing P.relativeCartierRootZero

/-- The prescribed quotient scalar map from Z/N to A, with the size lift removed.
Source: finite-root realization, first paragraph
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
def relativeCartierScalar (P : PurityFiniteSetting.{u}) :
    P.relativeCartierRootRing →+* P.Coefficient :=
  (Scheme.finiteEtaleTwistScalar P.diagonalExponent
    P.Coefficient P.diagonalExponent_annihilates).comp ULift.ringEquiv.toRingHom

/-- Flatness of the finite roots and the canonical derived-to-ordinary scalar identification.
The universal unit identifies the actual degree-zero ordinary tensor with derived extension
on all unbounded test objects. The last clause gives an isomorphism from every other derived
representative and fixes it by its unit, rather than asserting only homology isomorphisms.
Source: thm-pur-rank-one-thom.proof.md, Step 1, finite-root realization
(blueprint: lem-pur-cartier-relative-kummer-realization).

Proof: (1) ell is divisible by the uniformizer, so ell^level kills A. (2) Since ell is
invertible on S, finite_etale_torsion_twist_line over R makes the roots flat. Their
single complex is K-flat by bounded-above-flat-kflat-site. Compute coefficient change
on that complex by derived-change-of-rings, using the identity resolution: its value
is exactly the degree-zero ordinary root tensor. (3) The scalar unit on each root tensor
is r tensor z to scalar(r) tensor z. Its universal property gives the displayed derived
isomorphism, uniquely characterized by that unit. No flatness of A over R is used. -/
theorem relativeCartierRoots_realization (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) (a : S ⟶ Spec (.of P.field.k)) :
    (P.diagonalExponent : P.Coefficient) = 0 ∧
    ObjectProperty.flat (P.relativeCartierRoots S) ∧
    ∃ η : P.relativeCartierRoots S ⟶
      (Sheaf.restrictScalars S.smallEtaleTopology P.relativeCartierScalar).obj
        (P.frameTwistEtale S 1),
      (∀ (U : S.Etaleᵒᵖ) (r : P.relativeCartierRootRing)
        (z : (S.rootsOfUnitySheaf P.diagonalExponent).obj.obj U),
        η.hom.app U (Scheme.finiteEtaleTateOneGenerator P.relativeCartierRootRing
          P.diagonalExponent S P.relativeCartierRootZero U r z) =
        Scheme.finiteEtaleTateOneGenerator P.Coefficient P.diagonalExponent S
          P.diagonalExponent_annihilates U (P.relativeCartierScalar r) z) ∧
      Etale.SupportedDerivedScalarUnit P.relativeCartierScalar S
        (P.relativeCartierRoots S) (P.frameTwistEtale S 1) η ∧
      ∀ (L : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
        (ηL : SheafExactDegreeZero.scalarObj S.smallEtaleTopology
          P.relativeCartierRootRing (P.relativeCartierRoots S) ⟶
          (Sheaf.derivedRestrictScalars S.smallEtaleTopology P.relativeCartierScalar).obj L),
        Sheaf.IsDerivedBaseChange ηL →
        ∃ e : L ≅ SheafExactDegreeZero.scalarObj S.smallEtaleTopology
          P.Coefficient (P.frameTwistEtale S 1),
          ηL ≫ (Sheaf.derivedRestrictScalars S.smallEtaleTopology P.relativeCartierScalar).map
            e.hom = SheafExactDegreeZero.scalarUnit S.smallEtaleTopology
              P.relativeCartierScalar (P.relativeCartierRoots S) (P.frameTwistEtale S 1) η := by
  classical
  have hN : 0 < P.diagonalExponent :=
    pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  let : NeZero P.diagonalExponent := ⟨hN.ne'⟩
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : Finite P.Coefficient := (Equiv.ulift : P.Coefficient ≃ P.Ring).finite_iff.mpr
    inferInstance
  have hf := (Scheme.finite_etale_torsion_twist_line S P.diagonalExponent hN
    (fun x ↦ by
      simpa only [diagonalExponent, Nat.cast_pow] using
        (P.coefficientPrime_isUnit_stalk S a x).pow P.level)
    P.relativeCartierRootRing P.relativeCartierRootZero 1).2.2.1
  have hflat : ObjectProperty.flat (P.relativeCartierRoots S) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2 hf
  have hI : (Scheme.emptyTo S).ker.IsInvertible := by
    rw [Scheme.ker_eq_top_of_isEmpty]
    exact Scheme.IdealSheafData.isInvertible_top
  obtain ⟨η, hη, hηu⟩ := Etale.residueLineData S P.diagonalExponent hN
    (P.diagonalExponent_isUnit a) P.Coefficient P.diagonalExponent_annihilates
    (Scheme.emptyTo S) hI
  refine ⟨P.diagonalExponent_annihilates, hflat, η, hη, hηu, ?_⟩
  intro L ηL hL
  have hη' : Sheaf.IsDerivedBaseChange
      (SheafExactDegreeZero.scalarUnit S.smallEtaleTopology P.relativeCartierScalar
        (P.relativeCartierRoots S) (P.frameTwistEtale S 1) η) := by
    unfold Etale.SupportedDerivedScalarUnit SheafExactDegreeZero.scalarUniversal at hηu
    exact hηu
  obtain ⟨f, hf⟩ := (hL _).2
    (SheafExactDegreeZero.scalarUnit S.smallEtaleTopology P.relativeCartierScalar
      (P.relativeCartierRoots S) (P.frameTwistEtale S 1) η)
  have : IsIso f := hL.isIso hη' f hf
  exact ⟨asIso f, hf⟩

/-- The prescribed finite pro-etale twist, merely reindexed from n-1 to positive level n.
Source: def-coefficient-twists-detailed, root projection convention
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
@[no_expose] def relativeCartierProLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  match P with
  | @PurityFiniteSetting.mk _ _ _ _ 0 hlevel =>
    False.elim (Nat.not_succ_le_zero 0 hlevel)
  | @PurityFiniteSetting.mk _ C E hE (n + 1) _ =>
    letI : FiniteDimensional (Padic C.l) E := hE
    Scheme.finiteTateProSheaf C.l E n T 1

/-- The published normalized pro-etale Cartier Ext class, only reindexed at positive level n.
Source: lem-amb-cartier-kummer-map, the unique normalized pair
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
@[no_expose] def relativeCartierProExt (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Ext
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))
      (P.relativeCartierProLine T) 2 :=
  match P with
  | @PurityFiniteSetting.mk _ _ _ _ 0 hlevel =>
    False.elim (Nat.not_succ_le_zero 0 hlevel)
  | @PurityFiniteSetting.mk F C E hE (n + 1) hlevel => by
    letI : FiniteDimensional (Padic C.l) E := hE
    let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
    have hT : IsUnit (C.l : Γ(T, ⊤)) :=
      (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
        (by simpa only [diagonalExponent, Nat.cast_pow] using Q.diagonalExponent_isUnit a)
    unfold relativeCartierProLine
    dsimp only [Coefficient, Ring, coefficientCommRing, ringCommRing]
    have c := (Etale.cartier_kummer_map C.l E).2.exists.choose.2 n i hI hT
    unfold Etale.cartierSupported at c
    exact c

/-- The actual Ext-to-derived realization of the published Cartier class. This uses the
same Ext.hom as cartierKummerMap, with the ambient derived instances fixed by P.
Source: lem-amb-cartier-kummer-map, canonical arrow
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
def relativeCartierProMap (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient))) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (P.relativeCartierProLine T))⟦(2 : ℤ)⟧ :=
  (P.relativeCartierProExt a i hI).hom

/-- The recorded root-projection predicate, reindexed at the positive coefficient level.
It specifies the image of every local root tensor and hence the actual comparison.
Source: def-pur-frame-class and finite Tate site comparison data
(blueprint: lem-pur-cartier-relative-kummer-realization). -/
@[no_expose] def RelativeCartierRootNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (q : P.frameTwist T 1 ≅ P.relativeCartierProLine T) : Prop :=
  match P with
  | @PurityFiniteSetting.mk _ _ _ _ 0 hlevel =>
    False.elim (Nat.not_succ_le_zero 0 hlevel)
  | @PurityFiniteSetting.mk F C E hE (n + 1) hlevel => by
    letI : FiniteDimensional (Padic C.l) E := hE
    let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
    dsimp only [relativeCartierProLine, frameTwist, frameTwistEtale, Coefficient, Ring,
      coefficientCommRing, ringCommRing] at q ⊢
    exact Scheme.IsFiniteTateSiteComparison C.l E n T n Q.diagonalExponent_annihilates 1 q

/-- The root-projection comparison from C(L) to the prescribed twist exists on every
k-scheme, with precisely the normalized local root-tensor formula.
Source: thm-pur-rank-one-thom.proof.md, Step 1, realization step 3
(blueprint: lem-pur-cartier-relative-kummer-realization).
Proof: finite-root-site-comparison takes the inverse image of the ordinary root tensor
to the identical pro-etale root tensor. Compose with the inverse of the projection
reduction at r=level. On every tensor the formula is the roots-projection convention,
so this is the specified theta, not an arbitrary line isomorphism. Every finite root
lifts pro-etale locally to the infinite root tower by twist-sheaf-locally-free; pure
root tensors generate the inverse image locally, proving uniqueness. -/
theorem relativeCartierTwist_realization (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) (a : S ⟶ Spec (.of P.field.k)) :
    ∃! q : P.frameTwist S 1 ≅ P.relativeCartierProLine S,
      P.RelativeCartierRootNormalized S q := by
  induction P using positive_induction with
  | h F C E hE n hlevel =>
    let : FiniteDimensional (Padic C.l) E := hE
    let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
    have hT : IsUnit (C.l : Γ(S, ⊤)) :=
      (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
        (by simpa only [diagonalExponent, Nat.cast_pow] using Q.diagonalExponent_isUnit a)
    obtain ⟨q, hq, _⟩ := Scheme.finite_tate_site_descent C.l E n
    refine ⟨q S hT n Q.diagonalExponent_annihilates 1,
      hq S hT n Q.diagonalExponent_annihilates 1, ?_⟩
    intro q' hq'
    apply Iso.ext
    apply Scheme.finiteTate_local_root_tensors_hom_ext C.l E n S hT n
      Q.diagonalExponent_annihilates 1
    intro U W v a z x hx
    exact (hq' U W v a z x hx).trans
      ((hq S hT n Q.diagonalExponent_annihilates 1 U W v a z x hx).symm)


/-- Finite-root realization of the actual relative Cartier Kummer arrow, including
its derived scalar origin, supported-Hom class agreement and local Yoneda sign.
Source: thm-pur-rank-one-thom.proof.md, Step 1, expanded realization steps 4--7
(blueprint: lem-pur-cartier-relative-kummer-realization).

Proof: apply ordinary-supported-kummer at N=ell^level and A to the Cartier pair. Its
relative Yoneda normalization retains the frame of O(D) off D and its zero image
there, and its scalar clause identifies the whole arrow with the R-boundary after
derived extension. Boundary uniqueness identifies this with agreementCartierEtale.
CartierKummerRealization and unique descent give the published pro-etale arrow. Its
target comparison equals theta by root normalization and local lifting of roots;
its source comparison is the canonical gamma, uniquely determined by preserving the
constant quotient, by supported-constant-exchange-normalization. This gives the
actual derived-arrow equation. Cartier-class-agreement identifies the global divisor
class with agreementCartierMap under supported-cohomology-hom. Finally divisor-class
applies to the smooth codimension-one Cartier family and gives minus frameBoundary
on every etale principal presentation. This is a global equality before restriction;
local restrictions alone are not used to infer equality of global classes. -/
theorem relativeCartierKummer_realization (P : PurityFiniteSetting.{u})
    {B T D : Scheme.{u}} (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (v : T ⟶ B) (d : ℕ) [SmoothOfRelativeDimension d v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) [Smooth (i ≫ v)]
    (_hcodim : ∀ z : D, ringKrullDim (T.presheaf.stalk (i z)) =
      ringKrullDim (D.presheaf.stalk z) + (1 : WithBot ℕ∞)) :
    Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit (v ≫ b))
        (P.agreementCartierEtale (v ≫ b) i hI) ∧
    (∃ κR : Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.relativeCartierRootRing) i).obj
        (Etale.ordinaryFiniteConstant P.relativeCartierRootRing D))
      (P.relativeCartierRoots T) 2,
      Etale.SupportedKummerBoundary P.relativeCartierRootRing P.diagonalExponent
        P.relativeCartierRootZero i hI (P.diagonalExponent_isUnit (v ≫ b)) κR ∧
      Etale.SupportedKummerScalar P.relativeCartierScalar P.diagonalExponent
        P.relativeCartierRootZero P.diagonalExponent_annihilates i κR
          (P.agreementCartierEtale (v ≫ b) i hI)) ∧
    (∃ q : P.frameTwist T 1 ≅ P.relativeCartierProLine T,
      P.RelativeCartierRootNormalized T q ∧
      IsIso (SupportedConstantNormalization.gamma P.Coefficient i) ∧
      functorialCupExactHom
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T) 2
          (P.agreementCartierEtale (v ≫ b) i hI).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map q.hom)⟦(2 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map
        (SupportedConstantNormalization.gamma P.Coefficient i) ≫
          P.relativeCartierProMap (v ≫ b) i hI) ∧
    P.generalDivisorClass (v ≫ b) i hI = P.agreementCartierMap (v ≫ b) i hI ∧
    ∀ (U : Scheme.{u}) (e : U ⟶ T) [Etale e] (f : Γ(U, ⊤))
      (t : U.zeroLocusSubscheme {f} ⟶ D)
      (sq : ChosenCartesianSquare t (U.zeroLocusSubschemeι {f}) i e),
      HEq (P.functorialCupPullback true i (U.zeroLocusSubschemeι {f}) e t sq
        (v ≫ b) 2 1 (P.generalDivisorClass (v ≫ b) i hI))
        (-(P.frameBoundary U (e ≫ v ≫ b) f)) := by sorry

end WeilConjectures.PurityFiniteSetting
