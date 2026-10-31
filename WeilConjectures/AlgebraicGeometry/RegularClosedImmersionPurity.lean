/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityConventions
public import WeilConjectures.AlgebraicGeometry.PurityFrameClass
public import WeilConjectures.AlgebraicGeometry.FrameProductOnSupport
public import WeilConjectures.AlgebraicGeometry.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.AffineSpaceZeroSectionPurity
public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteExceptionalComposition
public import WeilConjectures.AlgebraicGeometry.AdicSmoothDualizingFinitePowers
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection

/-! # Purity and the normalized class of a regular closed immersion

Source: latest blueprint, sec-smooth-purity/sk-thm-regular/_section.md,
clauses (a)--(d) and proof Steps 1--5 (blueprint: sk-thm-regular).

Classes use the published supported Hom, concrete Kummer boundaries, and exact
site comparison. The closed exceptional adjunction gives the map sending one
to the class. Its right adjoint is the existing sections-with-support functor;
on the constructible domain this is the canonical closed presentation of Ri!.
The signed smooth comparison is stated by its tensor/projection/counit equation,
which uniquely characterizes the comparison assembled in proof Steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.RegularClosedImmersionPurity

/-- The canonical Cartesian square associated to a scheme-theoretic frame.
Source: the frame paragraph (blueprint: sk-thm-regular). -/
def frameSquare {Z X : Scheme.{u}} {i : Z ⟶ X} {c : ℕ} (F : i.EtaleFrame c) :
    ChosenCartesianSquare F.toZ (F.U.zeroLocusSubschemeι (Set.range F.f)) i F.e where
  w := F.isPullback.w
  isoPullback := F.isPullback.isoPullback
  hom_fst := F.isPullback.isoPullback_hom_fst
  hom_snd := F.isPullback.isoPullback_hom_snd

/-- Restriction to every frame is its actual ordered product of individual
Kummer support boundaries. The empty product is included.
Source: clause (b), displayed class formula (blueprint: sk-thm-regular). -/
def IsFundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : P.FunctorialCupH true i (2 * (c : ℤ)) c) : Prop :=
  ∀ F : i.EtaleFrame c,
    P.functorialCupPullback true i (F.U.zeroLocusSubschemeι (Set.range F.f))
      F.e F.toZ (frameSquare F) aX (2 * (c : ℤ)) c α =
        P.frameBoundaryProduct F.U (F.e ≫ aX) c F.f

/-- The complementary open is the actual scheme-theoretic closed support's
open complement. Source: localization used in (a) (blueprint: sk-thm-regular). -/
abbrev complement {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  i.openComplement.ι

/-- The existing closed exceptional inverse image, with its canonical support
construction. Source: clause (a) and proof Step 2b (blueprint: sk-thm-regular). -/
def exceptional (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  (closedUpperShriek (ModuleCat.{u + 1} P.Coefficient) i (complement i)).rightDerivedFunctor

/-- The shifted Tate input A_X(c)[2c].
Source: clause (a) (blueprint: sk-thm-regular). -/
abbrev input (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :=
  P.functorialCupTarget true X (2 * (c : ℤ)) c

/-- The exceptional target Ri!A_X(c)[2c].
Source: clause (a) (blueprint: sk-thm-regular). -/
abbrev value (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ) :=
  (exceptional P i).obj (input P X c)

/-- The actual constant coefficient complex in degree zero.
Source: clause (c) (blueprint: sk-thm-regular). -/
abbrev unit (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  (P.functorialCupSingle true X).obj (P.constant X)

/-- Canonical derived closed pushforward in degree zero, followed by the
exceptional adjunction. This is the supported-cohomology identification of (a)
and sends a supported class to its map A_Z -> Ri!A_X(c)[2c].
Source: proof Step 2b and clause (c) (blueprint: sk-thm-regular). -/
def classAdjunction (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact (complement i)] (c : ℕ) :
    P.FunctorialCupH true i (2 * (c : ℤ)) c ≃ (unit P Z ⟶ value P i c) :=
  let hj := eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι
  letI := preservesFiniteColimits_lowerStar_of_isCompl
    (R := P.Coefficient) i (complement i) hj
  let F := lowerStar (ModuleCat.{u + 1} P.Coefficient) i
  let e := AffineZeroPurity.closedSingleComparison F F.rightDerivedFunctor (Iso.refl _)
    (P.constant Z)
  e.homFromEquiv.symm.trans ((derivedLowerStarClosedUpperShriekAdjunction
    (R := P.Coefficient) i (complement i) hj).homEquiv _ _)

/-- The degree-zero sections map induced by H^0 and evaluation on one. This is
canonical even before the concentration assertion has been proved.
Source: clause (a), H^0 = Gamma(H^0) (blueprint: sk-thm-regular). -/
def homToSections (P : PurityFiniteSetting.{u}) (Z : Scheme.{u})
    (K : P.FunctorialCupDerived true Z) (f : unit P Z ⟶ K) :
    (globalSectionsFunctor (ModuleCat.{u + 1} P.Coefficient) Z).obj
      ((DerivedCategory.homologyFunctor _ 0).obj K) :=
  let h := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (P.functorialCupSheaves true Z) 0).inv.app (P.constant Z) ≫
      (DerivedCategory.homologyFunctor _ 0).map f
  ((constantSheafAdj (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} P.Coefficient)
    (Scheme.ProEt.isTerminalMkId Z)).homEquiv _ _
      ((cupConstantIso P Z).inv ≫ h)) 1

/-- The Kummer frame classes glue uniquely, with no relative-dimension constraint
on a connected component and no chosen global frame.
Source: clause (b), proof Step 3 (blueprint: sk-thm-regular).
Proof: smooth purity and co-projection give degree-zero concentration locally on
each component. The supported adjunction reads frame classes as sections of its
H^0 sheaf. On common refinements the generating tuples differ by local elementary
operations: unit scaling has zero extra boundary, transpositions of degree-two
factors have sign one, and affine-line homotopy identifies shear endpoints.
Therefore the classes agree on overlaps. Regularity supplies local frames; the
sheaf axiom glues their sections uniquely. The empty tuple gives the unit when
c=0, and the empty support gives its unique zero class. -/
theorem existsUnique_fundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! α : P.FunctorialCupH true i (2 * (c : ℤ)) c,
      IsFundamentalClass P i aX c α := by
  sorry

/-- The uniquely specified glued class; choice is applied only to the unique
class characterized by its actual Kummer-frame restrictions.
Source: clause (b) (blueprint: sk-thm-regular). -/
def fundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    P.FunctorialCupH true i (2 * (c : ℤ)) c :=
  (existsUnique_fundamentalClass P i aX c hreg hZ).exists.choose

/-- The exact conclusion of clauses (a)--(c), with derived technical instances
installed inside a named predicate so no opaque let occurs in a theorem signature.
Source: clauses (a)--(c) (blueprint: sk-thm-regular). -/
def purityConclusion (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) : Prop :=
    letI := isNoetherian_of_locallyOfFiniteType aX
    IsFundamentalClass P i aX c (fundamentalClass P i aX c hreg hZ) ∧
      IsIso (classAdjunction P i c
        (fundamentalClass P i aX c hreg hZ)) ∧
      (∀ r : ℤ, r ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj
        (value P i c))) ∧
      IsIso ((DerivedCategory.homologyFunctor _ 0).map
        (classAdjunction P i c (fundamentalClass P i aX c hreg hZ))) ∧
      Function.Bijective (homToSections P Z (value P i c))

/-- Purity, stalkwise generation, and the canonical degree-zero sections
identification. The image of one is the uniquely glued fundamental class.
Source: clauses (a)--(c), proof Steps 1--4 (blueprint: sk-thm-regular).
Proof: on constant-dimension pieces smooth purity computes omega_X and omega_Z.
Exceptional composition identifies omega_Z with Ri!omega_X; co-projection
cancels their invertible Tate shifts, showing degree-zero rank one. The closed
adjunction identifies supported cohomology with Hom(A_Z,Ri!A_X(c)[2c]).
Etale coordinates reduce the specified frame class to the affine zero-section
product. Its adjoint is invertible by affine-space zero-section purity.
Restrictions detect isomorphisms, so the global class map is an isomorphism.
Its H^0 map is therefore an isomorphism, expressing generation at every geometric
point. All other cohomology sheaves vanish, and concentration makes the natural
H^0 sections map bijective. Apply the same argument on every etale neighborhood;
no positive codimension or nonemptiness is used. -/
theorem regularImmersion_purity (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    purityConclusion P i aX c hreg hZ := by
  sorry

/-- The exact conclusion of clause (a), supported adjunction, with derived technical instances
installed inside a named predicate so no opaque let occurs in a theorem signature.
Source: clause (a), supported adjunction (blueprint: sk-thm-regular). -/
def closedComparisonConclusion (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) : Prop :=
    letI := isNoetherian_of_locallyOfFiniteType aX
    ∃ hK : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) X (input P X c),
    ∃! e : value P i c ≅ (ProEtale.rightDerivedUpperShriek P.Coefficient i).obj (input P X c),
      ∀ (M : P.FunctorialCupDerived true Z)
        (hM : ProEtale.DerivedCategory.plusEtaleOrigin
          (ModuleCat.{u + 1} P.Coefficient) Z M) (x : M ⟶ value P i c),
        x ≫ e.hom = closedUpperShriekHomEquivRightDerivedUpperShriek
          i (complement i) (eq_compl_iff_isCompl.mp i.range_eq_compl_range_openComplement_ι)
          hM hK.plusEtaleOrigin.plus x

/-- The full closed-support presentation is canonically the recorded constructible
exceptional inverse image, with its adjunction-normalized comparison retained.
Source: (a), proof Step 2b (blueprint: sk-thm-regular).
Proof: the finite Tate sheaf is locally free of rank one, hence its shifted
complex is bounded constructible. The published closed-support comparison
represents on every bounded-below etale-origin M the bijection obtained by
identifying Ri_! with Ri_* and applying the exceptional adjunction. Both
exceptional objects are of this kind. Yoneda gives the unique isomorphism
whose postcomposition is that bijection. Thus the map in regularImmersion_purity
is a map into the recorded Ri!, with precisely the same supported adjunct. -/
theorem closedExceptional_comparison (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] (c : ℕ) :
    closedComparisonConclusion P i aX c := by
  sorry

/-- Every etale neighborhood has the same concentrated rank-one exceptional
object, and restriction of the global class has the prescribed frame restrictions.
This includes neighborhoods that are not quasi-compact or separated over k.
Source: clauses (a),(b),(d), proof Steps 2b, 3, 5a (blueprint: sk-thm-regular).
Proof: etale base change preserves the affine regular sequences, smoothness of
X, and regularity of Z. Kummer classes, their individual localization boundaries,
and the ordered supported product commute with pullback. Apply the same local
smooth-purity and zero-section calculation on this neighborhood. Degree-zero
concentration and its rank-one generator are local and hence descend without
a quasi-compactness assumption on the neighborhood. -/
theorem etale_local_purity (P : PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (e : U ⟶ X) [Etale e] :
    IsFundamentalClass P (pullback.snd i e) (e ≫ aX) c
      (P.functorialCupPullback true i (pullback.snd i e) e (pullback.fst i e)
        { w := pullback.condition, isoPullback := Iso.refl _,
          hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
        aX (2 * (c : ℤ)) c (fundamentalClass P i aX c hreg hZ)) ∧
      ∃ hj : QuasiCompact (complement (pullback.snd i e)),
        IsIso (@classAdjunction P _ _ (pullback.snd i e) _ hj c
          (P.functorialCupPullback true i (pullback.snd i e) e (pullback.fst i e)
            { w := pullback.condition, isoPullback := Iso.refl _,
              hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
            aX (2 * (c : ℤ)) c (fundamentalClass P i aX c hreg hZ))) ∧
        (∀ r : ℤ, r ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ r).obj
          (value P (pullback.snd i e) c))) ∧
        Function.Bijective (homToSections P (pullback i e) (value P (pullback.snd i e) c)) ∧
        ∀ β : P.FunctorialCupH true (pullback.snd i e) (2 * (c : ℤ)) c,
          IsFundamentalClass P (pullback.snd i e) (e ≫ aX) c β →
          β = P.functorialCupPullback true i (pullback.snd i e) e (pullback.fst i e)
            { w := pullback.condition, isoPullback := Iso.refl _,
              hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
            aX (2 * (c : ℤ)) c (fundamentalClass P i aX c hreg hZ) := by
  sorry

/-- The explicit class base-change equality on any separated finite-type
etale neighborhood. Source: clause (d), proof Step 5a (blueprint: sk-thm-regular).
Proof: pulling back a frame pulls back its Kummer units, localization boundaries
and ordered product. Thus the restricted global class satisfies the defining
frame property of the base-changed pair. Uniqueness of gluing identifies it
with that pair's fundamental class. -/
theorem fundamentalClass_etale (P : PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (e : U ⟶ X) [Etale e] [IsSeparated (e ≫ aX)] [QuasiCompact (e ≫ aX)]
    :
    ∃ hregU : PurityConventions.IsRegularOfPureCodimension (pullback.snd i e) c,
      ∃ hZU : ∀ z : ↥(pullback i e), IsRegularLocalRing ((pullback i e).presheaf.stalk z),
    P.functorialCupPullback true i (pullback.snd i e) e (pullback.fst i e)
      { w := pullback.condition, isoPullback := Iso.refl _,
        hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
      aX (2 * (c : ℤ)) c (fundamentalClass P i aX c hreg hZ) =
        fundamentalClass P (pullback.snd i e) (e ≫ aX) c hregU hZU := by
  sorry

/-- The frame class on a global generating tuple, with only its source support
transported. In particular, applying this to the coordinate tuple gives exactly
the affine-space zero-section generator, and in rank one its Kummer boundary.
Source: clause (b), zero-section parenthesis (blueprint: sk-thm-regular).
Proof: a scheme-theoretic presentation by f gives the identity etale frame after
the unique identification of its zero scheme with Z. Specialize the defining
frame restriction of the global class to this frame. Identity pullback is the
identity by the normalized coefficient restriction, leaving the displayed source
transport. For affine space the f are its coordinates; their ordered product is
precisely the recorded zero-section supported class, including the empty product. -/
theorem fundamentalClass_globalFrame (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (f : Fin c → Γ(X, ⊤)) (e : X.zeroLocusSubscheme (Set.range f) ≅ Z)
    (he : e.hom ≫ i = X.zeroLocusSubschemeι (Set.range f)) :
    fundamentalClass P i aX c hreg hZ = P.frameProductOnSupport i aX c f e he := by
  sorry

/-- Canonical realization of a signed Tate target, with its actual shift.
Source: finite site comparison in clause (c) (blueprint: sk-thm-regular). -/
def targetComparison (P : PurityFiniteSetting.{u}) (Z : Scheme.{u}) (a r : ℤ) :
    (P.functorialCupComparisonFunctor Z).mapDerivedCategory.obj
      (P.functorialCupTarget false Z a r) ≅ P.functorialCupTarget true Z a r :=
  let F := P.functorialCupComparisonFunctor Z
  (F.mapDerivedCategory.commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso ((F.mapDerivedCategorySingleFunctor 0).app _)

set_option maxHeartbeats 800000 in
-- The published root-tensor comparison unfolds several derived-site layers.
/-- Compare the coordinate construction's higher-exponent shifted line with the
frame line through their common inverse-limit root tensor, using the two
canonical root-projection comparisons, with exact single and shift identifications.
Source: clause (b), zero-section normalization (blueprint: sk-thm-regular). -/
def coordinateLineMap (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    AffineSpacePurity.shiftedLine (AffineZeroPurity.setting P n) X ⟶
      input (AffineZeroPurity.setting P n) X 1 :=
  let Q := AffineZeroPurity.setting P n
  let hX := AffineLinePurity.primeUnit Q X aX
  (VectorIntegrationSite.twistDerived P.coefficients.l P.extension n X hX
    (n + 1) (AffineSpacePurity.annihilates Q) 1 2).hom ≫
    (VectorIntegrationSite.twistDerived P.coefficients.l P.extension n X hX
      n Q.diagonalExponent_annihilates 1 2).inv ≫
    (targetComparison Q X 2 1).hom

/-- Canonical ordered comparison of the coordinate target with A(c)[2c].
It starts with the zero-shift unit and appends the root-normalized line, using
exactly the published right-shift-first tensor comparison and frame multiplication.
Source: clause (b), zero-section normalization (blueprint: sk-thm-regular). -/
def coordinateTargetMap (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    (c : ℕ) → AffineZeroPurity.target P n X c ⟶
      input (AffineZeroPurity.setting P n) X c
  | 0 => (shiftFunctorZero _ ℤ).inv.app _
  | c + 1 =>
    let Q := AffineZeroPurity.setting P n
    let T := @curriedTensor (CupDerivedCategory Q X) _ (cupMonoidal Q X)
    (T.map (coordinateTargetMap P n X aX c)).app _ ≫
      (T.obj (input Q X c)).map (coordinateLineMap P n X aX) ≫
      (cupTensorShiftIso ((cupSingle Q X).obj (Q.frameTwist X c))
        ((cupSingle Q X).obj (Q.frameTwist X 1)) (2 * (c : ℤ)) 2).hom ≫
      (shiftFunctor _ (2 * (c : ℤ) + 2)).map (Q.frameTensorNext X c) ≫
      (eqToIso (congrArg (fun j : ℤ ↦
        ((cupSingle Q X).obj (Q.frameTwist X (c + 1)))⟦j⟧)
        (PurityFiniteSetting.frameDegreeNext c))).hom

/-- The actual zero-section generator is the frame-glued fundamental class under
its canonical target comparison.  The quantified equality identifies every class
with the defining frame restrictions with this specific `supportedClass` map.
It applies to every separated finite-type base; c=1 is the stated pur_s and c=0
is the empty product.
Source: clause (b), zero-section parenthesis (blueprint: sk-thm-regular).
Proof: the root-power transition preserves the scalar Kummer class. Exact site
comparison and the localization boundary therefore identify each coordinate
factor. The tensor/shift comparisons defining coordinateTargetMap identify their
ordered products, including the coefficient-unit start. The unique support
isomorphism over the zero section is supportIso, so its source transport agrees
with the frame transport. These maps commute with etale restriction, giving
IsFundamentalClass. Uniqueness follows by checking equality on the coordinate
frame; the tensor factors are locally free lines, so coordinateTargetMap is an iso. -/
theorem fundamentalClass_zeroSection_supportedClass
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB] (c : ℕ) :
    IsIso (coordinateTargetMap P n (iteratedAffineLine B c)
      (AffineSpacePurity.towerBase aB c) c) ∧
    IsFundamentalClass (AffineZeroPurity.setting P n) (AffineZeroPurity.zero B c)
      (AffineSpacePurity.towerBase aB c) c
      (AffineZeroPurity.supportedClass P n B aB c ≫
        coordinateTargetMap P n (iteratedAffineLine B c)
          (AffineSpacePurity.towerBase aB c) c) ∧
    ∀ α : (AffineZeroPurity.setting P n).FunctorialCupH true
        (AffineZeroPurity.zero B c) (2 * (c : ℤ)) c,
      IsFundamentalClass (AffineZeroPurity.setting P n) (AffineZeroPurity.zero B c)
        (AffineSpacePurity.towerBase aB c) c α →
      α = AffineZeroPurity.supportedClass P n B aB c ≫
        coordinateTargetMap P n (iteratedAffineLine B c)
          (AffineSpacePurity.towerBase aB c) c := by
  sorry

/-- Frame classes and their gluing also exist for a regular closed immersion
without the smoothness/regularity assumptions used to prove the purity isomorphism.
Source: clause (b), regular-immersion parenthesis (blueprint: sk-thm-regular).
Proof: the local complete intersection class is the ordered Kummer support-boundary
product. Deformation to the normal bundle gives the global class: the normal bundle
has its zero-section class defined by these coordinate boundaries; specialization
along the deformation transports it to the immersion. Localization functoriality
identifies its restrictions with the original products. Elementary changes of regular
generators preserve the product, so the local descriptions agree. No assertion that
the associated map is invertible is made in this generality. -/
theorem exists_fundamentalClass_regular (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c) :
    ∃ α : P.FunctorialCupH true i (2 * (c : ℤ)) c, IsFundamentalClass P i aX c α := by
  sorry

/-- The ordinary representative is uniquely fixed by finite etale/pro-etale comparison.
Source: supported adjunction in (a), Step 2b (blueprint: sk-thm-regular).
Proof: the support constant and finite Tate target are bounded below etale-origin
complexes. The derived site comparison is fully faithful on these objects. The
canonical source and target comparisons identify its Hom bijection with the
published functorialCupCompare, so the given global class has exactly one lift. -/
theorem existsUnique_ordinaryClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    ∃! α : P.FunctorialCupH false i (2 * (c : ℤ)) c,
      P.functorialCupCompare i (2 * (c : ℤ)) c α = fundamentalClass P i aX c hreg hZ := by
  sorry

/-- The uniquely characterized ordinary lift, rather than an arbitrary choice of class.
Source: (a),(c), Step 2b (blueprint: sk-thm-regular). -/
def ordinaryFundamentalClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    P.FunctorialCupH false i (2 * (c : ℤ)) c :=
  (existsUnique_ordinaryClass P i aX c hreg hZ).exists.choose

/-- Addition of ordered shifted root powers, using only associativity and the
unit comparison. Source: twist cancellation in Step 2 (blueprint: sk-thm-regular). -/
def orderedPowerAdd (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (c : ℕ) :
    (m : ℕ) → ((Etale.ordinaryFiniteTensor P.Coefficient X).obj
      (P.diagonalTwistEtale X c)).obj (P.diagonalTwistEtale X m) ≅
        P.diagonalTwistEtale X (c + m)
  | 0 => Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} P.Coefficient) X _
  | m + 1 =>
    (Etale.derivedTensorAssociator (ModuleCat.{u + 1} P.Coefficient) X
      (P.diagonalTwistEtale X c) (P.diagonalTwistEtale X m)
      ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates X)⟦(2 : ℤ)⟧)).symm ≪≫
    (Etale.derivedTensorRight (ModuleCat.{u + 1} P.Coefficient) X
      ((Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates X)⟦(2 : ℤ)⟧)).mapIso (orderedPowerAdd P X c m)

/-- The ordinary supported representative, read as an Ri_! arrow and in the
same ordered shifted-root presentation as the specified smooth orientations.
Source: Steps 1--2 and the comparison in (c) (blueprint: sk-thm-regular). -/
def ordinaryClass (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : P.FunctorialCupH false i (2 * (c : ℤ)) c) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i).obj
      (Etale.ordinaryFiniteUnit P.Coefficient Z) ⟶ P.diagonalTwistEtale X c :=
  letI := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom P.Coefficient i
  AffineZeroPurity.closedSingleComparison
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i) _
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} P.Coefficient) i) (P.constantEtale Z) |>.hom ≫
    α ≫ (AdicSmoothDualizing.etalePowerComparison P X (P.diagonalExponent_isUnit aX) c).inv

/-- The signed Tate evaluation, with the actual coefficient multiplication and
right-shift-first tensor comparison. Source: twist cancellation in (c)
(blueprint: sk-thm-regular). -/
def twistEvaluation (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (a b r s : ℤ) (ha : a + b = 0) (hr : r + s = 0) :
    ((Etale.ordinaryFiniteTensor P.Coefficient X).obj
      (P.functorialCupTarget false X a r)).obj (P.functorialCupTarget false X b s) ⟶
        Etale.ordinaryFiniteUnit P.Coefficient X :=
  (cupTensorShiftIso
      ((P.functorialCupSingle false X).obj (P.functorialCupTwist false X r))
      ((P.functorialCupSingle false X).obj (P.functorialCupTwist false X s)) a b).hom ≫
    (cupSingleTensorMap (hD := P.functorialCupHasDerived false X)
      (hDM := P.functorialCupDerivedMonoidal false X)
      (P.functorialCupTwist false X r) (P.functorialCupTwist false X s) ≫
      (P.functorialCupSingle false X).map
        (P.functorialCupTwistProduct false X aX r s).hom)⟦a+b⟧' ≫
    eqToHom (congrArg₂ (fun r a ↦ P.functorialCupTarget false X a r) hr ha) ≫
    (shiftFunctorZero _ ℤ).hom.app (Etale.ordinaryFiniteUnit P.Coefficient X)

/-- Exact pullback of the actual signed Tate target, including its shift.
Source: co-projection's twist restriction in (c) (blueprint: sk-thm-regular). -/
def ordinaryTargetPullback (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) (aX : X ⟶ Spec (.of P.field.k)) (a r : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor.obj
      (P.functorialCupTarget false X a r) ≅ P.functorialCupTarget false Z a r :=
  let F := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ i).app _ ≪≫
    (F.mapDerivedCategory.commShiftIso a).app _ ≪≫
    (shiftFunctor _ a).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (P.functorialCupSingle false Z).mapIso (P.functorialCupTwistPullback false i aX r))

/-- The ordinary exceptional adjunct of the same supported class, in the signed
single-sheaf Tate presentation. Source: (a),(c) (blueprint: sk-thm-regular). -/
def ordinaryAdjunct (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : P.FunctorialCupH false i (2 * (c : ℤ)) c) :=
  (Etale.rightDerivedUpperShriekAdjunction P.Coefficient i).homEquiv _ _
    (ordinaryClass P i aX c α ≫
      (AdicSmoothDualizing.etalePowerComparison P X (P.diagonalExponent_isUnit aX) c).hom)

/-- Untwist and invert the class using the canonical co-projection. Every arrow
is specified: Tate evaluation, co-projection adjoint to projection, inverse of
the given class, tensor unitor, and root-normalized Tate restriction.
Source: clause (c), equivalent untwisted isomorphism (blueprint: sk-thm-regular). -/
def ordinaryUntwisting (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ)
    (α : P.FunctorialCupH false i (2 * (c : ℤ)) c)
    [IsIso (ordinaryAdjunct P i aX c α)]
    [IsIso (twistEvaluation P X aX (2 * (c : ℤ)) (-(2 * (c : ℤ))) c (-(c : ℤ))
      (add_neg_cancel _) (add_neg_cancel _))]
    [IsIso (twistEvaluation P X aX (-(2 * (c : ℤ))) (2 * (c : ℤ)) (-(c : ℤ)) c
      (neg_add_cancel _) (neg_add_cancel _))] :
    P.diagonalOrdinaryDualizing i ⟶ P.functorialCupTarget false Z (-(2 * (c : ℤ))) (-(c : ℤ)) :=
  let L := P.functorialCupTarget false X (2 * (c : ℤ)) c
  let M := P.functorialCupTarget false X (-(2 * (c : ℤ))) (-(c : ℤ))
  let e := asIso (twistEvaluation P X aX (2 * (c : ℤ)) (-(2 * (c : ℤ))) c (-(c : ℤ))
    (add_neg_cancel _) (add_neg_cancel _))
  let e' := asIso (twistEvaluation P X aX (-(2 * (c : ℤ))) (2 * (c : ℤ)) (-(c : ℤ)) c
    (neg_add_cancel _) (neg_add_cancel _))
  let Q := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) i).leftDerivedFunctor
  (Etale.rightDerivedUpperShriek P.Coefficient i).map e.inv ≫
    (Etale.derivedTensorRightCompRightDerivedUpperShriekIsoOfTensorIso
      P.Coefficient i M L e e').hom.app L ≫
    ((Etale.ordinaryFiniteTensor P.Coefficient Z).map
      (inv (ordinaryAdjunct P i aX c α))).app (Q.obj M) ≫
    (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} P.Coefficient) Z _).hom ≫
    (ordinaryTargetPullback P i aX (-(2 * (c : ℤ))) (-(c : ℤ))).hom

/-- The exact conclusion of clause (c), negative Tate shift, with derived technical instances
installed inside a named predicate so no opaque let occurs in a theorem signature.
Source: clause (c), negative Tate shift (blueprint: sk-thm-regular). -/
def untwistedConclusion (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) : Prop :=
    letI := isNoetherian_of_locallyOfFiniteType aX
    let α := ordinaryFundamentalClass P i aX c hreg hZ
    ∃ hc : IsIso (ordinaryAdjunct P i aX c α),
      ∃ he : IsIso (twistEvaluation P X aX (2 * (c : ℤ)) (-(2 * (c : ℤ))) c (-(c : ℤ))
        (add_neg_cancel _) (add_neg_cancel _)),
      ∃ he' : IsIso (twistEvaluation P X aX (-(2 * (c : ℤ))) (2 * (c : ℤ)) (-(c : ℤ)) c
        (neg_add_cancel _) (neg_add_cancel _)),
      letI := hc
      letI := he
      letI := he'
      IsIso ((P.diagonalDualizingComparison i).hom ≫
        (P.functorialCupComparisonFunctor Z).mapDerivedCategory.map
          (ordinaryUntwisting P i aX c α) ≫
        (targetComparison P Z (-(2 * (c : ℤ))) (-(c : ℤ))).hom)

/-- The pro-etale untwisting map, transported by the specified exceptional site
comparison. It is the inverse of cl_i(-c)[-2c], not an unspecified isomorphism.
Source: clause (c), finite etale-origin realization (blueprint: sk-thm-regular).
Proof: finite comparison carries the uniquely lifted supported class and its
adjunct to cl_i. The Tate evaluation maps are isomorphisms since each finite
root line is locally free of rank one and its negative twist is its dual.
The ordinary adjunct is an isomorphism by the coordinate purity calculation.
Co-projection for the negative Tate line moves that line through Ri!. Its
canonical projection/counit construction is exactly the composite in
ordinaryUntwisting. Inverting the adjunct, evaluating the unit tensor, and
restricting the negative line therefore gives the inverse of the twisted
class. Every factor is invertible. Exact monoidal site comparison preserves
these factors and the exceptional adjunction, proving the asserted pro-etale
isomorphism with the specified inverse normalization. -/
theorem untwisted_purity (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    untwistedConclusion P i aX c hreg hZ := by
  sorry

/-- The exact conclusion of clause (c), signed smooth comparison, with derived technical instances
installed inside a named predicate so no opaque let occurs in a theorem signature.
Source: clause (c), signed smooth comparison (blueprint: sk-thm-regular). -/
def smoothComparisonConclusion (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    : Prop :=
    letI := isNoetherian_of_locallyOfFiniteType aX
    letI := isNoetherian_of_locallyOfFiniteType (i ≫ aX)
    ∃ α : P.FunctorialCupH false i (2 * (c : ℤ)) c,
      P.functorialCupCompare i (2 * (c : ℤ)) c α = fundamentalClass P i aX c hreg hZ ∧
      ∀ (n m : ℕ) (hm : c + m = n)
        (θX : P.diagonalOrdinaryDualizing aX ≅ P.diagonalTwistEtale X n)
        (θZ : P.diagonalOrdinaryDualizing (i ≫ aX) ≅ P.diagonalTwistEtale Z m),
        P.DiagonalOrientationNormalization n aX (𝟙 _) θX →
        P.DiagonalOrientationNormalization m (i ≫ aX) (𝟙 _) θZ →
        ∀ t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates,
        ((Etale.ordinaryFiniteTensor P.Coefficient X).map
            (ordinaryClass P i aX c α)).app (P.diagonalTwistEtale X m) ≫
          (orderedPowerAdd P X c m).hom ≫
          (eqToIso (congrArg (P.diagonalTwistEtale X) hm)).hom ≫ θX.inv =
        ((-1 : ℤ) ^ c) •
          (((Etale.projectionMap (ModuleCat.{u + 1} P.Coefficient) i).app
              (Etale.ordinaryFiniteUnit P.Coefficient Z)).app (P.diagonalTwistEtale X m) ≫
            (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) i).map
              ((Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} P.Coefficient) Z _).hom ≫
                (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
                  P.diagonalExponent P.diagonalExponent_annihilates t i
                  (P.diagonalExponent_isUnit aX) m).hom ≫ θZ.inv ≫
                (PurityFiniteSetting.finiteExceptionalComposition P.Coefficient i aX).hom.app
                  (Etale.ordinaryFiniteUnit P.Coefficient (Spec (.of P.field.k)))) ≫
            (Etale.rightDerivedUpperShriekAdjunction P.Coefficient i).counit.app
              (P.diagonalOrdinaryDualizing aX))

/-- The signed equality with the smooth-purity comparison, expressed without
choosing an unspecified isomorphism Phi. Tensoring a supported map with A(m)[2m]
and applying projection is an injective comparison: its right side is exactly
Ri_!(Pi_Z^-1), exceptional composition, and the actual exceptional counit.
Thus this equation says cl_i=(-1)^c Phi_i. Both smooth orientations are the
specified, coordinate-normalized orientations, universally quantified in the
conclusion; no additional choice of orientation is a hypothesis.
Source: current clause (c), proof Steps 1, 2 and 4 (blueprint: sk-thm-regular).
Proof: etale coordinates reduce to the zero section of A^c over A^m. Composition
coherence cancels the orientation on the base. The projective-line trace sends
the Cartier class to one, whereas the chosen support boundary is its negative.
The c-fold coordinate product therefore has trace (-1)^c. Naturality of roots,
boundaries and support products transports this identity to every chart.
Degree-zero descent glues it. For c=0 both composites are the unit identity.
For dimensions varying among components apply the equality on each constant-
dimension piece; these pieces cover X along Z and so determine the assembled map. -/
theorem fundamentalClass_smooth_comparison (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (aX : X ⟶ Spec (.of P.field.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [Smooth aX]
    (c : ℕ) (hreg : PurityConventions.IsRegularOfPureCodimension i c)
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    :
    smoothComparisonConclusion P i aX c hreg hZ := by
  sorry

/-- The exact conclusion of clause (d), exterior product, with derived technical instances
installed inside a named predicate so no opaque let occurs in a theorem signature.
Source: clause (d), exterior product (blueprint: sk-thm-regular). -/
def productConclusion (P : PurityFiniteSetting.{u})
    {Z₁ X₁ Z₂ X₂ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (a₁ : X₁ ⟶ Spec (.of P.field.k)) (a₂ : X₂ ⟶ Spec (.of P.field.k))
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁] [Smooth a₁]
    [IsSeparated a₂] [LocallyOfFiniteType a₂] [QuasiCompact a₂] [Smooth a₂]
    (c₁ c₂ : ℕ)
    (hreg₁ : PurityConventions.IsRegularOfPureCodimension i₁ c₁)
    (hreg₂ : PurityConventions.IsRegularOfPureCodimension i₂ c₂)
    (hZ₁ : ∀ z : Z₁, IsRegularLocalRing (Z₁.presheaf.stalk z))
    (hZ₂ : ∀ z : Z₂, IsRegularLocalRing (Z₂.presheaf.stalk z)) : Prop :=
    let i₁₂ := pullback.map (i₁ ≫ a₁) (i₂ ≫ a₂) a₁ a₂ i₁ i₂ (𝟙 _)
      (by simp) (by simp)
    letI : IsClosedImmersion i₁₂ := IsClosedImmersion.pullback_map i₁ i₂ rfl rfl
    let a₁₂ := pullback.fst a₁ a₂ ≫ a₁
    let j₁ := pullback.snd i₁ (pullback.fst a₁ a₂)
    let j₂ := pullback.snd i₂ (pullback.snd a₁ a₂)
    ∃ hreg₁₂ : PurityConventions.IsRegularOfPureCodimension i₁₂ (c₁ + c₂),
      ∃ hZ₁₂ : ∀ z : ↥(pullback (i₁ ≫ a₁) (i₂ ≫ a₂)),
        IsRegularLocalRing ((pullback (i₁ ≫ a₁) (i₂ ≫ a₂)).presheaf.stalk z),
      ∀ (e : pullback (i₁ ≫ a₁) (i₂ ≫ a₂) ≅ pullback j₁ j₂)
        (he : e.hom ≫ ProEtale.cupIntersection j₁ j₂ = i₁₂),
      P.functorialCupChangeSupport true (ProEtale.cupIntersection j₁ j₂) i₁₂ e.hom he
        (2 * ((c₁ + c₂ : ℕ) : ℤ)) (c₁ + c₂)
        (fundamentalClass P i₁₂ a₁₂ (c₁ + c₂) hreg₁₂ hZ₁₂) =
      P.functorialCupReindex true (ProEtale.cupIntersection j₁ j₂)
        (by push_cast; ring) (by rfl)
        (P.functorialCup true a₁₂ j₁ j₂ (2 * (c₁ : ℤ)) (2 * (c₂ : ℤ)) c₁ c₂
          (P.functorialCupPullback true i₁ j₁ (pullback.fst a₁ a₂) (pullback.fst _ _)
            { w := pullback.condition, isoPullback := Iso.refl _,
              hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
            a₁ (2 * (c₁ : ℤ)) c₁ (fundamentalClass P i₁ a₁ c₁ hreg₁ hZ₁))
          (P.functorialCupPullback true i₂ j₂ (pullback.snd a₁ a₂) (pullback.fst _ _)
            { w := pullback.condition, isoPullback := Iso.refl _,
              hom_fst := Category.id_comp _, hom_snd := Category.id_comp _ }
            a₂ (2 * (c₂ : ℤ)) c₂ (fundamentalClass P i₂ a₂ c₂ hreg₂ hZ₂)))

/-- Exterior products, including the assertion that the product is again a regular
pair of the sum codimension. The support identification is the unique isomorphism
over X1 x X2, and the right-hand side is the published pullback/cup composite.
Source: clause (d), proof Steps 5b--5c (blueprint: sk-thm-regular).
Proof: over the perfect ground field regular Z1 and Z2 are smooth. Their product
is smooth, hence regular. Flat base change preserves each affine regular sequence;
concatenating the two pulled-back sequences cuts out Z1 x Z2 and has length c1+c2.
The corresponding frame boundary product is the cup of the two factor products:
Kummer boundaries commute with pullback and the ordered tensor multiplication
associates. All factors have degree two, so no permutation sign is introduced.
The Cartesian intersection identifies the product closed support uniquely over
X1 x X2. The frame descriptions agree on a cover, and uniqueness of gluing gives
the stated equality. Empty factors and empty sequences obey the same unit formula. -/
theorem fundamentalClass_product (P : PurityFiniteSetting.{u})
    {Z₁ X₁ Z₂ X₂ : Scheme.{u}}
    (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (a₁ : X₁ ⟶ Spec (.of P.field.k)) (a₂ : X₂ ⟶ Spec (.of P.field.k))
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁] [Smooth a₁]
    [IsSeparated a₂] [LocallyOfFiniteType a₂] [QuasiCompact a₂] [Smooth a₂]
    (c₁ c₂ : ℕ)
    (hreg₁ : PurityConventions.IsRegularOfPureCodimension i₁ c₁)
    (hreg₂ : PurityConventions.IsRegularOfPureCodimension i₂ c₂)
    (hZ₁ : ∀ z : Z₁, IsRegularLocalRing (Z₁.presheaf.stalk z))
    (hZ₂ : ∀ z : Z₂, IsRegularLocalRing (Z₂.presheaf.stalk z)) :
    productConclusion P i₁ i₂ a₁ a₂ c₁ c₂ hreg₁ hreg₂ hZ₁ hZ₂ := by
  sorry

end WeilConjectures.RegularClosedImmersionPurity
