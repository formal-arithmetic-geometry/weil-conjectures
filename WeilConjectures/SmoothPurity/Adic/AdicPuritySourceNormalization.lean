/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTransitions
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars

/-! # Canonical finite source normalizations

(blueprint: def-pur-adic-finite-source-normalization).

Source: main-20261015, sec-smooth-purity/sk-thm-purity-transport,
thm-pur-adic-reconstruction.proof.md, common-bounds sentence and source-object argument.
(blueprint: lem-pur-adic-source-finiteness-reductions).

The helpers put the recorded direct quotient comparisons in the same coordinates.
Their data are quotient maps, adjunction transposes and the root-normalized finite
source comparison. In particular the finite normalization is defined independently
of the integral source reduction whose compatibility is asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The actual direct quotient ring diagram, with coefficients lifted to the site's size.
Source: adic coefficient datum, direct quotient paragraph
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicDirectQuotientRings {A : Type u} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj n := .of (ULift.{u + 1} (A ⧸ I ^ (n.unop + 1)))
  map {i j} f := CommRingCat.ofHom
    (Ideal.Quotient.factor (S := I ^ (i.unop + 1)) (T := I ^ (j.unop + 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))).ulift
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro ⟨x⟩
    exact congrArg ULift.up (DFunLike.congr_fun Ideal.Quotient.factor_eq x)
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro ⟨x⟩
    exact congrArg ULift.up (Ideal.Quotient.factor_comp_apply
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f.unop) 1))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom g.unop) 1)) x).symm

/-- Exact derived restriction with the published exactness witnesses supplied explicitly.
Source: adic coefficient datum, quotient normalization
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicDerivedCoefficientRestriction (W : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) :
    Scheme.proEtaleDerivedCategory W B ⥤ Scheme.proEtaleDerivedCategory W A :=
  letI := Scheme.proEtaleCoefficientRestrictScalars_preservesFiniteLimits W q
  letI := Scheme.proEtaleCoefficientRestrictScalars_preservesFiniteColimits W q
  (Scheme.proEtaleCoefficientRestrictScalars W q).mapDerivedCategory

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

/-- Identity-on-sections comparison of restriction along the sequence quotient and
along the direct quotient used by finite purity. Naturality of the identity comparison
of the two ring diagrams supplies the required equality for every pair of levels.
Source: adic coefficient datum, direct quotient paragraph
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicQuotientRestrictionIso (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes C.l E W h ≅
      purAdicDerivedCoefficientRestriction W
        ((purAdicFiniteSetting D C E m).finiteReductionRingHom (n + 1)
          (Nat.succ_pos n) (Nat.add_le_add_right h 1)) := by
  let Q := purAdicDirectQuotientRings
    (Ideal.span ({Padic.coefficientExtensionUniformizer C.l E} :
      Set (Padic.coefficientExtensionIntegers C.l E))) ⋙
    constantSheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1} ⋙
    sheafCompose _ (forget₂ CommRingCat RingCat)
  let e : integralCoefficientSheafSystem C.l E W ⟶ Q :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun k ↦ by
      simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp]
      rfl)
  let eq := (Category.comp_id _).symm.trans
    ((e.naturality (homOfLE h).op).trans (Category.id_comp _))
  let q := (purAdicFiniteSetting D C E m).finiteReductionRingHom (n + 1)
    (Nat.succ_pos n) (Nat.add_le_add_right h 1)
  letI : PreservesFiniteLimits (Scheme.proEtaleCoefficientRestrictScalars W q) :=
    Scheme.proEtaleCoefficientRestrictScalars_preservesFiniteLimits W q
  letI : PreservesFiniteColimits (Scheme.proEtaleCoefficientRestrictScalars W q) :=
    Scheme.proEtaleCoefficientRestrictScalars_preservesFiniteColimits W q
  let e₀ : normalizedDVRModuleRes C.l E W h ≅
      Scheme.proEtaleCoefficientRestrictScalars W
        ((purAdicFiniteSetting D C E m).finiteReductionRingHom (n + 1)
          (Nat.succ_pos n) (Nat.add_le_add_right h 1)) :=
    eqToIso (congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q) eq)
  exact Functor.mapDerivedCategoryNatIso e₀

/-- Canonical direct normalization red_m(M) tensor B_n -> red_n(M), defined by the
smaller quotient unit under the actual scalar-extension adjunction. Its transpose is
exactly the recorded reduction transition, with the identity-on-sections comparison.
Source: adic coefficient datum, K-flat balancing normalization
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicQuotientNormalization (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M : DerivedCategory (scalarReductionSource C.l E W)) :
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) W).obj
        ((scalarReductionDerivedExtension C.l E W m).obj M) ⟶
      (scalarReductionDerivedExtension C.l E W n).obj M :=
  (((purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1) W).homEquiv _ _).symm
      (normalizedDVRReductionTransition C.l E W D C.different h M ≫
        (purAdicQuotientRestrictionIso D C E W h).hom.app _)

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [hXsep : IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [hYsep : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The finite source U_n = Lf_n* K_n(d)[2d] in the intrinsic twist coordinates.
Source: thm-pur-adic-reconstruction, source-object argument
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
abbrev purAdicFiniteSource
    (K : DerivedCategory (scalarReductionSource C.l E Y)) (n : ℕ) :=
  ((finiteComplexTwist C.l E X n (d : ℤ)).obj
    ((finiteDerivedPullback C.l E n f).obj
      ((scalarReductionDerivedExtension C.l E Y n).obj K)))⟦2 * (d : ℤ)⟧

universe a₁ a₂ a₃ v₁ v₂ v₃

/-- A source-normalization composite specified in abstract coordinates, with equality
fixing each actual factor and the complete composite. Source: blueprint source-object
argument, Step 6 (blueprint: lem-pur-adic-source-finiteness-reductions). -/
def IsPurAdicNormalizationComposite
    {A : Type a₁} [Category.{v₁} A] {B : Type a₂} [Category.{v₂} B]
    {T : Type a₃} [Category.{v₃} T] (F : A ⥤ T) (G : B ⥤ T)
    (M : A) (N L : B) {P : Type v₃} {Q : Type v₂} {S : Type v₃}
    (p₀ : P) (q₀ : Q) (t₀ : S) : Prop :=
  ∃ (e : F.obj M ≅ G.obj N) (q : N ⟶ L),
    HEq e p₀ ∧ HEq q q₀ ∧ HEq t₀ (e.hom ≫ G.map q)

/-- The finite-source normalization is fixed by equality to the root-normalized
source comparison followed by shifted pullback of the input scalar normalization.
Heterogeneous equality retains the actual composite while avoiding a second expansion
of the concrete finite purity arrow's endpoint.
Source: thm-pur-adic-reconstruction, source-object argument, Step 6
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
def IsPurAdicFiniteSourceNormalization
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m)
    (t : ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).obj
        (purAdicFiniteArrow D C E f d K hK m).left ⟶
      (purAdicFiniteArrow D C E f d K hK n).left) : Prop :=
  IsPurAdicNormalizationComposite
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X)
    ((purAdicFiniteSetting D C E n).compositionShiftedPullback f d)
    (purAdicFiniteArrow D C E f d K hK m).left
    (((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) Y).obj
        ((scalarReductionDerivedExtension C.l E Y m).obj K))
    ((scalarReductionDerivedExtension C.l E Y n).obj K)
    ((purAdicFiniteSetting D C E m).finiteReductionSourceComparison (n + 1)
      (Nat.succ_pos n) (Nat.add_le_add_right h 1) f d
        ((scalarReductionDerivedExtension C.l E Y m).obj K))
    (purAdicQuotientNormalization D C E Y h K) t

set_option linter.unusedSectionVars false in
/-- The specified finite comparison has exactly the source endpoints of the finite
purity arrows; its displayed composite determines it uniquely.
Source: thm-pur-adic-reconstruction, source-object argument, Step 6
(blueprint: lem-pur-adic-source-finiteness-reductions).
Proof: expand the source of smoothPurityMap and compositionShiftedPullback. Both
are inverse intrinsic realization, finite pullback, tensor with the inverse-shifted
diagonal line, shift by 2d, and forward intrinsic realization, in that order.
Thus the root-normalized finiteReductionSourceComparison followed by the smaller
shifted pullback of the scalar normalization has exactly the displayed endpoints.
Transport that composite to the displayed type. The heterogeneous equality fixes
this morphism uniquely, and proof irrelevance removes the finite-Tor witnesses. -/
theorem purAdicFiniteSourceNormalization_existsUnique
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    ∃! t : ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).obj
        (purAdicFiniteArrow D C E f d K hK m).left ⟶
      (purAdicFiniteArrow D C E f d K hK n).left,
      IsPurAdicFiniteSourceNormalization D C E f d K hK h t := by
  let e := (purAdicFiniteSetting D C E m).finiteReductionSourceComparison (n + 1)
    (Nat.succ_pos n) (Nat.add_le_add_right h 1) f d
      ((scalarReductionDerivedExtension C.l E Y m).obj K)
  let q := purAdicQuotientNormalization D C E Y h K
  let G := (purAdicFiniteSetting D C E n).compositionShiftedPullback f d
  refine ⟨e.hom ≫ G.map q, ?_, ?_⟩
  · exact ⟨e, q, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · intro t ht
    obtain ⟨e', q', he, hq, ht⟩ := ht
    cases eq_of_heq he
    cases eq_of_heq hq
    exact eq_of_heq ht

/-- Direct finite-source normalization, uniquely fixed by its actual root-normalized
pullback/twist/shift composite and input normalization, independently of b^U.
Source: thm-pur-adic-reconstruction, source-object argument, Step 6
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicFiniteSourceNormalization
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).obj
        (purAdicFiniteArrow D C E f d K hK m).left ⟶
      (purAdicFiniteArrow D C E f d K hK n).left :=
  (purAdicFiniteSourceNormalization_existsUnique D C E f d K hK h).choose

/-- The semilinear transition underlying the specified direct finite normalization.
Transposing retains the actual quotient coefficient action. Identity and composition
are stated using the recorded canonical scalar-restriction comparisons.
Source: thm-pur-adic-reconstruction, source-object argument, Steps 6--7
(blueprint: lem-pur-adic-source-finiteness-reductions). -/
@[no_expose] def purAdicFiniteSourceTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    (purAdicFiniteArrow D C E f d K hK m).left ⟶
      (normalizedDVRRes C.l E X h).obj (purAdicFiniteArrow D C E f d K hK n).left :=
  ((purAdicFiniteSetting D C E m).finiteReductionAdjunction (n + 1) (Nat.succ_pos n)
    (Nat.add_le_add_right h 1) X).homEquiv _ _
      (purAdicFiniteSourceNormalization D C E f d K hK h) ≫
        (purAdicQuotientRestrictionIso D C E X h).inv.app _

end WeilConjectures
