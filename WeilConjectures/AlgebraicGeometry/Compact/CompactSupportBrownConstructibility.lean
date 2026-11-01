/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeWeilLocalizingBrownAdjoints
import WeilConjectures.AlgebraicGeometry.NativeWeilInduction.NativeWeilDerivedInductionComparison
import WeilConjectures.SixFunctors.NativeGeometricBrown.NativeGeometricBrownConstructibleComparison
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.CompactSupportStageActionAdjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.WeilSheaf.Localization

/-! # Constructibility of the native localizing exceptional adjoint

This is the constructibility step before restricting Brown's adjunction to Weil complexes.
It concerns an arbitrary supplied adjunction on the native localizing hulls; it neither
constructs that adjunction nor asserts an adjunction on the constructible subcategories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Endofunctor
open WeilConjectures.LocallyFiniteAdicCompactSupport

namespace AlgebraicGeometry

private theorem nativeGeometricRight_constructible
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ K, nativeWeilUnderlyingHull k₀ l X K →
      nativeWeilUnderlyingHull k₀ l Y
        ((nativeWeilUnderlyingCompactSupport k₀ l f
          (nativeWeilChosenCompactification k₀ f)).obj K))
    (G : (nativeWeilUnderlyingHull k₀ l Y).FullSubcategory ⥤
      (nativeWeilUnderlyingHull k₀ l X).FullSubcategory)
    (adj : (nativeWeilUnderlyingHull k₀ l X).liftFullSubcategory
      (nativeWeilUnderlyingHull k₀ l Y)
      (nativeWeilUnderlyingCompactSupport k₀ l f
        (nativeWeilChosenCompactification k₀ f)) h ⊣ G)
    (M : (nativeWeilUnderlyingHull k₀ l Y).FullSubcategory)
    (hM : ProEtale.DerivedCategory.boundedAdicConstructible l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber M.obj) :
    ProEtale.DerivedCategory.boundedAdicConstructible l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber (G.obj M).obj := by
  classical
  let c := nativeWeilChosenCompactification k₀ f
  let := Compactification.over (k₀ := k₀) c
  let Xb := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let Yb := (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let Zb := (c.Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let fb := Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))
  let ib := Scheme.Hom.geometricFiberMap c.i (comp_over c.i (Spec (CommRingCat.of k₀)))
  let pb := Scheme.Hom.geometricFiberMap c.g (comp_over c.g (Spec (CommRingCat.of k₀)))
  have : IsProper pb :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange
      (P := @IsProper) c.g (comp_over c.g _) inferInstance
  let cb : Compactification fb :=
    { Z := Zb, g := pb, i := ib
      comm := by
        dsimp [fb, ib, pb]
        rw [← Scheme.Hom.geometricFiberMap_comp]
        congr 1
        exact c.comm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  let : Xb.Over (Spec (CommRingCat.of (AlgebraicClosure k₀))) :=
    ⟨(X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  let : Yb.Over (Spec (CommRingCat.of (AlgebraicClosure k₀))) :=
    ⟨(Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  let : fb.IsOver (Spec (CommRingCat.of (AlgebraicClosure k₀))) :=
    ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure f _⟩
  have : LocallyOfFiniteType (Xb ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change LocallyOfFiniteType
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : QuasiCompact (Xb ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change QuasiCompact (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : LocallyOfFiniteType (Yb ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change LocallyOfFiniteType
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  have : QuasiCompact (Yb ↘ Spec (CommRingCat.of (AlgebraicClosure k₀))) := by
    change QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    infer_instance
  let : Fintype k₀ := Fintype.ofFinite k₀
  obtain ⟨n, hp, hn⟩ := FiniteField.card k₀ (ringChar k₀)
  let D : WeilConjectures.FiniteFieldDatum.{u} :=
    { p := ringChar k₀, a := n, q := Nat.card k₀, prime := hp
      exponent_pos := n.pos, cardinality_eq := by simpa only [Nat.card_eq_fintype_card] using hn
      k₀ := k₀, card_base := rfl, k := AlgebraicClosure k₀ }
  have hl : l ≠ D.p := Ne.symm (Fact.out : ringChar k₀ ≠ l)
  obtain ⟨P⟩ :=
    WeilConjectures.ConstructibleExceptionalCoefficients.exists_coefficient_construction
      l (ULift.{u} (PadicAlgCl l)) D hl fb
  obtain ⟨N, ⟨C⟩⟩ :=
    locally_finite_adic_compact_support_realization l D hl P cb
  have := compactSupport_stageAction_isLeftAdjoint l D hl P cb C.stage
  let Fs := C.stage.system.functor
  let Gs := Fs.rightAdjoint
  let stageAdj : Fs ⊣ Gs := Adjunction.ofIsLeftAdjoint Fs
  obtain ⟨_, _, _, hcomparison⟩ :=
    WeilConjectures.NativeGeometricBrown.native_geometric_brown_constructible_comparison
      k₀ l f C.source C.target Fs Gs stageAdj C.alpha
  obtain ⟨_, _, hp, _, _⟩ := hcomparison h G adj
  exact hp ⟨M.obj, hM⟩

/-- The localizing exceptional adjoint takes constructible native Weil inputs to
constructible native Weil objects.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, final exceptional
adjunction sentence; native assembly, step 3 of
`thm-sf-weil-compact-direct-image-right-adjoint`.
(blueprint: lem-sf-native-brown-right-constructible)

Proof: obtain the underlying localizing adjunction F ⊣ G from
`lem-sf-native-weil-localizing-brown-adjoints`. The geometric constructible comparison
`lem-sf-native-geometric-brown-constructible-comparison` identifies G on constructible
inputs with the realized common-stage exceptional inverse image. Thus G preserves the
geometric bounded constructible subcategory. The free/forgetful derived adjunction and
`lem-sf-native-weil-derived-induction-comparison` identify, naturally in A,
Hom(A, U_X (G_W M)) with Hom(I_X A, G_W M), then with Hom(F_W I_X A, M), then with
Hom(I_Y F A, M), Hom(F A, U_Y M), and finally Hom(A, G U_Y M).
The hull equality in `lem-sf-native-weil-localizing-brown-adjoints` ensures both representing
objects lie in the underlying localizing hull. Yoneda gives U_X G_W M ≅ G U_Y M.
For a Weil complex M, U_Y M is bounded constructible, so G U_Y M is bounded constructible.
Transport this along that isomorphism. Exact conservative forgetting commutes with
cohomology, so boundedness and constructibility of U_X G_W M are precisely
WeilComplex.objectProperty of G_W M. This proves the assertion. No absolute separatedness
of X or Y is required; only the stated separatedness of f enters the compactification.
-/
theorem nativeBrownRight_preserves_weilComplex
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hW : ∀ K, nativeWeilLocalizingHull k₀ l X K →
      nativeWeilLocalizingHull k₀ l Y
        ((ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
          (nativeWeilChosenCompactification k₀ f)).obj K))
    (G : (nativeWeilLocalizingHull k₀ l Y).FullSubcategory ⥤
      (nativeWeilLocalizingHull k₀ l X).FullSubcategory)
    (_adj : (nativeWeilLocalizingHull k₀ l X).liftFullSubcategory
      (nativeWeilLocalizingHull k₀ l Y)
      (ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f
        (nativeWeilChosenCompactification k₀ f)) hW ⊣ G)
    (M : WeilComplex k₀ l Y) :
    WeilComplex.objectProperty k₀ l X
      (G.obj ⟨M.obj, (nativeWeil_localizing_hulls k₀ l Y).2.2.2.2.1 M.obj M.property⟩).obj := by
  classical
  let c := nativeWeilChosenCompactification k₀ f
  let LX := nativeWeilUnderlyingHull k₀ l X
  let LY := nativeWeilUnderlyingHull k₀ l Y
  let WX := nativeWeilLocalizingHull k₀ l X
  let WY := nativeWeilLocalizingHull k₀ l Y
  let UX := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory
  let UY := (IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory
  let IX := (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategory
  let IY := (IsoAlgebra.Free.functor (WeilSheaf.frobeniusPullback k₀ l Y)).mapDerivedCategory
  let F := nativeWeilUnderlyingCompactSupport k₀ l f c
  let FW := ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l f c
  have hX := nativeWeil_localizing_hulls k₀ l X
  have hY := nativeWeil_localizing_hulls k₀ l Y
  let RX := WX.liftFullSubcategory LX UX hX.2.2.2.1
  let RY := WY.liftFullSubcategory LY UY hY.2.2.2.1
  let JX := LX.liftFullSubcategory WX IX hX.2.2.1
  let JY := LY.liftFullSubcategory WY IY hY.2.2.1
  let adjX : JX ⊣ RX :=
    (IsoAlgebra.freeWeilDerivedAdjunction
      (WeilSheaf.frobeniusPullback k₀ l X)).restrictFullyFaithful
        LX.fullyFaithfulι WX.fullyFaithfulι
        (LX.liftFullSubcategoryCompιIso WX IX _).symm
        (WX.liftFullSubcategoryCompιIso LX UX _).symm
  let adjY : JY ⊣ RY :=
    (IsoAlgebra.freeWeilDerivedAdjunction
      (WeilSheaf.frobeniusPullback k₀ l Y)).restrictFullyFaithful
        LY.fullyFaithfulι WY.fullyFaithfulι
        (LY.liftFullSubcategoryCompιIso WY IY _).symm
        (WY.liftFullSubcategoryCompιIso LY UY _).symm
  obtain ⟨h, _, _, _, _, _, hB, _⟩ := nativeWeil_localizing_brown_adjoints k₀ l f
  obtain ⟨G₀, ⟨adj₀⟩, _⟩ := hB
  let R := LX.liftFullSubcategory LY F h
  let RW := WX.liftFullSubcategory WY FW hW
  have hcomp := NativeWeilInduction.nativeWeil_derived_induction_comparison k₀ l f c
  obtain ⟨_, _, _, _, κ, _, hκ⟩ := hcomp.2.2.2.2.2.2.2
  have hκiso (A : LX.FullSubcategory) : IsIso (κ.app A.obj) :=
    (hκ A.obj A.property).1
  let σ : R ⋙ JY ≅ JX ⋙ RW := NatIso.ofComponents
    (fun A ↦ WY.isoMk (asIso (κ.app A.obj))) (by
      intro A B a
      apply InducedCategory.hom_ext
      exact κ.naturality a.hom)
  let e : G ⋙ RX ≅ RY ⋙ G₀ :=
    ((adjX.comp _adj).ofNatIsoLeft σ.symm).rightAdjointUniq (adj₀.comp adjY)
  let MW : WY.FullSubcategory :=
    ⟨M.obj, (nativeWeil_localizing_hulls k₀ l Y).2.2.2.2.1 M.obj M.property⟩
  have hM : ProEtale.DerivedCategory.boundedAdicConstructible l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber (UY.obj M.obj) :=
    (WeilComplex.objectProperty_iff M.obj).1 M.property
  have hgeom : ProEtale.DerivedCategory.boundedAdicConstructible l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber (G₀.obj (RY.obj MW)).obj :=
    nativeGeometricRight_constructible k₀ l f h G₀ adj₀ (RY.obj MW) hM
  apply (WeilComplex.objectProperty_iff _).2
  have : (ProEtale.DerivedCategory.boundedAdicConstructible l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).IsClosedUnderIsomorphisms := by
    dsimp [ProEtale.DerivedCategory.boundedAdicConstructible]
    infer_instance
  exact (ProEtale.DerivedCategory.boundedAdicConstructible l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).prop_of_iso
      (LX.ι.mapIso (e.app MW)).symm hgeom

end AlgebraicGeometry
