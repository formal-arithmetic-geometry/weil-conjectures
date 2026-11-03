/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyComp

/-! # Condensed coefficient restriction calculus on a smooth curve

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-curve-heart/
thm-a1-curve-perverse-heart.proof.md, Steps 0--4
(blueprint: lem-per-condensed-curve-restriction-calculus).

All cohomology and truncations belong to the ordinary derived category of actual
modules over the pulled-back finite-subextension-valued condensed coefficient ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
open Opposite AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale.CondensedCurve

local notation "ModΩ[" ell ", " T "]" =>
  Mod (Sheaf (Scheme.ProEt.topology T) Ab) (coefficients ell T)

attribute [instance] LatticeBase.field LatticeBase.algebra LatticeBase.finiteDimensional
  LatticeBase.noetherian LatticeBase.separated LatticeBase.invertible

section HomologySquare
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] Functor.mapDerivedCategoryCompIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryHomologyFunctorIso
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory pullSquare
attribute [local irreducible] CondensedRing.upperStar Functor.mapDerivedCategory
  DerivedCategory.homologyFunctor
  Functor.leftDerivedFunctor

-- Use the supplied functors and comparisons verbatim. In particular, no abelian or
-- derived-category instance is reconstructed when this calculation is specialized.
private theorem homology_square_transport_expanded
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    (HA : DA ⥤ A) (HB : DB ⥤ B) (P : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (DP : DA ⥤ DB) (DU : DA ⥤ DA) (DV : DB ⥤ DB)
    {R S : DA ⥤ DB} (a : DU ⋙ DP ≅ R) (b : R ≅ S) (c : S ≅ DP ⋙ DV)
    (γP : HA ⋙ P ≅ DP ⋙ HB) (γU : HA ⋙ U ≅ DU ⋙ HA) (γV : HB ⋙ V ≅ DV ⋙ HB)
    (L : DA ⥤ DB) (δ : L ≅ DP) (e : U ⋙ P ≅ P ⋙ V) (K : DA)
    (hs : P.map (γU.hom.app K) ≫ γP.hom.app (DU.obj K) ≫
        HB.map ((a ≪≫ b ≪≫ c).hom.app K) =
      e.hom.app (HA.obj K) ≫ V.map (γP.hom.app K) ≫ γV.hom.app (DP.obj K)) :
    V.map (γP.hom.app K ≫ HB.map (δ.inv.app K)) ≫ γV.hom.app (L.obj K) =
      e.inv.app (HA.obj K) ≫ P.map (γU.hom.app K) ≫ γP.hom.app (DU.obj K) ≫
        HB.map (δ.inv.app (DU.obj K)) ≫ HB.map
          (δ.hom.app (DU.obj K) ≫ (a ≪≫ b ≪≫ c).hom.app K ≫
            DV.map (δ.inv.app K)) := by
  have hn := γV.hom.naturality (δ.inv.app K)
  apply (cancel_epi (e.hom.app (HA.obj K))).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  conv_rhs =>
    simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_map] at hn
  conv_lhs =>
    arg 2
    arg 2
    rw [hn]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun q ↦ q ≫ HB.map (DV.map (δ.inv.app K))) hs.symm

-- Keep the application in the original isomorphism form, with the same five factors
-- as derivedPullSquare. Expansion and reassociation are checked over abstract categories.
private theorem homology_square_transport
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    (HA : DA ⥤ A) (HB : DB ⥤ B) (P : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    (DP : DA ⥤ DB) (DU : DA ⥤ DA) (DV : DB ⥤ DB)
    {R S : DA ⥤ DB} (a : DU ⋙ DP ≅ R) (b : R ≅ S) (c : S ≅ DP ⋙ DV)
    (γP : HA ⋙ P ≅ DP ⋙ HB) (γU : HA ⋙ U ≅ DU ⋙ HA) (γV : HB ⋙ V ≅ DV ⋙ HB)
    (L : DA ⥤ DB) (δ : L ≅ DP) (e : U ⋙ P ≅ P ⋙ V) (K : DA)
    (hs : P.map (γU.hom.app K) ≫ γP.hom.app (DU.obj K) ≫
        HB.map ((a ≪≫ b ≪≫ c).hom.app K) =
      e.hom.app (HA.obj K) ≫ V.map (γP.hom.app K) ≫ γV.hom.app (DP.obj K)) :
    let z := γP ≪≫ Functor.isoWhiskerRight δ.symm HB
    let w := Functor.isoWhiskerLeft DU δ ≪≫ a ≪≫ b ≪≫ c ≪≫
      Functor.isoWhiskerRight δ.symm DV
    V.map (z.hom.app K) ≫ γV.hom.app (L.obj K) =
      e.inv.app (HA.obj K) ≫ P.map (γU.hom.app K) ≫ z.hom.app (DU.obj K) ≫
        HB.map (w.hom.app K) := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc] using
      homology_square_transport_expanded HA HB P U V DP DU DV a b c γP γU γV L δ e K hs

/-- The transported homology square, before specializing its coefficient categories. -/
private theorem exact_homology_square_transport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (P : A ⥤ B) (U : A ⥤ A) (V : B ⥤ B)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (L : DerivedCategory A ⥤ DerivedCategory B) (δ : L ≅ P.mapDerivedCategory)
    (e : U ⋙ P ≅ P ⋙ V) (m : ℤ) (K : DerivedCategory A) :
    let z := P.mapDerivedCategoryHomologyFunctorIso m ≪≫
      Functor.isoWhiskerRight δ.symm (DerivedCategory.homologyFunctor B m)
    let w := Functor.isoWhiskerLeft U.mapDerivedCategory δ ≪≫
      (Functor.mapDerivedCategoryCompIso U P).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso P V ≪≫
      Functor.isoWhiskerRight δ.symm V.mapDerivedCategory
    V.map (z.hom.app K) ≫ (V.mapDerivedCategoryHomologyFunctorIso m).hom.app (L.obj K) =
      e.inv.app ((DerivedCategory.homologyFunctor A m).obj K) ≫
        P.map ((U.mapDerivedCategoryHomologyFunctorIso m).hom.app K) ≫
        z.hom.app (U.mapDerivedCategory.obj K) ≫
        (DerivedCategory.homologyFunctor B m).map (w.hom.app K) := by
  exact homology_square_transport
    (DerivedCategory.homologyFunctor A m) (DerivedCategory.homologyFunctor B m)
    P U V P.mapDerivedCategory U.mapDerivedCategory V.mapDerivedCategory
    (Functor.mapDerivedCategoryCompIso U P).symm
    (Functor.mapDerivedCategoryNatIso e) (Functor.mapDerivedCategoryCompIso P V)
    (P.mapDerivedCategoryHomologyFunctorIso m) (U.mapDerivedCategoryHomologyFunctorIso m)
    (V.mapDerivedCategoryHomologyFunctorIso m) L δ e K
    (Functor.mapDerivedCategoryHomologyFunctorIso_squareIso e m K)

private def exactPullComparison (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPull ell f ≅ (pull ell f).mapDerivedCategory :=
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) f

/-- The exact-pullback cohomology identification itself respects compatible automorphisms.
Source: curve-heart proof, Steps 0--4, automorphism paragraph
(blueprint: lem-per-condensed-curve-restriction-calculus).

Proof: pullSquare is obtained by functor composition and the given equality of scheme
maps. The homology comparison for an exact functor is natural under exact natural
isomorphisms and composition: on representing complexes each map is induced on kernels
and then on their quotient by boundaries. Its two composites are therefore equal. The
exact-functor identification of total derived pullback gives the displayed equation. -/
theorem automorphism_pull_cohomology (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ≅ X) (gY : Y ≅ Y)
    (h : gX.hom ≫ f = f ≫ gY.hom) (m : ℤ) (K : Ambient ell Y) :
    (pull ell gX.hom).map ((pullCohomology ell f m).hom.app K) ≫
      ((pull ell gX.hom).mapDerivedCategoryHomologyFunctorIso m).hom.app
        ((derivedPull ell f).obj K) =
    (pullSquare ell f gX gY h).inv.app ((ordinaryCohomology ell Y m).obj K) ≫
      (pull ell f).map
        (((pull ell gY.hom).mapDerivedCategoryHomologyFunctorIso m).hom.app K) ≫
      (pullCohomology ell f m).hom.app ((action ell gY).obj K) ≫
      (ordinaryCohomology ell X m).map ((derivedPullSquare ell f gX gY h).hom.app K) := by
  have hp := exact_homology_square_transport
    (pull ell f) (pull ell gY.hom) (pull ell gX.hom)
    (derivedPull ell f) (exactPullComparison ell f) (pullSquare ell f gX gY h) m K
  -- Supply congruence proofs for the thin instance aliases instead of asking the
  -- kernel to normalize the large derived functors to compare their presentations.
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let hp ← Lean.Meta.getLocalDeclFromUserName `hp
      let normalize (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let mut e ← Lean.instantiateMVars e
        for _ in [:16] do
          e := e.consumeMData.headBeta
          if let .letE _ _ v b _ := e then
            e := b.instantiate1 v
            continue
          let aliases : Array Lean.Name := #[``coefficients, ``Ambient, ``pull,
            ``ordinaryCohomology, ``derivedPull, ``action,
            ``pullCohomology, ``derivedPullSquare, ``exactPullComparison,
            ``CondensedRing.StrictWeilCondensed.action,
            ``CondensedRing.moduleObjectDerivedPullback,
            ``GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall]
          if (e.getAppFn.constName?.any aliases.contains) then
            if let some e' ← Lean.Meta.withTransparency .all
                (Lean.Meta.unfoldDefinition? e) then
              e ← Lean.instantiateMVars e'
              continue
          break
        return e
      let source ← normalize hp.type
      let target ← normalize (← goal.getType)
      let mut pending := [(source, target, false)]
      let mut proofs : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr := {}
      let mut congruences : Std.HashMap (Lean.Expr × Nat) Lean.Meta.CongrTheorem := {}
      for _ in [:100000] do
        if pending.isEmpty then break
        let (a, b, ready) := pending.head!
        pending := pending.tail!
        let a ← normalize a
        let b ← normalize b
        let key := (a, b)
        if proofs.contains key then continue
        if a == b then
          proofs := proofs.insert key (← Lean.Meta.mkHEqRefl a)
        else if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
          proofs := proofs.insert key (← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b])
        else
          let f := a.getAppFn
          let xs := a.getAppArgs
          let ys := b.getAppArgs
          unless f == b.getAppFn && xs.size == ys.size && !xs.isEmpty do
            throwError "Unsupported homology congruence: {a} versus {b}"
          if !ready then
            pending := (a, b, true) :: pending
            for x in xs, y in ys do
              pending := (x, y, false) :: pending
          else
            let congr ← match congruences[(f, xs.size)]? with
              | some congr => pure congr
              | none => Lean.Meta.mkHCongrWithArity f xs.size
            congruences := congruences.insert (f, xs.size) congr
            let mut proof := congr.proof
            for i in [:xs.size] do
              let child := (← normalize xs[i]!, ← normalize ys[i]!)
              let some h := proofs[child]? | throwError "Missing homology congruence proof"
              let h ← if congr.argKinds[i]! == .eq then Lean.Meta.mkEqOfHEq h else pure h
              proof := Lean.mkAppN proof #[xs[i]!, ys[i]!, h]
            proofs := proofs.insert key proof
      let some proof := proofs[(source, target)]?
        | throwError "Homology congruence traversal unfinished"
      let eq ← Lean.Meta.mkEqOfHEq proof
      let proof ← Lean.Meta.mkAppM ``Eq.mp #[eq, hp.toExpr]
      if proof.hasSorry || proof.hasMVar then throwError "Unfinished homology congruence proof"
      goal.assign proof

end HomologySquare

end AlgebraicGeometry.ProEtale.CondensedCurve
