/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonFaithful
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Algebra.ZMod
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonFaithful
import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate

/-!
# Finite-ring site transport, including exceptional base change

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (2)--(3), and the eleven-step
finite-ring transport refinement
(blueprint: lem-pur-finite-ring-site-tensor-transpose).

The existing tensor-transport module supplies the canonical comparison, projection,
tensor and pullback constructions. The assertions below state their precise counit,
projection, tensor-transpose and base-change identities without unconditionally
asserting projection invertibility.
The pro-etale adjoints take values in the full localizing subcategories, with ambient Hom
sets. All coefficient categories are ordinary and uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale

-- The two lifted-ring instances agree by a small structural calculation. Prove this
-- separately, so conversions of derived functors can use congruence rather than unfolding.
private theorem uliftCommRingToRing (B : Type) [CommRing B] :
    (ULift.commRing : CommRing (ULift.{u + 1} B)).toRing =
      (ULift.ring : Ring (ULift.{u + 1} B)) := by rfl

private theorem moduleCatSymmetricBraided (R : Type u) [CommRing R] :
    (ModuleCat.MonoidalCategory.symmetricCategory :
      SymmetricCategory (ModuleCat.{u} R)).toBraidedCategory =
      (ModuleCat.MonoidalCategory.instBraidedCategory :
        BraidedCategory (ModuleCat.{u} R)) := by
  rfl

private theorem proofHeterogeneous {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have h : p = q := propext ⟨fun _ => hq, fun _ => hp⟩
  cases h
  rfl

-- Construct ordinary kernel-checked heterogeneous congruence proofs. In particular,
-- never discharge a whole derived-functor comparison by a reflexivity conversion.
open Lean Lean.Meta in
private meta def explicitCongruence (fuel : Nat) (ringProof a b : Lean.Expr) :
    Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => throwError "congruence depth exhausted"
  | fuel + 1 => do
    let normalize (e : Expr) : MetaM Expr := do
      let e ← instantiateMVars e
      let e := e.consumeMData.headBeta
      let e := mkAppN e.getAppFn.consumeMData e.getAppArgs
      if let .letE _ _ val body _ := e then
        return (body.instantiate1 val).headBeta
      if let .fvar id := e.getAppFn then
        if let some val := (← id.getDecl).value? then
          return (mkAppN val e.getAppArgs).headBeta
      return e
    let a' ← normalize a
    let b' ← normalize b
    if a' != a || b' != b then return ← explicitCongruence fuel ringProof a' b'
    let a := a'
    let b := b'
    if a == b then return ← mkAppM ``HEq.refl #[a]
    let rt ← inferType ringProof
    if let some (_, ra, rb) := rt.eq? then
      if a == ra && b == rb then return ← mkAppM ``heq_of_eq #[ringProof]
      if a == rb && b == ra then
        return ← mkAppM ``heq_of_eq #[← mkAppM ``Eq.symm #[ringProof]]
      if (← inferType a).isAppOf ``Ring then
        if (← isDefEq a ra) && (← isDefEq b rb) then
          return ← mkAppM ``heq_of_eq #[← instantiateMVars ringProof]
    if (← isProof a) && (← isProof b) then
      return ← mkAppM ``proofHeterogeneous #[a, b]
    let expandProj (e : Expr) : MetaM Expr := do
      if let .proj n i val := e.getAppFn then
        let env ← getEnv
        let some info := getStructureInfo? env n
          | throwError "no structure info {n}"
        let some proj := getProjFnForField? env n info.fieldNames[i]!
          | throwError "no projection for {n}"
        return mkAppN (← mkAppM proj #[val]) e.getAppArgs
      else pure e
    let a ← expandProj a
    let b ← expandProj b
    let af := a.getAppFn
    let bf := b.getAppFn
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    if af.isConstOf ``SymmetricCategory.toBraidedCategory &&
        bf.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
      let hp := mkApp2 (mkConst ``moduleCatSymmetricBraided bf.constLevels!) ba[0]! ba[1]!
      let some (_, lhs, rhs) := (← inferType hp).eq? | throwError "expected instance equality"
      if (← isDefEq a lhs) && (← isDefEq b rhs) then
        return ← mkAppM ``heq_of_eq #[hp]
    if bf.isConstOf ``SymmetricCategory.toBraidedCategory &&
        af.isConstOf ``ModuleCat.MonoidalCategory.instBraidedCategory then
      let hp := mkApp2 (mkConst ``moduleCatSymmetricBraided af.constLevels!) aa[0]! aa[1]!
      let some (_, lhs, rhs) := (← inferType hp).eq? | throwError "expected instance equality"
      if (← isDefEq b lhs) && (← isDefEq a rhs) then
        return ← mkAppM ``heq_of_eq #[← mkAppM ``Eq.symm #[hp]]
    let sameHead ← if af == bf then pure true else
      if af.isConst && bf.isConst && af.constName? == bf.constName? then
        isDefEq af bf
      else pure false
    if sameHead && aa.size == ba.size && !aa.isEmpty then
      let ct ← mkHCongrWithArity af aa.size
      let mut args := #[]
      for k in [:aa.size] do
        match ct.argKinds[k]! with
        | .eq =>
          let hp ← explicitCongruence fuel ringProof aa[k]! ba[k]!
          args := args ++ #[aa[k]!, ba[k]!, ← mkAppM ``eq_of_heq #[hp]]
        | .heq =>
          let hp ← explicitCongruence fuel ringProof aa[k]! ba[k]!
          args := args ++ #[aa[k]!, ba[k]!, hp]
        | .fixed => args := args.push aa[k]!
        | _ => throwError "unexpected congruence argument"
      let hp := mkAppN ct.proof args
      let tp ← inferType hp
      if tp.isHEq then return hp
      else return ← mkAppM ``heq_of_eq #[hp]
    if aa.isEmpty && ba.isEmpty && (← isDefEq a b) then
      return ← mkAppM ``HEq.refl #[a]
    throwError "unmatched congruence expressions:\n{a}\n{b}\n\
      HEADS: {reprStr af}\n{reprStr bf}\nRIGHT: {reprStr b}"

section BraidedCalculations

variable {C D C' D' : Type*}
  [Category C] [MonoidalCategory C] [BraidedCategory C]
  [Category D] [MonoidalCategory D] [BraidedCategory D]
  [Category C'] [MonoidalCategory C'] [BraidedCategory C']
  [Category D'] [MonoidalCategory D'] [BraidedCategory D']

private theorem reverseProjectionSquare
    (E : C ⥤ C') (H : D ⥤ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (P : D ⥤ C) (P' : D' ⥤ C') (b : F ⋙ H ≅ E ⋙ F')
    (tx : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (ty : ∀ M N, H.obj (M ⊗ N) ≅ H.obj M ⊗ H.obj N)
    (pb : ∀ K, E.obj (P.obj K) ≅ P'.obj (H.obj K))
    (pf : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ P.obj K))
    (pf' : ∀ M K, F'.obj M ⊗ K ⟶ F'.obj (M ⊗ P'.obj K))
    (hx : ∀ M N, E.map (β_ M N).hom ≫ (tx N M).hom =
      (tx M N).hom ≫ (β_ (E.obj M) (E.obj N)).hom)
    (hy : ∀ M N, H.map (β_ M N).hom ≫ (ty N M).hom =
      (ty M N).hom ≫ (β_ (H.obj M) (H.obj N)).hom)
    (hp : ∀ M K, H.map (pf M K) ≫ b.hom.app (M ⊗ P.obj K) ≫
        F'.map ((tx M (P.obj K)).hom ≫ (𝟙 _ ⊗ₘ (pb K).hom)) =
      (ty (F.obj M) K).hom ≫ (b.hom.app M ⊗ₘ 𝟙 _) ≫ pf' (E.obj M) (H.obj K))
    (M : C) (K : D) :
    H.map ((β_ K (F.obj M)).hom ≫ pf M K ≫ F.map (β_ M (P.obj K)).hom) ≫
        b.hom.app (P.obj K ⊗ M) ≫
        F'.map ((tx (P.obj K) M).hom ≫ ((pb K).hom ⊗ₘ 𝟙 _)) =
      (ty K (F.obj M)).hom ≫ (𝟙 _ ⊗ₘ b.hom.app M) ≫
        (β_ (H.obj K) (F'.obj (E.obj M))).hom ≫ pf' (E.obj M) (H.obj K) ≫
        F'.map (β_ (E.obj M) (P'.obj (H.obj K))).hom := by
  have hswap : E.map (β_ M (P.obj K)).hom ≫ (tx (P.obj K) M).hom ≫
        ((pb K).hom ⊗ₘ 𝟙 (E.obj M)) =
      (tx M (P.obj K)).hom ≫ (𝟙 (E.obj M) ⊗ₘ (pb K).hom) ≫
        (β_ (E.obj M) (P'.obj (H.obj K))).hom := by
    rw [reassoc_of% (hx M (P.obj K))]
    rw [← BraidedCategory.braiding_naturality]
  have hb' := b.hom.naturality (β_ M (P.obj K)).hom
  dsimp only [Functor.comp_map] at hb'
  have hp' := hp M K
  simp only [F'.map_comp] at hp'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hb']
  simp only [← F'.map_comp]
  rw [hswap]
  simp only [F'.map_comp]
  rw [reassoc_of% hp', reassoc_of% (hy K (F.obj M))]
  rw [← BraidedCategory.braiding_naturality_assoc]

private theorem reverseProjectionSquarePinned
    (E : C ⥤ C') (H : D ⥤ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (P : D ⥤ C) (P' : D' ⥤ C') (b : F ⋙ H ≅ E ⋙ F')
    (tx : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (ty : ∀ M N, H.obj (M ⊗ N) ≅ H.obj M ⊗ H.obj N)
    (pb : ∀ K, E.obj (P.obj K) ≅ P'.obj (H.obj K))
    (pf : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ P.obj K))
    (pf' : ∀ M K, F'.obj M ⊗ K ⟶ F'.obj (M ⊗ P'.obj K))
    (beta : ∀ M, H.obj (F.obj M) ⟶ F'.obj (E.obj M))
    (hb : ∀ M, b.hom.app M = beta M)
    (hx : ∀ M N, E.map (β_ M N).hom ≫ (tx N M).hom =
      (tx M N).hom ≫ (β_ (E.obj M) (E.obj N)).hom)
    (hy : ∀ M N, H.map (β_ M N).hom ≫ (ty N M).hom =
      (ty M N).hom ≫ (β_ (H.obj M) (H.obj N)).hom)
    (hp : ∀ M K, H.map (pf M K) ≫ beta (M ⊗ P.obj K) ≫
        F'.map (finiteRingTensorPullbackComparison E P P' H tx pb M K).hom =
      (ty (F.obj M) K).hom ≫ (beta M ⊗ₘ 𝟙 _) ≫ pf' (E.obj M) (H.obj K))
    (M : C) (K : D) (pe : K ⊗ F.obj M ≅ F.obj (P.obj K ⊗ M))
    (hpe : pe.hom = (β_ K (F.obj M)).hom ≫ pf M K ≫
      F.map (β_ M (P.obj K)).hom) :
    H.map pe.hom ≫ b.hom.app (P.obj K ⊗ M) ≫
        F'.map ((tx (P.obj K) M).hom ≫ ((pb K).hom ⊗ₘ 𝟙 _)) =
      (ty K (F.obj M)).hom ≫ (𝟙 _ ⊗ₘ b.hom.app M) ≫
        (β_ (H.obj K) (F'.obj (E.obj M))).hom ≫ pf' (E.obj M) (H.obj K) ≫
        F'.map (β_ (E.obj M) (P'.obj (H.obj K))).hom := by
  have h := reverseProjectionSquare E H F F' P P' b tx ty pb pf pf' hx hy
    (fun M K ↦ by
      simpa only [finiteRingTensorPullbackComparison, Iso.trans_hom, tensorIso_hom,
        Iso.refl_hom, ← hb] using hp M K) M K
  simpa only [hpe] using h

private theorem tensorEvaluation_reverse {A : Type*} [Category A]
    [MonoidalCategory A] [BraidedCategory A] (K Z : A) (e : Z ⟶ 𝟙_ A) :
    (β_ K Z).hom ≫ (e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom =
      (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom := by
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [braiding_leftUnitor]

private theorem rightTensorEvaluationComparison (H : D ⥤ D')
    (ty : ∀ M N, H.obj (M ⊗ N) ≅ H.obj M ⊗ H.obj N)
    (uy : H.obj (𝟙_ D) ≅ 𝟙_ D')
    (hy : ∀ M N, H.map (β_ M N).hom ≫ (ty N M).hom =
      (ty M N).hom ≫ (β_ (H.obj M) (H.obj N)).hom)
    (hu : ∀ (Z K : D) (e : Z ⟶ 𝟙_ D),
      H.map ((e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) =
        (ty Z K).hom ≫ ((H.map e ≫ uy.hom) ⊗ₘ 𝟙 _) ≫ (λ_ _).hom)
    (Z K : D) (e : Z ⟶ 𝟙_ D) :
    H.map ((𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom) =
      (ty K Z).hom ≫ (𝟙 _ ⊗ₘ (H.map e ≫ uy.hom)) ≫ (ρ_ _).hom := by
  rw [← tensorEvaluation_reverse K Z e, H.map_comp, hu]
  rw [← Category.assoc, hy, Category.assoc, tensorEvaluation_reverse]

private theorem tensorPairComposite {A : Type*} [Category A] [MonoidalCategory A]
    {U V W Z : A} (f : U ⟶ V) (g : W ⟶ Z) :
    (f ⊗ₘ 𝟙 W) ≫ (𝟙 V ⊗ₘ g) = f ⊗ₘ g := by
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

private theorem comparisonCounitComposite
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (E : A ⥤ A') (H : B ⥤ B') (F : A ⥤ B) (F' : A' ⥤ B')
    (beta : ∀ M, H.obj (F.obj M) ⟶ F'.obj (E.obj M))
    (J W : A) (Q : B) (V V' : A') (Qp : B')
    (v : J ⟶ W) (r : E.obj W ⟶ V) (z : V ⟶ V')
    (e : F.obj W ⟶ Q) (ep : F'.obj V ⟶ H.obj Q)
    (ep' : F'.obj V' ⟶ Qp) (u : H.obj Q ⟶ Qp)
    (hn : H.map (F.map v) ≫ beta W = beta J ≫ F'.map (E.map v))
    (hc : beta W ≫ F'.map r ≫ ep = H.map e)
    (hz : F'.map z ≫ ep' = ep ≫ u) :
    beta J ≫ F'.map (E.map v ≫ r ≫ z) ≫ ep' =
      H.map (F.map v ≫ e) ≫ u := by
  simp only [F'.map_comp, Category.assoc]
  rw [hz, ← reassoc_of% hn, reassoc_of% hc, ← H.map_comp_assoc]

omit [BraidedCategory D] [MonoidalCategory C'] [BraidedCategory C']
  [BraidedCategory D'] in
private theorem inverseProjectionEvaluation
    (H : D ⥤ D') (FP : C' ⥤ D')
    (K Z L : D) (Wp V J₀ J₁ N : C')
    (pe : K ⊗ Z ≅ L) (b : H.obj L ≅ FP.obj J₀)
    (pp : H.obj K ⊗ FP.obj V ≅ FP.obj N)
    (ty : H.obj (K ⊗ Z) ≅ H.obj K ⊗ H.obj Z)
    (bp : H.obj Z ⟶ FP.obj Wp) (r : Wp ⟶ V)
    (s₀ : J₀ ⟶ J₁) (z : J₁ ⟶ N)
    (p₀ : H.obj K ⊗ FP.obj Wp ⟶ FP.obj J₁)
    (e : Z ⟶ 𝟙_ D) (ep : FP.obj V ⟶ 𝟙_ D') (U : H.obj (𝟙_ D) ≅ 𝟙_ D')
    (hsq : H.map pe.hom ≫ b.hom ≫ FP.map s₀ =
      ty.hom ≫ (𝟙 _ ⊗ₘ bp) ≫ p₀)
    (hn : (𝟙 (H.obj K) ⊗ₘ FP.map r) ≫ pp.hom = p₀ ≫ FP.map z)
    (hr : bp ≫ FP.map r ≫ ep = H.map e ≫ U.hom)
    (hu : H.map ((𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom) =
      ty.hom ≫ (𝟙 _ ⊗ₘ (H.map e ≫ U.hom)) ≫ (ρ_ (H.obj K)).hom) :
    FP.map (s₀ ≫ z) ≫ pp.inv ≫ (𝟙 (H.obj K) ⊗ₘ ep) ≫ (ρ_ (H.obj K)).hom =
      b.inv ≫ H.map (pe.inv ≫ (𝟙 K ⊗ₘ e) ≫ (ρ_ K).hom) := by
  apply (cancel_epi (H.map pe.hom ≫ b.hom)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hsq, ← reassoc_of% hn]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc (𝟙 (H.obj K) ⊗ₘ FP.map r), tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [← Category.assoc (𝟙 (H.obj K) ⊗ₘ bp), tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [hr, ← hu]
  simp only [← H.map_comp, pe.hom_inv_id_assoc]

private theorem restrictionCounitNaturality
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (PX : ObjectProperty A) (PY : ObjectProperty B)
    (hs : ∀ N, PX N → PY (F.obj N)) (G : PY.FullSubcategory ⥤ PX.FullSubcategory)
    (ap : finiteRingRestriction F PX PY hs ⊣ G) (K L : PY.FullSubcategory)
    (u : K.obj ⟶ L.obj) :
    F.map (G.map (ObjectProperty.homMk u)).hom ≫ (ap.counit.app L).hom =
      (ap.counit.app K).hom ≫ u :=
  congrArg (fun z ↦ z.hom) (ap.counit.naturality (ObjectProperty.homMk u))

private theorem restrictionTransposeComposite
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (PX : ObjectProperty A) (PY : ObjectProperty B)
    (hs : ∀ N, PX N → PY (F.obj N)) (G : PY.FullSubcategory ⥤ PX.FullSubcategory)
    (ap : finiteRingRestriction F PX PY hs ⊣ G)
    (J N : PX.FullSubcategory) (K : PY.FullSubcategory)
    (s : J.obj ⟶ N.obj) (w : F.obj N.obj ⟶ K.obj)
    (t : F.obj J.obj ⟶ K.obj) (h : F.map s ≫ w = t) :
    (ap.homEquiv J K (ObjectProperty.homMk t)).hom =
      s ≫ (ap.homEquiv N K (ObjectProperty.homMk w)).hom := by
  subst t
  let smk : J ⟶ N := ObjectProperty.homMk s
  let wmk : (finiteRingRestriction F PX PY hs).obj N ⟶ K := ObjectProperty.homMk w
  have hn := congrArg (fun z ↦ z.hom) (ap.homEquiv_naturality_left smk wmk)
  exact hn

private theorem restrictionTransposeFactored
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) (PX : ObjectProperty A) (PY : ObjectProperty B)
    (hs : ∀ N, PX N → PY (F.obj N)) (G : PY.FullSubcategory ⥤ PX.FullSubcategory)
    (ap : finiteRingRestriction F PX PY hs ⊣ G)
    (J N : PX.FullSubcategory) (K : PY.FullSubcategory) (I : A)
    (x : J.obj ⟶ (G.obj K).obj) (s : J.obj ⟶ N.obj)
    (s₁ : J.obj ⟶ I) (s₂ : I ⟶ N.obj)
    (w : F.obj N.obj ⟶ K.obj) (t : F.obj J.obj ⟶ K.obj)
    (ht : x = (ap.homEquiv J K (ObjectProperty.homMk t)).hom)
    (hw : F.map s ≫ w = t) (hsplit : s = s₁ ≫ s₂) :
    x = s₁ ≫ s₂ ≫ (ap.homEquiv N K (ObjectProperty.homMk w)).hom := by
  have hn := restrictionTransposeComposite F PX PY hs G ap J N K s w t hw
  exact ht.trans (hn.trans ((congrArg
    (fun z ↦ z ≫ (ap.homEquiv N K (ObjectProperty.homMk w)).hom) hsplit).trans
      (Category.assoc _ _ _)))

private theorem dualizingTransposeCalculation
    (E : C ⥤ C') (H : D ⥤ D') (F : C ⥤ D) (F' : C' ⥤ D')
    (P : D ⥤ C) (P' : D' ⥤ C')
    (PX : ObjectProperty C') (PY : ObjectProperty D')
    (hX : ∀ M, PX (E.obj M)) (hY : ∀ K, PY (H.obj K))
    (hs : ∀ N, PX N → PY (F'.obj N))
    (R : D ⥤ C) (ae : F ⊣ R) (G : PY.FullSubcategory ⥤ PX.FullSubcategory)
    (ap : finiteRingRestriction F' PX PY hs ⊣ G)
    (b : F ⋙ H ≅ E ⋙ F')
    (beta : ∀ M, H.obj (F.obj M) ⟶ F'.obj (E.obj M))
    (hb : ∀ M, b.hom.app M = beta M)
    (rho : R ⋙ finiteRingImageLift E PX hX ≅ finiteRingImageLift H PY hY ⋙ G)
    (hc : ∀ K, beta (R.obj K) ≫ F'.map (rho.hom.app K).hom ≫
      (ap.counit.app ⟨H.obj K, hY K⟩).hom = H.map (ae.counit.app K))
    (tx : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (ty : ∀ M N, H.obj (M ⊗ N) ≅ H.obj M ⊗ H.obj N)
    (U : H.obj (𝟙_ D) ≅ 𝟙_ D')
    (pb : ∀ K, E.obj (P.obj K) ≅ P'.obj (H.obj K))
    (pf : ∀ M K, F.obj M ⊗ K ⟶ F.obj (M ⊗ P.obj K))
    (pf' : ∀ M K, F'.obj M ⊗ K ⟶ F'.obj (M ⊗ P'.obj K))
    (hx : ∀ M N, E.map (β_ M N).hom ≫ (tx N M).hom =
      (tx M N).hom ≫ (β_ (E.obj M) (E.obj N)).hom)
    (hy : ∀ M N, H.map (β_ M N).hom ≫ (ty N M).hom =
      (ty M N).hom ≫ (β_ (H.obj M) (H.obj N)).hom)
    (hp : ∀ M K, H.map (pf M K) ≫ beta (M ⊗ P.obj K) ≫
        F'.map (finiteRingTensorPullbackComparison E P P' H tx pb M K).hom =
      (ty (F.obj M) K).hom ≫ (beta M ⊗ₘ 𝟙 _) ≫ pf' (E.obj M) (H.obj K))
    (hpf : ∀ {M N : C'} (r : M ⟶ N) (K : D'),
      (F'.map r ⊗ₘ 𝟙 K) ≫ pf' N K = pf' M K ≫ F'.map (r ⊗ₘ 𝟙 (P'.obj K)))
    (hu : ∀ (Z K : D) (e : Z ⟶ 𝟙_ D),
      H.map ((e ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) =
        (ty Z K).hom ≫ ((H.map e ≫ U.hom) ⊗ₘ 𝟙 _) ≫ (λ_ _).hom)
    (htrans : ∀ (M : C) (K : D) (v : F.obj M ⟶ K),
      E.map (ae.homEquiv M K v) ≫ (rho.hom.app K).hom =
        (ap.homEquiv ⟨E.obj M, hX M⟩ ⟨H.obj K, hY K⟩
          (ObjectProperty.homMk (b.inv.app M ≫ H.map v))).hom)
    (hUnit : PY (𝟙_ D')) (K : D)
    (hN : PX (P'.obj (H.obj K) ⊗ (G.obj ⟨𝟙_ D', hUnit⟩).obj))
    (pe : K ⊗ F.obj (R.obj (𝟙_ D)) ≅ F.obj (P.obj K ⊗ R.obj (𝟙_ D)))
    (hpe : pe.hom = (β_ K (F.obj (R.obj (𝟙_ D)))).hom ≫ pf (R.obj (𝟙_ D)) K ≫
      F.map (β_ (R.obj (𝟙_ D)) (P.obj K)).hom)
    (pp : H.obj K ⊗ F'.obj (G.obj ⟨𝟙_ D', hUnit⟩).obj ≅
      F'.obj (P'.obj (H.obj K) ⊗ (G.obj ⟨𝟙_ D', hUnit⟩).obj))
    (hpp : pp.hom = (β_ (H.obj K) (F'.obj (G.obj ⟨𝟙_ D', hUnit⟩).obj)).hom ≫
      pf' (G.obj ⟨𝟙_ D', hUnit⟩).obj (H.obj K) ≫
      F'.map (β_ (G.obj ⟨𝟙_ D', hUnit⟩).obj (P'.obj (H.obj K))).hom) :
    E.map (ae.homEquiv _ _ (pe.inv ≫
      (𝟙 K ⊗ₘ ae.counit.app (𝟙_ D)) ≫ (ρ_ K).hom)) ≫ (rho.hom.app K).hom =
    (tx (P.obj K) (R.obj (𝟙_ D))).hom ≫
      ((pb K).hom ⊗ₘ ((rho.hom.app (𝟙_ D)).hom ≫
        (G.map (ObjectProperty.homMk U.hom)).hom)) ≫
      (ap.homEquiv ⟨_, hN⟩ ⟨H.obj K, hY K⟩ (ObjectProperty.homMk
        (pp.inv ≫ (𝟙 (H.obj K) ⊗ₘ (ap.counit.app ⟨𝟙_ D', hUnit⟩).hom) ≫
          (ρ_ (H.obj K)).hom))).hom := by
  let W := R.obj (𝟙_ D)
  let V := (G.obj ⟨𝟙_ D', hUnit⟩).obj
  let r : E.obj W ⟶ V := (rho.hom.app (𝟙_ D)).hom ≫
    (G.map (ObjectProperty.homMk U.hom)).hom
  let s₀ := (tx (P.obj K) W).hom ≫ ((pb K).hom ⊗ₘ 𝟙 (E.obj W))
  let s := s₀ ≫ (𝟙 (P'.obj (H.obj K)) ⊗ₘ r)
  let p₀ := (β_ (H.obj K) (F'.obj (E.obj W))).hom ≫ pf' (E.obj W) (H.obj K) ≫
    F'.map (β_ (E.obj W) (P'.obj (H.obj K))).hom
  have hsq : H.map pe.hom ≫ b.hom.app (P.obj K ⊗ W) ≫ F'.map s₀ =
      (ty K (F.obj W)).hom ≫ (𝟙 _ ⊗ₘ b.hom.app W) ≫ p₀ :=
    reverseProjectionSquarePinned E H F F' P P' b tx ty pb pf pf' beta hb hx hy hp W K pe hpe
  have hn : (𝟙 (H.obj K) ⊗ₘ F'.map r) ≫ pp.hom =
      p₀ ≫ F'.map (𝟙 (P'.obj (H.obj K)) ⊗ₘ r) := by
    rw [hpp, ← Category.assoc, BraidedCategory.braiding_naturality]
    simp only [Category.assoc]
    rw [reassoc_of% (hpf r (H.obj K))]
    dsimp only [p₀]
    simp only [Category.assoc]
    apply congrArg (fun z ↦ (β_ (H.obj K) (F'.obj (E.obj W))).hom ≫
      pf' (E.obj W) (H.obj K) ≫ z)
    simpa only [F'.map_comp] using congrArg F'.map
      (BraidedCategory.braiding_naturality r (𝟙 (P'.obj (H.obj K))))
  have hr : b.hom.app W ≫ F'.map r ≫
      (ap.counit.app ⟨𝟙_ D', hUnit⟩).hom = H.map (ae.counit.app (𝟙_ D)) ≫ U.hom := by
    have hn := restrictionCounitNaturality F' PX PY hs G ap
      ⟨H.obj (𝟙_ D), hY (𝟙_ D)⟩ ⟨𝟙_ D', hUnit⟩ U.hom
    dsimp only [r]
    rw [hb W, F'.map_comp]
    simp only [Category.assoc]
    rw [hn]
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ U.hom) (hc (𝟙_ D))
  have hue := rightTensorEvaluationComparison H ty U hy hu (F.obj W) K
    (ae.counit.app (𝟙_ D))
  let v := pe.inv ≫ (𝟙 K ⊗ₘ ae.counit.app (𝟙_ D)) ≫ (ρ_ K).hom
  let w := pp.inv ≫ (𝟙 (H.obj K) ⊗ₘ
    (ap.counit.app ⟨𝟙_ D', hUnit⟩).hom) ≫ (ρ_ (H.obj K)).hom
  have hw : F'.map s ≫ w = b.inv.app (P.obj K ⊗ W) ≫ H.map v :=
    inverseProjectionEvaluation H F' K (F.obj W) (F.obj (P.obj K ⊗ W))
      (E.obj W) V (E.obj (P.obj K ⊗ W))
      (P'.obj (H.obj K) ⊗ E.obj W) (P'.obj (H.obj K) ⊗ V)
      pe (b.app (P.obj K ⊗ W)) pp (ty K (F.obj W)) (b.hom.app W) r s₀
      (𝟙 (P'.obj (H.obj K)) ⊗ₘ r) p₀ (ae.counit.app (𝟙_ D))
      (ap.counit.app ⟨𝟙_ D', hUnit⟩).hom U hsq hn hr hue
  have ht := htrans (P.obj K ⊗ W) K v
  have hsimp : s = (tx (P.obj K) W).hom ≫ ((pb K).hom ⊗ₘ r) := by
    dsimp only [s, s₀]
    rw [Category.assoc, tensorPairComposite]
  exact restrictionTransposeFactored F' PX PY hs G ap
    ⟨E.obj (P.obj K ⊗ W), hX (P.obj K ⊗ W)⟩ ⟨_, hN⟩ ⟨H.obj K, hY K⟩
    (E.obj (P.obj K) ⊗ E.obj W)
    (E.map (ae.homEquiv _ _ v) ≫ (rho.hom.app K).hom) s
    (tx (P.obj K) W).hom ((pb K).hom ⊗ₘ r) w
    (b.inv.app (P.obj K ⊗ W) ≫ H.map v) ht hw hsimp

end BraidedCalculations

private theorem compactExchangeCoordinates
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (H : C ⥤ D) (H' : C' ⥤ D') (P : C ⥤ C') (Q Qd : D ⥤ D')
    (i : Qd ≅ Q) (a : H ⋙ Q ≅ P ⋙ H')
    {S : Type*} [Category S] (FP : S ⥤ D')
    {U V : C} {Tp T : C'} {W : D} {Zd Ze Et : S}
    (e : U ⟶ V) (ei : V ⟶ U) (he : ei ≫ e = 𝟙 V)
    (ep : Tp ⟶ T) (q : P.obj U ⟶ Tp)
    (beta : H.obj V ⟶ W) (betap : H'.obj T ⟶ FP.obj Et)
    (ip : Zd ⟶ Ze) (ipi : Ze ⟶ Zd) (hip : ipi ≫ ip = 𝟙 Ze)
    (si : Et ⟶ Ze) (ex : Qd.obj W ⟶ FP.obj Zd)
    (h : H'.map q ≫ H'.map ep ≫ betap ≫ FP.map si ≫ FP.map ipi =
      a.inv.app U ≫ i.inv.app (H.obj U) ≫ Qd.map (H.map e) ≫ Qd.map beta ≫ ex) :
    H'.map (P.map ei ≫ q ≫ ep) ≫ betap ≫ FP.map si =
      a.inv.app V ≫ Q.map beta ≫ i.inv.app W ≫ ex ≫ FP.map ip := by
  have h' := congrArg (fun z ↦ H'.map (P.map ei) ≫ z ≫ FP.map ip) h
  have hi := i.inv.naturality (H.map e ≫ beta)
  have ha := a.inv.naturality ei
  dsimp only [Functor.comp_map] at ha
  simp only [Category.assoc, ← FP.map_comp, ← Qd.map_comp_assoc] at h'
  rw [← reassoc_of% hi, reassoc_of% ha] at h'
  simp only [Q.map_comp, Category.assoc] at h'
  have he' : Q.map (H.map ei) ≫ Q.map (H.map e) = 𝟙 _ := by
    rw [← Q.map_comp, ← H.map_comp, he, H.map_id, Q.map_id]
  simp only [hip, Category.comp_id, reassoc_of% he'] at h'
  simpa only [H'.map_comp, FP.map_comp, Category.assoc] using h'



/-- The ambient pro-etale proper-mate/open exchange, using exact pullback coordinates.
The two inserted isomorphisms identify the derived pullbacks with termwise pullback.
Source: Stacks 0F7F, 0GL1; node base-change clause
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingProExchangeMap (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.obj
        ((finiteRingProShriek B c).obj M) ⟶
      (finiteRingProShriek B (c.ofIsPullback sq)).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).inv.app _ ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq c).app M ≫
    (finiteRingProShriek B (c.ofIsPullback sq)).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').hom.app M)

-- The published comparison has an inferred result type involving composite functors.
-- Give its fixed ambient endpoints a named, non-reducible interface for proof checking.
@[irreducible] private def finiteRingCompactComparison
    (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :
    (finiteRingSitePull B Y).obj ((finiteRingEtaleShriek B c).obj M) ⟶
      (finiteRingProShriek B c).obj ((finiteRingSitePull B X).obj M) :=
  finiteComparisonCompactSupportMap B c.i c.g M

private theorem finiteRingCompactComparison_eq
    (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :
    finiteRingCompactComparison B c M = finiteComparisonCompactSupportMap B c.i c.g M := by
  unfold finiteRingCompactComparison
  rfl

private theorem finiteRingCompactInclusion_inv_hom
    (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).inv.app L ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).hom.app L =
      𝟙 ((finiteRingEtaleShriek B c).obj L.obj) := by
  simpa only [Functor.comp_obj, ObjectProperty.ι_obj] using
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).inv_hom_id_app L

private theorem finiteRingCompactComparison_naturality
    (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : Etale.DerivedCategoryModule (ULift.{u + 1} B) X} (v : M ⟶ N) :
    (finiteRingSitePull B Y).map ((finiteRingEtaleShriek B c).map v) ≫
        finiteComparisonCompactSupportMap B c.i c.g N =
      finiteComparisonCompactSupportMap B c.i c.g M ≫
        (finiteRingProShriek B c).map ((finiteRingSitePull B X).map v) := by
  unfold finiteComparisonCompactSupportMap
  dsimp only [finiteRingEtaleShriek, finiteRingProShriek,
    Etale.rightDerivedLowerShriekOfCompactification,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map]
  rw [← Category.assoc, unboundedDirectImageComparisonMap_naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact congrArg
    ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.g).rightDerivedFunctor.map)
    ((finiteComparisonOpenIso B c.i).hom.naturality v)

private def finiteRingProExchangeNatTrans (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f) :
    finiteRingProShriek B c ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory ⋙
        finiteRingProShriek B (c.ofIsPullback sq) :=
  Functor.whiskerLeft (finiteRingProShriek B c)
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq c ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').hom
      (finiteRingProShriek B (c.ofIsPullback sq))

private theorem finiteRingProExchange_naturality (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))} (v : M ⟶ N) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).mapDerivedCategory.map
        ((finiteRingProShriek B c).map v) ≫ finiteRingProExchangeMap B sq c N =
      finiteRingProExchangeMap B sq c M ≫
        (finiteRingProShriek B (c.ofIsPullback sq)).map
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g').mapDerivedCategory.map v) :=
  (finiteRingProExchangeNatTrans B sq c).naturality v

-- Restricting the specified unbounded mate to D+ preserves its counit normalization.
private theorem finiteRingProperComparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (Kp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.hom.app
          Kp) ≫
      unboundedDirectImageComparisonMap A g Kp.obj =
        (rightDerivedLowerStarComparisonIso' g (ModuleCat.{u + 1} A)).hom.app Kp := by
  let E := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g
  let P := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let G := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let R := (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let S := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
  let re := (Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility
  let rp := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility
  let b := (fixedComparisonDirectImageMatePlus A g).app Kp
  have hc := congrArg (fun z ↦ DerivedCategory.Plus.ι.map z)
    (fixedComparisonDirectImageMatePlus_counit A g Kp)
  simp only [Functor.map_comp, derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus] at hc
  change DerivedCategory.Plus.ι.map
      ((fixedComparisonPullbackPlus A g).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj Kp)) ≫
      L.map (DerivedCategory.Plus.ι.map b) ≫
      DerivedCategory.Plus.ι.map (P.derivedPlus.counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj Kp)) =
      G.map (DerivedCategory.Plus.ι.map (E.derivedPlus.counit.app Kp)) at hc
  rw [included_pullback, included_counit, included_counit] at hc
  have hn := (unboundedDirectImagePullbackIso A g).hom.naturality (re.hom.app Kp)
  simp only [Functor.comp_map] at hn
  have ht : F.map (re.hom.app Kp) ≫ unboundedDirectImageComparisonMap A g Kp.obj =
      DerivedCategory.Plus.ι.map b ≫ rp.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj Kp) := by
    apply (P.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm]
    dsimp only [P]
    rw [unboundedDirectImageComparisonMap]
    simp only [F, Functor.comp_obj, ObjectProperty.ι,
      inducedFunctor, Equiv.symm_apply_apply]
    change L.map (F.map (re.hom.app Kp)) ≫
        (unboundedDirectImagePullbackIso A g).hom.app (R.obj Kp.obj) ≫
          G.map (E.mapDerivedCategoryRightDerivedAdjunction.counit.app Kp.obj) = _
    erw [reassoc_of% hn]
    simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
    have hc' := hc
    simp only [Functor.map_comp] at hc'
    have hh := congrArg (fun z ↦
      (unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj Kp).obj ≫ z) hc'
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at hh
    simpa only [F, G, L, E, P, re, rp, Functor.comp_obj, Functor.comp_map,
      DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor, Functor.mapDerivedCategoryPlus,
      ObjectProperty.lift, ObjectProperty.homMk, Functor.id_obj,
      Etale.rightDerivedLowerStarPlus, Category.assoc] using hh.symm
  dsimp only [F, re, rp, b] at ht
  have hid := (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map_id
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj Kp.obj)
  simpa only [rightDerivedLowerStarComparisonIso', rightDerivedLowerStarComparisonPlusIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, asIso_hom, fixedComparisonDirectImageMatePlus,
    Functor.comp_obj, Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    ObjectProperty.ι_obj, hid, Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc] using ht

private theorem finiteRingCompactComparison_plus
    (B : Type) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    (compactExchangeTransportComparison (ULift.{u + 1} B) c).hom.app K =
      (finiteRingSitePull B Y).map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).hom.app K) ≫
        finiteComparisonCompactSupportMap B c.i c.g K.obj := by
  rw [compactComparison_hom, ← finiteRingProperComparison_plus]
  simp only [finiteComparisonCompactSupportMap,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, NatTrans.id_app, Functor.map_comp,
    Category.comp_id, Category.id_comp, Category.assoc]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj]
  have hid := (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.g).rightDerivedFunctor.map_id
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.i).mapDerivedCategory.obj K.obj)
  have hid' := (finiteRingSitePull B Y).map_id
    ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.g).rightDerivedFunctor.obj
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) c.i).mapDerivedCategory.obj K.obj))
  simp only [hid, hid', Category.id_comp]
  rfl

private theorem finiteRingCompactExchange_plus_square
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    (Functor.whiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c)
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y').mapDerivedCategory) ≫
      (compactExchangeTransportTarget Λ sq c).hom =
    (compactExchangeTransportSource Λ g c).hom ≫
      Functor.whiskerLeft
        (DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory)
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} Λ) sq c)) := by
  with_unfolding_all
    apply NatTrans.ext
    funext K
    let A := ModuleCat.{u + 1} Λ
    let M := (Etale.openImmersionLowerShriek A c.i).mapDerivedCategoryPlus.obj K
    let P' := (lowerStar A (c.ofIsPullback sq).g).rightDerivedFunctor
    let e := (fixSiteOpenComparison Λ c.i).hom.app K.obj
    let β := (Etale.extensionZeroBaseChangeDerivedPlusIso Λ
      (c.isPullback_i_ofIsPullback sq)).hom.app K
    have hp := comparison_derivedBaseChangeMap Λ
      (c.isPullback_g_ofIsPullback sq).flip M
    have ho := open_transport Λ (c.isPullback_i_ofIsPullback sq) K
    have hn := (derivedBaseChangeMap A
      (c.isPullback_g_ofIsPullback sq).flip.toCommSq).naturality e
    have hb := (rightDerivedLowerStarComparisonIso' (c.ofIsPullback sq).g A).hom.naturality β
    simp only [baseChangeSourceComparisonIso, baseChangeTargetComparisonIso,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hp
    simp only [Functor.comp_map] at hn hb
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      compactExchangeTransportTarget, compactExchangeTransportSource,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, compactComparison_hom,
      etale_exchange_app, proetale_exchange_app, Functor.comp_map, Functor.map_comp, Category.assoc]
    dsimp only [A, β, P', Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj] at *
    simp only [Category.id_comp] at *
    -- Move the proper comparison across the etale open exchange.
    rw [reassoc_of% hb]
    -- Combine the three images of the open square, and use its compatibility.
    simp only [← Functor.map_comp]
    rw [← ho]
    simp only [Functor.map_comp]
    simp only [Category.assoc] at hp hn
    -- The remaining square is proper base change, followed by its naturality in e.
    erw [reassoc_of% hp]
    erw [← reassoc_of% hn]
    rfl

-- A separate proposition equality freezes the native and categorical coordinates.
-- Its explicit congruence proof avoids conversions across derived-model data.
private theorem finiteRingCompactExchange_components
    (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (hM : DerivedCategory.TStructure.t.plus M) :
    let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
    let L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) := ⟨M, hM⟩
    let P : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y'.smallEtaleTopology A) :=
      (Etale.upperStar A g).mapDerivedCategory
    let H : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) := finiteRingSitePull B Y
    let H' : DerivedCategory (Sheaf Y'.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A) := finiteRingSitePull B Y'
    let F' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A) :=
      finiteRingProShriek B (c.ofIsPullback sq)
    let a : H ⋙ (upperStar A g).mapDerivedCategory ≅ P ⋙ H' :=
      unboundedDirectImagePullbackIso (ULift.{u + 1} B) g
    let i : (upperStar A g).leftDerivedFunctor ≅ (upperStar A g).mapDerivedCategory :=
      leftDerivedUpperStarIsoMapDerivedCategory A g
    let i' : (upperStar A g').leftDerivedFunctor ≅ (upperStar A g').mapDerivedCategory :=
      leftDerivedUpperStarIsoMapDerivedCategory A g'
    let E : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) := finiteRingSitePull B X
    let EP : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X'.smallEtaleTopology A) :=
      (Etale.upperStar A g').mapDerivedCategory
    let L' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology A) :=
      (Etale.upperStar A g').mapDerivedCategoryPlus.obj L
    let U : DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus A c).obj L).obj
    let ec := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility A c
    let e : U ⟶ (finiteRingEtaleShriek B c).obj M := ec.hom.app L
    let epc := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility A
      (c.ofIsPullback sq)
    let ep : ((Etale.rightDerivedLowerShriekOfCompactificationPlus A
        (c.ofIsPullback sq)).obj L').obj ⟶
        (finiteRingEtaleShriek B (c.ofIsPullback sq)).obj (EP.obj M) := epc.hom.app L'
    let q : P.obj U ⟶ ((Etale.rightDerivedLowerShriekOfCompactificationPlus A
        (c.ofIsPullback sq)).obj L').obj := DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (ULift.{u + 1} B) sq c).app L)
    let ex : (upperStar A g).leftDerivedFunctor.obj
        ((finiteRingProShriek B c).obj (E.obj M)) ⟶
        F'.obj ((upperStar A g').leftDerivedFunctor.obj (E.obj M)) :=
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app (E.obj M)
    let beta : H.obj ((finiteRingEtaleShriek B c).obj M) ⟶
        (finiteRingProShriek B c).obj (E.obj M) :=
      finiteRingCompactComparison B c M
    let betap : H'.obj ((finiteRingEtaleShriek B (c.ofIsPullback sq)).obj (EP.obj M)) ⟶
        F'.obj ((finiteRingSitePull B X').obj (EP.obj M)) :=
      finiteRingCompactComparison B (c.ofIsPullback sq) (EP.obj M)
    H'.map q ≫ H'.map (ep) ≫
      betap ≫
      F'.map ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) ≫
      F'.map (i'.inv.app (E.obj M)) =
    a.inv.app U ≫ i.inv.app (H.obj U) ≫
      (upperStar A g).leftDerivedFunctor.map (H.map (e)) ≫
      (upperStar A g).leftDerivedFunctor.map
        (beta) ≫ ex := by
  intro A L P H H' F' a i i' E EP L' U ec e epc ep q ex beta betap
  have h := congrArg (fun t ↦ t.app L)
    (finiteRingCompactExchange_plus_square (ULift.{u + 1} B) sq c)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    compactExchangeTransportTarget, compactExchangeTransportSource,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, finiteRingCompactComparison_plus, pullbackComparison_hom,
    Functor.comp_map, Functor.map_comp, Category.assoc] at h
  dsimp only [Etale.rightDerivedLowerShriekOfCompactificationPlus,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift, ObjectProperty.ι_obj,
    Functor.comp_obj] at h
  simp only [Category.id_comp] at h
  rw [← finiteRingCompactComparison_eq B c M,
    ← finiteRingCompactComparison_eq B (c.ofIsPullback sq) (EP.obj M)] at h
  change H'.map q ≫ H'.map (ep) ≫
      betap ≫
      F'.map ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) ≫
      F'.map (i'.inv.app (E.obj M)) =
    a.inv.app U ≫ i.inv.app (H.obj U) ≫
      (upperStar A g).leftDerivedFunctor.map (H.map (e)) ≫
      (upperStar A g).leftDerivedFunctor.map
        (beta) ≫ ex at h
  exact h

-- Infer the derived-pullback models from the comparison maps themselves, so the
-- generic cancellation theorem uses exactly their native source and target data.
private theorem finiteRingCompactExchange_assembly
    (B : Type) [CommRing B] [Finite B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1} B) X)
    (hM : DerivedCategory.TStructure.t.plus M) :
    let A := ModuleCat.{u + 1} (ULift.{u + 1} B)
    let L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) := ⟨M, hM⟩
    let P : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y'.smallEtaleTopology A) :=
      (Etale.upperStar A g).mapDerivedCategory
    let H : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) := finiteRingSitePull B Y
    let H' : DerivedCategory (Sheaf Y'.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A) := finiteRingSitePull B Y'
    let F' : DerivedCategory (Sheaf (Scheme.ProEt.topology X') A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A) :=
      finiteRingProShriek B (c.ofIsPullback sq)
    let a : H ⋙ (upperStar A g).mapDerivedCategory ≅ P ⋙ H' :=
      unboundedDirectImagePullbackIso (ULift.{u + 1} B) g
    let i : (upperStar A g).leftDerivedFunctor ≅ (upperStar A g).mapDerivedCategory :=
      leftDerivedUpperStarIsoMapDerivedCategory A g
    let i' : (upperStar A g').leftDerivedFunctor ≅ (upperStar A g').mapDerivedCategory :=
      leftDerivedUpperStarIsoMapDerivedCategory A g'
    let E : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) := finiteRingSitePull B X
    let EP : DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X'.smallEtaleTopology A) :=
      (Etale.upperStar A g').mapDerivedCategory
    let L' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology A) :=
      (Etale.upperStar A g').mapDerivedCategoryPlus.obj L
    let U : DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus A c).obj L).obj
    let ec := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility A c
    let e : U ⟶ (finiteRingEtaleShriek B c).obj M := ec.hom.app L
    let ei : (finiteRingEtaleShriek B c).obj M ⟶ U := ec.inv.app L
    let epc := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility A
      (c.ofIsPullback sq)
    let ep : ((Etale.rightDerivedLowerShriekOfCompactificationPlus A
        (c.ofIsPullback sq)).obj L').obj ⟶
        (finiteRingEtaleShriek B (c.ofIsPullback sq)).obj (EP.obj M) := epc.hom.app L'
    let q : P.obj U ⟶ ((Etale.rightDerivedLowerShriekOfCompactificationPlus A
        (c.ofIsPullback sq)).obj L').obj := DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (ULift.{u + 1} B) sq c).app L)
    let ex : (upperStar A g).leftDerivedFunctor.obj
        ((finiteRingProShriek B c).obj (E.obj M)) ⟶
        F'.obj ((upperStar A g').leftDerivedFunctor.obj (E.obj M)) :=
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap A sq c).app (E.obj M)
    let beta : H.obj ((finiteRingEtaleShriek B c).obj M) ⟶
        (finiteRingProShriek B c).obj (E.obj M) :=
      finiteRingCompactComparison B c M
    let betap : H'.obj ((finiteRingEtaleShriek B (c.ofIsPullback sq)).obj (EP.obj M)) ⟶
        F'.obj ((finiteRingSitePull B X').obj (EP.obj M)) :=
      finiteRingCompactComparison B (c.ofIsPullback sq) (EP.obj M)
    (H'.map q ≫ H'.map (ep) ≫
      betap ≫
      F'.map ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) ≫
      F'.map (i'.inv.app (E.obj M)) =
    a.inv.app U ≫ i.inv.app (H.obj U) ≫
      (upperStar A g).leftDerivedFunctor.map (H.map (e)) ≫
      (upperStar A g).leftDerivedFunctor.map
        (beta) ≫ ex) →
    H'.map (P.map ei ≫ q ≫ ep) ≫ betap ≫
        F'.map ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) =
      a.inv.app ((finiteRingEtaleShriek B c).obj M) ≫
        (upperStar A g).mapDerivedCategory.map beta ≫
        i.inv.app ((finiteRingProShriek B c).obj (E.obj M)) ≫ ex ≫
        F'.map (i'.hom.app (E.obj M)) := by
  intro A L P H H' F' a i i' E EP L' U ec e ei epc ep q ex beta betap h
  exact compactExchangeCoordinates H H' P _ _ i a F'
    e ei (finiteRingCompactInclusion_inv_hom B c L) ep q beta betap
    (i'.hom.app (E.obj M)) (i'.inv.app (E.obj M))
    (i'.inv_hom_id_app (E.obj M))
    ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g').inv.app M) ex h

private theorem finiteRingProPF_naturality
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (r : M ⟶ N)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((rightDerivedLowerShriekOfCompactification A c).map r ⊗ₘ 𝟙 K) ≫
        finiteRingProPF A c N K = finiteRingProPF A c M K ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (r ⊗ₘ 𝟙 ((upperStar A f).leftDerivedFunctor.obj K)) := by
  have hp := NatTrans.congr_app ((projectionMapOfCompactification A c).naturality r) K
  dsimp only [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar] at hp
  simpa only [rightDerivedLowerShriekOfCompactification, finiteRingProPF,
    derivedTensor, Functor.comp_map, Functor.postcompose₂_obj_obj_map_app,
    Functor.whiskeringLeft₂_obj_obj_obj_map_app, Functor.id_map,
    curriedTensor_map_app, tensorHom_id, NatTrans.comp_app] using hp

set_option maxHeartbeats 500000 in
-- The concrete specialization checks several derived flat-resolution instances.
end AlgebraicGeometry.ProEtale
