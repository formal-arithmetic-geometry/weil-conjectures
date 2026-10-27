/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.IntegralCondensedCoefficientRing
import Sheaf.Paper.IntegralLfpConstantModelComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import all Sheaf.Paper.ConstructibleInternalHomContinuity
import all Sheaf.Algebra.Homology.RHomContinuityTriangleClosure
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Integral general-lfp sequential internal-Hom continuity

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), Lemma 6.8.12;
Hemo--Richarz--Scholbach, Lemma 5.3(2), Theorems 4.13 and 6.2(2)--(3);
Stacks Project, Tags 01OZ and 0118
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity).

The derived comparison uses the exact termwise colimit of functorial internal-Hom
representatives. Its formula fixes the canonical map, and the theorem quantifies over
all such representatives. No ordinary categorical colimit in the derived category is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralSequentialContinuity

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.homComplexFunctor CategoryTheory.derivedInternalHomOfUniverses
  WeilConjectures.coefficientHomResolution WeilConjectures.coefficientHomResolutionIso
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  HasDerivedCategory.ofIsGrothendieckAbelian

-- Prefer the native module-object instance before searching equivalent ringed models.
attribute [local instance 2000] Mod.isGrothendieckAbelian
  hasSmallestColimitsOfHasColimits Limits.instHasColimitOfHasColimitsOfShape

/-- The existing category of internal modules over `p_X^* underline(O_E)`.
Source: Bhatt--Scholze 6.8.10--6.8.12; the integral local-model comparison
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity). -/
abbrev Modules := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj (integralCondensedCoefficientRing l E) X)

/-- The existing ordinary unbounded derived internal Hom, with its first argument fixed.
Source: Bhatt--Scholze 6.8.12; HRS Lemma 5.3(2)
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity). -/
abbrev hom (K : DerivedCategory (Modules l E X)) :=
  (CondensedRing.derivedHom (integralCondensedCoefficientRing l E) X).obj (op K)

/-- The canonical comparison from the termwise colimit of functorial Hom representatives.
Here e identifies the representative functor F with the already defined derived internal
Hom after localization. The map is induced by the images of the colimit legs; naturality
of e identifies those images with internal Hom applied to the target colimit legs.
Source: HRS Lemma 5.3(2), evaluation-induced comparison
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity). -/
def comparison (K : DerivedCategory (Modules l E X))
    (F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
    (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)
    (M : ℕ ⥤ CochainComplex (Modules l E X) ℤ) :
    DerivedCategory.Q.obj (colimit (M ⋙ F)) ⟶
      (hom l E X K).obj (DerivedCategory.Q.obj (colimit M)) :=
  DerivedCategory.Q.map (colimit.post M F) ≫ e.hom.app (colimit M)

/-- The repeated-ell diagram of a complex, using its actual scalar endomorphism.
Source: Stacks 0118; the final scalar-tower clause of the item
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity). -/
def tower (C : CochainComplex (Modules l E X) ℤ) :
    ℕ ⥤ CochainComplex (Modules l E X) ℤ :=
  Functor.ofSequence (X := fun _ : ℕ ↦ C) (fun _ ↦ l • 𝟙 C)

/-- The scalar tower on an ordinary derived object, with no boundedness assumption.
Source: Stacks 0118; the final scalar-tower clause of the item
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity). -/
def derivedTower (L : DerivedCategory (Modules l E X)) :
    ℕ ⥤ DerivedCategory (Modules l E X) :=
  Functor.ofSequence (X := fun _ : ℕ ↦ L) (fun _ ↦ l • 𝟙 L)

private theorem coefficient_iso : Nonempty
    (Mon.mk (integralCondensedCoefficientRing l E) ≅
      Mon.mk (FiniteConstantModel.integralCoefficients l E)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let ei : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.val.ofAbs, x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ x.val, x.property⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ rfl
      map_mul' := fun x y ↦ rfl
      map_add' := fun x y ↦ rfl }
  have hei : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    rfl
  have heis : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hei (ei.symm x) (ei.symm y)).symm
  let eR : Profinite.continuousMapRingSheafOfUniverse.{u, u} A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop heis.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  exact ⟨Mon.mkIso' eAb⟩

private theorem native_continuity
    [TopologicalSpace.NoetherianSpace X]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (FiniteConstantModel.integralCoefficients l E) ∨
      Λ = Mon.mk (FiniteConstantModel.rationalCoefficients l E))
    (K : DerivedCategory (CondensedRing.supportModules Λ.X X))
    (hK : constantModelBoundedConstructible Λ.X X K) :
    HomContinuous ((CondensedRing.derivedHom Λ.X X).obj (op K)) := by
  let P : ObjectProperty (DerivedCategory (CondensedRing.supportModules Λ.X X)) :=
    NativeContinuous Λ X
  let := (nativeContinuous_closure Λ X).1
  let := (nativeContinuous_closure Λ X).2
  have hgen : ∀ (V S : Scheme.{u}) (v : V ⟶ X) [IsOpenImmersion v]
      (t : S ⟶ V) [IsClosedImmersion t] [IsReduced S]
      (L : CondensedRing.supportModules Λ.X S), HasFiniteConstantLocalModel Λ.X S L →
      P ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.openImmersionLowerShriek Λ.X v).obj
          ((CondensedRing.lowerStar Λ.X t).obj L))) := by
    intro V S v _ t _ _ L hL
    have : TopologicalSpace.NoetherianSpace V :=
      v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let A := (DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ.X t).obj L)
    have hopen := openContinuous Λ X V v A (closedModelContinuous l E Λ hΛ t L hL)
    exact P.prop_of_iso
      ((CondensedRing.openImmersionLowerShriek Λ.X v).mapDerivedCategorySingleFunctor 0 |>.app
        ((CondensedRing.lowerStar Λ.X t).obj L)) hopen
  exact ((CondensedRing.bounded_finiteModel_generation Λ.X X P hgen K hK).1).continuity

private theorem integral_continuity
    [TopologicalSpace.NoetherianSpace X]
    (K : DerivedCategory (Modules l E X))
    (hK : constantModelBoundedConstructible (integralCondensedCoefficientRing l E) X K) :
    HomContinuous (hom l E X K) := by
  obtain ⟨e⟩ := coefficient_iso l E
  let ψ := (upperStarFromPoint X).map e.inv.hom
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  have : IsIso ψ := inferInstanceAs (IsIso ((upperStarFromPoint X).map e.inv.hom))
  let T := Mod.comapEquivalenceOfIsIso ψ
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ψ
  have : T.functor.Additive := inferInstanceAs F.Additive
  have : T.inverse.Additive := inferInstanceAs
    (Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (asIso ψ).inv).Additive
  have : F.IsEquivalence := T.isEquivalence_functor
  let D := T.mapDerivedCategory
  let K' := D.functor.obj K
  have hK' : constantModelBoundedConstructible (FiniteConstantModel.integralCoefficients l E)
      X K' := by
    refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun q ↦ ?_⟩
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso q).app K)
      (constructible_comap e.inv.hom X _ (hK.2 q))
  have hcont := native_continuity l E X
    (Mon.mk (FiniteConstantModel.integralCoefficients l E)) (Or.inl rfl) K' hK'
  let t := DerivedCategory.tensorLeftCompMapDerivedCategoryIso F K
  let z := Adjunction.equivalenceCompRightAdjointIso D
    (CondensedRing.derivedTensorHomAdjunction (integralCondensedCoefficientRing l E) K)
    (CondensedRing.derivedTensorHomAdjunction (FiniteConstantModel.integralCoefficients l E) K')
    t
  exact (continuous_equivalence_iff T _ _ z.symm).mpr hcont

private theorem sequential_cocones
    (K : DerivedCategory (Modules l E X)) (hK : HomContinuous (hom l E X K))
    (M : ℕ ⥤ CochainComplex (Modules l E X) ℤ) (c : ℤ)
    (hM : ∀ n q, q < c → IsZero ((M.obj n).X q)) :
    ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        (colimit.cocone M))) := by
  let T : ℕ ≌ AsSmall.{u + 1} ℕ := AsSmall.equiv
  let N := T.inverse ⋙ M
  have hb (i : AsSmall.{u + 1} ℕ) : (DerivedCategory.Q.obj (N.obj i)).IsGE c := by
    change (DerivedCategory.Q.obj (M.obj (ULift.down i))).IsGE c
    have : (M.obj (ULift.down i)).IsStrictlyGE c :=
      (CochainComplex.isStrictlyGE_iff _ _).mpr (hM (ULift.down i))
    infer_instance
  intro q
  let H := DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q
  obtain ⟨hc⟩ := hK _ N c hb q
  have : PreservesColimit N H :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit N) hc
  have : PreservesColimit (T.symm.functor ⋙ M) H :=
    inferInstanceAs (PreservesColimit N H)
  have hs := isColimitOfPreserves H ((colimit.isColimit M).whiskerEquivalence T.symm)
  exact ⟨IsColimit.ofWhiskerEquivalence T.symm hs⟩

attribute [local semireducible] AlgebraicGeometry.ProEtale.CondensedRing.derivedHom in
private theorem exists_hom_model (K : DerivedCategory (Modules l E X)) :
    ∃ F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ,
      Nonempty (F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K) := by
  let A := Modules l E X
  let R := CochainComplex.kInjectiveResolutionFunctor.{u + 1} A
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P := DerivedCategory.Qh.objPreimage K
  let H := HomotopyCategory.internalHom P
  let D := DerivedCategory.internalHomQhObj P
  let η := DerivedCategory.internalHomQhObjUnit P
  let T : (R ⋙ q) ⋙ (H ⋙ DerivedCategory.Qh) ⟶
      (R ⋙ q) ⋙ (DerivedCategory.Qh ⋙ D) := Functor.whiskerLeft (R ⋙ q) η
  have : IsIso T := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro C
    exact (HomotopyCategory.KInjectives.localizerMorphism_derives
      (H ⋙ DerivedCategory.Qh)).isIso_of_isRightDerivedFunctor η
        (HomotopyCategory.KInjectives.mk (R.obj C))
  let σ : DerivedCategory.Q ⟶ R ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (CochainComplex.toKInjectiveResolution.{u + 1} A) DerivedCategory.Q
  have : IsIso σ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro C
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} A).app C) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A C).2
    exact inferInstanceAs
      (IsIso (DerivedCategory.Q.map
        ((CochainComplex.toKInjectiveResolution.{u + 1} A).app C)))
  let a : (CochainComplex.internalHom P.as) ⋙ DerivedCategory.Q ≅
      q ⋙ H ⋙ DerivedCategory.Qh :=
    (Functor.isoWhiskerLeft (CochainComplex.internalHom P.as)
      (DerivedCategory.quotientCompQhIso A)).symm ≪≫
        Functor.isoWhiskerRight (HomotopyCategory.quotientCompInternalHomIso P).symm
          DerivedCategory.Qh
  refine ⟨R ⋙ CochainComplex.internalHom P.as, ⟨?_⟩⟩
  change (R ⋙ CochainComplex.internalHom P.as) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ D
  exact Functor.isoWhiskerLeft R a ≪≫ asIso T ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft R (DerivedCategory.quotientCompQhIso A)) D ≪≫
        Functor.isoWhiskerRight (asIso σ).symm D

private theorem comparison_isIso
    (K : DerivedCategory (Modules l E X))
    (F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
    (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)
    (M : ℕ ⥤ CochainComplex (Modules l E X) ℤ)
    (hc : ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        (colimit.cocone M)))) : IsIso (comparison l E X K F e M) := by
  let := AB5OfSize_shrink.{0, 0, u + 1, u + 1} (Modules l E X)
  have hp : IsIso (DerivedCategory.Q.map (colimit.post M F)) := by
    rw [DerivedCategory.isIso_iff]
    intro q
    let H := DerivedCategory.homologyFunctor (Modules l E X) q
    have := complexHomologyPreserves (A := Modules l E X) ℕ q
    have : PreservesColimitsOfShape ℕ (DerivedCategory.Q ⋙ H) :=
      preservesColimitsOfShape_of_natIso
        (DerivedCategory.homologyFunctorFactors (Modules l E X) q).symm
    have : IsIso (colimit.post M ((DerivedCategory.Q ⋙ hom l E X K) ⋙ H)) :=
      (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1 (hc q)
    have hp : IsIso (colimit.post M (F ⋙ (DerivedCategory.Q ⋙ H))) :=
      post_isIso_natIso _ _ (Functor.isoWhiskerRight e.symm H) M
    rw [← colimit.post_post M F (DerivedCategory.Q ⋙ H)] at hp
    exact (isIso_comp_left_iff _ _).mp hp
  unfold comparison
  infer_instance

private theorem colimit_quasiIso
    {M N : ℕ ⥤ CochainComplex (Modules l E X) ℤ}
    (τ : M ⟶ N) (hτ : ∀ n, QuasiIso (τ.app n)) : QuasiIso (colimMap τ) := by
  let := AB5OfSize_shrink.{0, 0, u + 1, u + 1} (Modules l E X)
  exact MorphismProperty.colimMap
    (W := HomologicalComplex.quasiIso (Modules l E X) (.up ℤ)) τ hτ

private theorem cocone_transfer
    (K : DerivedCategory (Modules l E X))
    {M N : ℕ ⥤ CochainComplex (Modules l E X) ℤ}
    (τ : M ⟶ N) (hτ : ∀ n, QuasiIso (τ.app n))
    (hc : ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        (colimit.cocone M)))) :
    ∀ q : ℤ, Nonempty (IsColimit
      ((DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
        (colimit.cocone N))) := by
  have := colimit_quasiIso l E X τ hτ
  intro q
  let H := DerivedCategory.Q ⋙ hom l E X K ⋙ DerivedCategory.homologyFunctor _ q
  have : IsIso (H.map (colim.map τ)) := inferInstanceAs
    (IsIso ((hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).map
      (DerivedCategory.Q.map (colimMap τ))))
  have : IsIso (Functor.whiskerRight τ H) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    have := hτ n
    exact inferInstanceAs (IsIso ((hom l E X K ⋙ DerivedCategory.homologyFunctor _ q).map
      (DerivedCategory.Q.map (τ.app n))))
  have : IsIso (colimit.post M H) :=
    (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.1 (hc q)
  have hp : IsIso (colim.map (Functor.whiskerRight τ H) ≫ colimit.post N H) := by
    rw [← colimit.map_post]
    infer_instance
  have : IsIso (colimit.post N H) := (isIso_comp_left_iff _ _).mp hp
  exact (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 this

/-- Sequential internal-Hom continuity for general-lfp bounded constructible integral
complexes, with representative independence and the scalar-equivariant good truncation.
The existence clause supplies functorial Hom representatives. All choices of such models
are covered, so no resolution, constructibility, or completeness of the targets is assumed.
In the independence clause N need not itself be termwise bounded below.

Source: Bhatt--Scholze 6.8.10--6.8.12; HRS Lemma 5.3(2), Theorems 4.13 and
6.2(2)--(3); Stacks Tags 01OZ and 0118
(blueprint: lem-sfb-integral-general-lfp-sequential-continuity).

Proof, following the six steps of the node:
1. A locally Noetherian quasi-compact scheme is Noetherian by the existing scheme
instance. Its NoetherianSpace instance gives the descending-chain condition.
2. In every degree apply the forward implication of
lem-sfb-integral-lfp-constant-model-comparison to the general constructible cohomology
module. It gives finite constant scalar models on a finite stratification. Torsion is
allowed and the stratifications may depend on the degree. Boundedness is unchanged.
3. The native internal-module Grothendieck-abelian instance gives small colimits and
AB5. Functorial K-injective resolution followed by the Hom complex out of a homotopy
representative of K supplies a functorial model of the existing derived internal Hom:
the right-derived-functor unit is invertible on the K-injective resolutions.
4. Explicitly identify the two integral coefficient rings by their underlying isometric
ring isomorphism. Restriction of scalars gives an exact monoidal equivalence and preserves
finite constant models. Tensor/Hom adjunctions transport internal Hom through this
equivalence. Use the cohomologically bounded continuity property established inside
lem-sfb-constructible-internal-hom-continuity, before its final termwise specialization.
Lift the filtered category of natural numbers to the site universe and transfer its
colimit cocone across the equivalence. A common termwise lower bound gives the needed
cohomological bound. Exact colimits commute with cohomology, and naturality of any
representative identification gives the canonical comparison isomorphism. Exact colimits
also preserve objectwise quasi-isomorphisms. Naturality transfers the cocone property to
an unbounded replacement N. Composing the two comparison isomorphisms with Hom applied
to the localized colimit map gives the required isomorphism; cancellation proves its
uniqueness. Thus no constructibility or completeness of the target diagrams is used.
5. Use the existing good lower truncation C.truncGE c: its terms are zero below c,
opcycles C c = coker(d_C^(c-1)) at c, and C above c. The differential out of c factors
through that cokernel because d squared is zero. The quotient projection is a chain
map, zero below c, the cokernel projection at c, and identity above c. At c its kernel
is ker(d_C^c)/im(d_C^(c-1)); at c+1 the incoming image is unchanged since the quotient
map is epic; above c+1 the complexes agree. Below c both cohomologies vanish by the
hypothesis on L and its representative isomorphism. Thus the projection is a
quasi-isomorphism, including for C with a nonzero exact tail below c.
6. All components of that projection are B-linear, so it commutes with multiplication
by ell. Its localized inverse followed by the given representative isomorphism gives
the natural isomorphism from the truncated scalar tower to the scalar tower of L,
with the displayed component normalization. The truncated tower has common termwise
lower bound c, so step 4 applies to it. This uses only the cohomological lower bound
on L and allows an arbitrary original representative C. -/
theorem integralGeneralLfpSequentialContinuity
    [CompactSpace X] [IsLocallyNoetherian X]
    (K : DerivedCategory (Modules l E X))
    (_hK : boundedConstructible (condensedRingObj (integralCondensedCoefficientRing l E) X) K) :
    TopologicalSpace.NoetherianSpace X ∧
    (∀ q : ℤ, IsConstantModelConstructible (integralCondensedCoefficientRing l E) X
      ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
    HasColimitsOfSize.{u + 1, u + 1} (Modules l E X) ∧
    AB5OfSize.{u + 1, u + 1} (Modules l E X) ∧
    (∃ F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ,
      Nonempty (F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)) ∧
    (∀ (F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
      (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)
      (M : ℕ ⥤ CochainComplex (Modules l E X) ℤ) (c : ℤ),
      (∀ (n : ℕ) (q : ℤ), q < c → IsZero ((M.obj n).X q)) →
      IsIso (comparison l E X K F e M)) ∧
    (∀ (F G : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
      (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)
      (f : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K)
      (M N : ℕ ⥤ CochainComplex (Modules l E X) ℤ) (c : ℤ),
      (∀ (n : ℕ) (q : ℤ), q < c → IsZero ((M.obj n).X q)) →
      ∀ τ : M ⟶ N, (∀ n : ℕ, QuasiIso (τ.app n)) →
      ∃! a : DerivedCategory.Q.obj (colimit (M ⋙ F)) ≅
          DerivedCategory.Q.obj (colimit (N ⋙ G)),
        a.hom ≫ comparison l E X K G f N =
          comparison l E X K F e M ≫
            (hom l E X K).map (DerivedCategory.Q.map (colimMap τ))) ∧
    (∀ (L : DerivedCategory (Modules l E X))
      (C : CochainComplex (Modules l E X) ℤ)
      (eC : DerivedCategory.Q.obj C ≅ L) (c : ℤ), L.IsGE c →
      QuasiIso (C.πTruncGE c) ∧
      (C.truncGE c).IsStrictlyGE c ∧
      ((l • 𝟙 C) ≫ C.πTruncGE c = C.πTruncGE c ≫ (l • 𝟙 (C.truncGE c))) ∧
      (∃ a : tower l E X (C.truncGE c) ⋙ DerivedCategory.Q ≅ derivedTower l E X L,
        ∀ n : ℕ, DerivedCategory.Q.map (C.πTruncGE c) ≫ a.hom.app n = eC.hom) ∧
      ∀ (F : CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
        (e : F ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ hom l E X K),
        IsIso (comparison l E X K F e (tower l E X (C.truncGE c)))) := by
  classical
  let : IsNoetherian X := ⟨⟩
  have hmodels (q : ℤ) : IsConstantModelConstructible
      (integralCondensedCoefficientRing l E) X ((DerivedCategory.homologyFunctor _ q).obj K) :=
    (integralLfpConstantModelComparison l E X _).mp (_hK.2 q)
  have hconst : constantModelBoundedConstructible
      (integralCondensedCoefficientRing l E) X K := ⟨_hK.1, hmodels⟩
  have hc := sequential_cocones l E X K (integral_continuity l E X K hconst)
  refine ⟨inferInstance, hmodels, inferInstance, inferInstance,
    exists_hom_model l E X K, ?_, ?_, ?_⟩
  · intro F e M c hM
    exact comparison_isIso l E X K F e M (hc M c hM)
  · intro F G e f M N c hM τ hτ
    have := comparison_isIso l E X K F e M (hc M c hM)
    have := comparison_isIso l E X K G f N (cocone_transfer l E X K τ hτ (hc M c hM))
    have := colimit_quasiIso l E X τ hτ
    let a := asIso (comparison l E X K F e M) ≪≫
      (hom l E X K).mapIso (asIso (DerivedCategory.Q.map (colimMap τ))) ≪≫
        (asIso (comparison l E X K G f N)).symm
    refine ⟨a, ?_, ?_⟩
    · simp [a]
    · intro b hb
      apply Iso.ext
      apply (cancel_mono (comparison l E X K G f N)).mp
      exact hb.trans (by simp [a])
  · intro L C eC c hL
    have : DerivedCategory.TStructure.t.IsGE L c := hL
    have hQC := DerivedCategory.TStructure.t.isGE_of_iso eC.symm c
    have : C.IsGE c := (DerivedCategory.isGE_Q_obj_iff C c).mp hQC
    have hπ : QuasiIso (C.πTruncGE c) := inferInstance
    refine ⟨hπ, inferInstance, ?_, ?_, ?_⟩
    · simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    · let t := (asIso (DerivedCategory.Q.map (C.πTruncGE c))).symm ≪≫ eC
      let α : tower l E X (C.truncGE c) ⋙ DerivedCategory.Q ⟶ derivedTower l E X L :=
        NatTrans.ofSequence (fun _ ↦ t.hom) (by
          intro n
          simp only [tower, derivedTower, Functor.comp_map,
            Functor.ofSequence_map_homOfLE_succ]
          change DerivedCategory.Q.map (l • 𝟙 (C.truncGE c)) ≫ t.hom =
            t.hom ≫ (l • 𝟙 L)
          rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
          simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
            Category.id_comp, Category.comp_id])
      have : IsIso α := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro n
        exact t.isIso_hom
      refine ⟨asIso α, fun n ↦ ?_⟩
      simp [α, t]
    · intro F e
      apply comparison_isIso l E X K F e
      apply hc (tower l E X (C.truncGE c)) c
      intro n q hq
      change IsZero ((C.truncGE c).X q)
      exact (CochainComplex.isStrictlyGE_iff _ _).mp inferInstance q hq

end AlgebraicGeometry.ProEtale.IntegralSequentialContinuity
