/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Normalization of the strict coefficient unit tower

Source: tower-geometric gamma proof (1) and (3), the coefficient unit's actual reductions.
(blueprint: lem-sp-coefficient-unit-tower-normalized).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale.SpFiniteOrientation

-- Unfold the diagram to compare its levels with B, but keep the shared leaves closed.
attribute [local irreducible] spCoefficientRings
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
-- Use the canonical ring instance throughout the section calculations.
attribute [local instance 20000] CommRing.toRing

section UnitEvaluation
universe c v r
variable {C : Type c} [Category.{v} C] {D : Type*} [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})

/-- Evaluation of the ring's regular module along an identity ring identification.
Source: the definition of module pushforward
(blueprint: lem-sp-coefficient-unit-tower-normalized). -/
@[irreducible] private def coefficientPushforwardUnitIso
    (S : Sheaf J RingCat.{r})
    (e : S = (F.sheafPushforwardContinuous RingCat.{r} J K).obj R) :
    (SheafOfModules.pushforward (eqToHom e)).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  subst S
  exact Iso.refl _
private theorem coefficientPushforwardUnitIso_apply_heq
    (S : Sheaf J RingCat.{r})
    (e : S = (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
    (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward (eqToHom e)).obj
      (SheafOfModules.unit R)).val.obj U) :
    HEq (((coefficientPushforwardUnitIso F R S e).hom).val.app U x) x := by
  subst S
  unfold coefficientPushforwardUnitIso
  rfl
end UnitEvaluation

private theorem semilinear_apply_heq
    {R S : Type*} [Ring R] [Ring S]
    {M M' : ModuleCat R} {N N' : ModuleCat S}
    {φ ψ : R →+* S} (hφ : φ = ψ) (hM : M = M') (hN : N = N')
    {f : M ⟶ (ModuleCat.restrictScalars φ).obj N}
    {g : M' ⟶ (ModuleCat.restrictScalars ψ).obj N'}
    (hf : HEq f g) {x : M} {y : M'} (hx : HEq x y) : HEq (f x) (g y) := by
  subst ψ M' N'
  cases eq_of_heq hf
  cases eq_of_heq hx
  rfl

section RingMap
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})

private theorem reconstructedRing_horizontal {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    (SemilinearSections.ring (coefficientSequenceTopology J)
      (SemilinearSections.systemRing J (fun i ↦ B.obj (op i))
        (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))).obj.map
          (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op =
      (forget₂ CommRingCat RingCat).map ((B.map (homOfLE h).op).hom.app U) := by
  let B' := SemilinearSections.rings J (fun i ↦ B.obj (op i))
    (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op)
  let α : B' ⟶ B := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro i
    simp only [B', SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
      Category.comp_id, Category.id_comp])
  have hh : B'.map (homOfLE h).op = B.map (homOfLE h).op := by
    simpa only [α, NatTrans.ofOpSequence_app, Category.comp_id, Category.id_comp]
      using α.naturality (homOfLE h).op
  change (forget₂ CommRingCat RingCat).map
    ((B'.map (homOfLE h).op).hom.app U ≫
      (B'.obj (op m)).obj.map (𝟙 U)) = _
  simp only [(B'.obj (op m)).obj.map_id U, Category.comp_id]
  exact congrArg (fun f : B.obj (op n) ⟶ B.obj (op m) ↦
    (forget₂ CommRingCat RingCat).map (f.hom.app U)) hh
end RingMap

private theorem isIso_app_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (τ : F ⟶ G) {K L : C} (e : K ≅ L)
    [IsIso (τ.app K)] : IsIso (τ.app L) := by
  exact IsIso.of_isIso_fac_left (τ.naturality e.hom)

private theorem adjoint_square
    {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X U : C} {Y V : D}
    (t : X ⟶ G.obj Y) (u : U ⟶ G.obj V) (en : X ⟶ U) (em : Y ⟶ V)
    (h : t ≫ G.map em = en ≫ u) :
    (adj.homEquiv X Y).symm t ≫ em = F.map en ≫ (adj.homEquiv U V).symm u := by
  apply (adj.homEquiv X V).injective
  calc
    _ = t ≫ G.map em := by
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    _ = en ≫ u := h
    _ = _ := by
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]

section ScalarUnit
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {R S : Sheaf J CommRingCat.{r}}
private abbrev scalarRing (A : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A
private abbrev scalarRestrict (φ : R ⟶ S) := SheafOfModules.restrictScalars
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

private def scalarUnitMap (φ : R ⟶ S) :
    SheafOfModules.unit (scalarRing R) ⟶
      (scalarRestrict φ).obj (SheafOfModules.unit (scalarRing S)) where
  val.app U := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map
    ((forget₂ CommRingCat RingCat).map (φ.hom.app U)))
    (fun a ↦ by ext b; exact ((φ.hom.app U).hom.map_mul a b).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _

private theorem scalarUnitMap_adjoint_isIso (φ : R ⟶ S)
    (F : SheafOfModules.{r} (scalarRing R) ⥤ SheafOfModules.{r} (scalarRing S))
    (adj : F ⊣ scalarRestrict φ) :
    IsIso ((adj.homEquiv _ _).symm (scalarUnitMap φ)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro N
  let e : (SheafOfModules.unit (scalarRing R) ⟶ (scalarRestrict φ).obj N) ≃ N.sections :=
    ((scalarRestrict φ).obj N).unitHomEquiv
  rw [← (adj.homEquiv _ _).bijective.of_comp_iff', ← e.bijective.of_comp_iff']
  convert N.unitHomEquiv.bijective using 1
  funext f
  change e (adj.homEquiv _ _ ((adj.homEquiv _ _).symm (scalarUnitMap φ) ≫ f)) =
    N.unitHomEquiv f
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  change f.val.app U ((φ.hom.app U).hom (1 : R.obj.obj U)) =
    f.val.app U (1 : S.obj.obj U)
  rw [map_one]
end ScalarUnit

-- Keep the section calculation over a variable ring diagram: specializing its proof
-- to constant quotient sheaves would make conversion unfold their sheafifications.
section UnitCoordinates
universe c v r
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (L : SheafOfModules.StrictRingSystem.{c, v, r} B)
    (N : SemilinearSections.Systems.{c, v, r} J (fun i ↦ B.obj (op i))
      (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))
    (ε : N ⟶ SheafOfModules.unit (SemilinearSections.ring (coefficientSequenceTopology J)
      (SemilinearSections.systemRing J (fun i ↦ B.obj (op i))
        (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))))
    (d : ∀ i (U : Cᵒᵖ), (L.level i).val.obj U → N.val.obj (op (i, U.unop)))
    (e : ∀ i, L.level i ⟶ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj (B.obj (op i))))
    (hs : ∀ i (U : Cᵒᵖ), HEq ((L.level i).val.obj U) (N.val.obj (op (i, U.unop))))
    (ht : ∀ {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq ((L.transition h).val.app U)
        (N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op))

variable (hd : ∀ i (U : Cᵒᵖ) (x : (L.level i).val.obj U), HEq (d i U x) x)

variable (he : ∀ i (U : Cᵒᵖ) (x : (L.level i).val.obj U),
      ((SheafOfModules.Hom.val (e i)).app U).hom x = ε.val.app (op (i, U.unop)) (d i U x))

include N ε d hs ht hd he in
private theorem unitCoordinates_transition {m n : ℕ} (h : m ≤ n) :
    L.transition h ≫ (SheafOfModules.systemRestriction B h).map (e m) =
      (e n) ≫ scalarUnitMap (B.map (homOfLE h).op) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let f := (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  let yn : N.val.obj (op (n, U.unop)) := d n U x
  let t := (L.transition h).val.app U
  have hr := congrArg RingCat.Hom.hom (reconstructedRing_horizontal J B h U)
  have htx : HEq (t x) (N.val.map f yn) := semilinear_apply_heq
    (M := (L.level n).val.obj U) (M' := N.val.obj (op (n, U.unop)))
    (N := (L.level m).val.obj U) (N' := N.val.obj (op (m, U.unop)))
    (f := t) (g := N.val.map f) hr.symm (eq_of_heq (hs n U))
      (eq_of_heq (hs m U)) (ht h U) (hd n U x).symm
  let ym : N.val.obj (op (m, U.unop)) := d m U (t x)
  have hy : ym = N.val.map f yn := eq_of_heq ((hd m U (t x)).trans htx)
  change (SheafOfModules.Hom.val (e m)).app U (t x) =
    (B.map (homOfLE h).op).hom.app U ((SheafOfModules.Hom.val (e n)).app U x)
  rw [he, he]
  change ε.val.app (op (m, U.unop)) ym = _
  rw [hy]
  have hn := ConcreteCategory.congr_hom (ε.val.naturality f) yn
  change ε.val.app (op (m, U.unop)) (N.val.map f yn) =
    (SemilinearSections.ring (coefficientSequenceTopology J)
      (SemilinearSections.systemRing J (fun i ↦ B.obj (op i))
        (fun i ↦ B.map (homOfLE (Nat.le_succ i)).op))).obj.map f
          (ε.val.app (op (n, U.unop)) yn) at hn
  exact hn.trans (ConcreteCategory.congr_hom (reconstructedRing_horizontal J B h U)
    (ε.val.app (op (n, U.unop)) yn))
end UnitCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u})

/-- Exact evaluation of the coefficient unit in the specified ordinary coordinates.
The comparison uses the ordinary evaluation isomorphism, the realization counit,
and the identity identification of the evaluated coefficient ring.
Source: tower-geometric gamma proof (1)
(blueprint: lem-sp-coefficient-unit-tower-normalized). -/
@[irreducible] private def coefficientUnitLevelIso (n : ℕ) :
    (spCoefficientEvaluation l E T (q.abelian T).equivalence n).obj
        ((b.realization T).inverse.obj
          (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))) ≅
      SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (SpTowerShriek.B l E T n)) := by
  let M := SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)
  exact ((q.ordinaryEvaluation T n).app ((b.realization T).inverse.obj M)).symm ≪≫
    (SpTowerShriek.ev l E T n).mapIso ((b.realization T).counitIso.app M) ≪≫
    coefficientPushforwardUnitIso (Prod.sectR n T.ProEt) _ _
      (SemilinearSections.evaluation_ring _ _ _ n).symm

private theorem ordinaryEvaluation_inv_sections (n : ℕ)
    (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
    (x : ((spCoefficientEvaluation l E T (q.abelian T).equivalence n).obj M).val.obj U) :
    HEq ((((q.ordinaryEvaluation T n).inv.app M).val.app U) x) x := by
  have h := q.sections T n M U
    ((((q.ordinaryEvaluation T n).inv.app M).val.app U) x)
  have he : (((q.ordinaryEvaluation T n).hom.app M).val.app U)
      ((((q.ordinaryEvaluation T n).inv.app M).val.app U) x) = x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app U) ((q.ordinaryEvaluation T n).app M).inv_hom_id) x
  exact h.symm.trans (heq_of_eq he)

private theorem coefficientUnitLevelIso_apply (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spCoefficientEvaluation l E T (q.abelian T).equivalence n).obj
      ((b.realization T).inverse.obj
        (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)))).val.obj U) :
    ((coefficientUnitLevelIso l E b q T n).hom).val.app U x =
      (((b.realization T).counitIso.app
        (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))).hom).val.app
          (op (n, U.unop))
          ((((q.ordinaryEvaluation T n).inv.app
            ((b.realization T).inverse.obj
              (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)))).val.app U) x) := by
  unfold coefficientUnitLevelIso
  let M := (b.realization T).inverse.obj
    (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))
  let y := (((SpTowerShriek.ev l E T n).map
    ((b.realization T).counitIso.app
      (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))).hom).val.app U)
    ((((q.ordinaryEvaluation T n).inv.app M).val.app U) x)
  exact eq_of_heq (coefficientPushforwardUnitIso_apply_heq
    (Prod.sectR n T.ProEt)
    (SemilinearSections.ring (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (SemilinearSections.systemRing (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)))
    (SemilinearSections.ring (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))
    (SemilinearSections.evaluation_ring (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm U y)

/-- The level identifications carry the actual strict transition to the coefficient
quotient on every section. This is an equality of ordinary module maps, before
scalar extension, complexes, or localization.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (1),
and coefficient-unit normalization, proof step 1.
(blueprint: lem-sp-coefficient-unit-tower-normalized).

Proof: write M for the inverse ordinary realization of the coefficient module.
The field SpCoefficientTowersAbelian.transitions identifies its uncurried transition
on each section with M's horizontal restriction. The realization's restrictions
field identifies that restriction with the same map in the sequence-site presentation.
The ordinaryEvaluation comparison is the identity on sections by Coordinates.sections,
so it does not change this map. Naturality of the realization counit with respect to
the horizontal arrow then identifies its conjugate with the horizontal restriction of
the actual coefficient module. That module is the unit of the sequence ring sheaf,
whose horizontal restriction is precisely the quotient homomorphism. Finally the
coefficientPushforwardUnitIso in coefficientUnitLevelIso only transports the evaluated ring along
its specified equality, so it preserves this section equation. These identities include
identity arrows and do not use surjectivity of sheaf sections or flatness of quotients. -/
private theorem coefficient_unit_transition {m n : ℕ} (h : m ≤ n) :
    ((q.abelian T).equivalence.functor.obj
      ((b.realization T).inverse.obj
        (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)))).transition h ≫
      (SheafOfModules.systemRestriction (spCoefficientCommRings l E T) h).map
        (coefficientUnitLevelIso l E b q T m).hom =
    (coefficientUnitLevelIso l E b q T n).hom ≫
      scalarUnitMap ((spCoefficientCommRings l E T).map (homOfLE h).op) := by
  let a := q.abelian T
  let C := SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T)
  let M := (b.realization T).inverse.obj C
  apply unitCoordinates_transition (Scheme.ProEt.topology T) (spCoefficientCommRings l E T)
    (a.equivalence.functor.obj M) ((b.realization T).functor.obj M)
    ((b.realization T).counitIso.app C).hom
    (fun i U x ↦ ((q.ordinaryEvaluation T i).inv.app M).val.app U x)
    (fun i ↦ (coefficientUnitLevelIso l E b q T i).hom)
  · intro i U
    exact (a.sections M i U).trans (b.sections T M i U).symm
  · intro m n h U
    exact (a.transitions M h U).trans (b.restrictions T M _).symm
  · intro i U x
    exact ordinaryEvaluation_inv_sections l E b q T i M U x
  · intro i U x
    exact coefficientUnitLevelIso_apply l E b q T i U x

private theorem coefficientLevelKFlat (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := SpTowerShriek.B l E T n)
      (((spCoefficientEvaluation l E T (q.abelian T).equivalence n).mapHomologicalComplex
        (.up ℤ)).obj
        ((CochainComplex.singleFunctor (spCoefficientTowers l E T) 0).obj
          ((b.realization T).inverse.obj
            (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))))) := by
  let a := q.abelian T
  let := a.equivalenceAdditive
  let := a.evaluationLimits n
  let := a.evaluationColimits n
  let F := spCoefficientEvaluation l E T a.equivalence n
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let M := (b.realization T).inverse.obj
    (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))
  let P := ((CochainComplex.singleFunctor (spCoefficientTowers l E T) 0).obj M)
  let R := SpTowerShriek.B l E T n
  let A := SheafOfModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let e : (F.mapHomologicalComplex (.up ℤ)).obj P ≅
      (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit _) :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M ≪≫
      (CochainComplex.singleFunctor A 0).mapIso (coefficientUnitLevelIso l E b q T n)
  have hb : CochainComplex.IsStrictlyLE ((F.mapHomologicalComplex (.up ℤ)).obj P) 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (SheafOfModules.unit _) i (by omega)).of_iso ((HomologicalComplex.eval A _ i).mapIso e)
  have hf (i : ℤ) : SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T) (R := R)
      (((F.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
    apply (exactFunctor A A).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm
    have hcat : ObjectProperty.flat
        (((CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit _)).X i) := by
      by_cases hi : i = 0
      · subst i
        exact (ObjectProperty.flat.prop_iff_of_iso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (SheafOfModules.unit _))).2
          (ObjectProperty.prop_unit _)
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
    exact ((ObjectProperty.flat.prop_iff_of_iso
      ((HomologicalComplex.eval A _ i).mapIso e)).2 hcat).2
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0 hf

/-- The actual coefficient unit, in the inverse section coordinates, has invertible
canonical derived reductions. No exceptional inverse image or smoothness is involved.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (1) and (3).
(blueprint: lem-sp-coefficient-unit-tower-normalized).

Proof: the coefficient module on the sequence site evaluates to the free rank-one
constant quotient module at every positive level. Its strict transitions are the actual
quotient homomorphisms. The section-preserving realization and uncurrying equivalences
preserve these modules and transitions. The ordinary reduction is their scalar adjunct:
on local tensors it sends b tensor a to b*q(a). Multiplication identifies this extension
with the smaller coefficient unit, with inverse b mapping to b tensor 1. The coefficient
unit is flat and its degree-zero single complex is K-flat, so the universal derived
scalar comparison on this complex is invertible. The representative equation
SpCoefficientTowersAbelian.reduction_rep identifies the canonical derived reduction
with that comparison followed by ordinary multiplication, up to the invertible exact
evaluation comparisons. Thus every canonical reduction is invertible. Equal levels use
the tensor unitor. This works for ramified extensions and empty schemes, and uses no
flatness of the quotient as a module over the larger quotient ring. -/
theorem coefficient_unit_tower_normalized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) :
    IsSpNormalizedTower l E T (q.abelian T)
      ((SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj
        (SpTowerClasses.unit T (SpTowerClasses.Arings l E T))) := by
  let a := q.abelian T
  let := a.hasDerived
  let := a.equivalenceAdditive
  let := b.realizationAdditive T
  let M := (b.realization T).inverse.obj
    (SpTowerClasses.coefficient T (SpTowerClasses.Arings l E T))
  let P := (CochainComplex.singleFunctor (spCoefficientTowers l E T) 0).obj M
  let R := SpTowerCalculus.realization l E b T a
  let e : DerivedCategory.Q.obj P ≅
      R.inverse.obj (SpTowerClasses.unit T (SpTowerClasses.Arings l E T)) :=
    (R.unitIso.app _) ≪≫ R.inverse.mapIso
      (((b.realization T).functor.mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).mapIso
          ((b.realization T).counitIso.app _))
  intro m n h
  have := a.evaluationLimits n
  have := a.evaluationColimits n
  have := a.evaluationLimits m
  have := a.evaluationColimits m
  have hOrd : IsIso ((a.ordinaryReduction h).app M) := by
    let φ := (spCoefficientCommRings l E T).map (homOfLE h).op
    let adj := SheafOfModules.systemTensorAdj a.scalar (spCoefficientCommRings l E T) h
    let en := coefficientUnitLevelIso l E b q T n
    let em := coefficientUnitLevelIso l E b q T m
    let f := (adj.homEquiv _ _).symm (scalarUnitMap φ)
    have : IsIso f := scalarUnitMap_adjoint_isIso φ _ adj
    have he : (a.ordinaryReduction h).app M ≫ em.hom =
        (SheafOfModules.systemTensor a.scalar (spCoefficientCommRings l E T) h).map en.hom ≫
          f := by
      rw [a.ordinaryReduction_eq]
      exact adjoint_square adj _ _ en.hom em.hom
        (coefficient_unit_transition l E b q T h)
    have : IsIso ((a.ordinaryReduction h).app M ≫ em.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ em.hom
  have hChain : IsIso
      ((NatTrans.mapHomologicalComplex (a.ordinaryReduction h) (.up ℤ)).app P) := by
    have : (spCoefficientEvaluation l E T a.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    have : (spCoefficientEvaluation l E T a.equivalence m).Additive :=
      Functor.additive_of_preserves_binary_products _
    have hi (i : ℤ) : IsIso ((a.ordinaryReduction h).app (P.X i)) := by
      by_cases hi : i = 0
      · subst i
        exact isIso_app_of_iso (a.ordinaryReduction h)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm
      · have hz : IsZero (P.X i) :=
          HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
        exact ((spCoefficientEvaluation l E T a.equivalence n ⋙
          SheafOfModules.systemTensor a.scalar (spCoefficientCommRings l E T) h).map_isZero
          hz).isIso ((spCoefficientEvaluation l E T a.equivalence m).map_isZero hz) _
    have hComponents : ∀ i : ℤ, IsIso
        (((NatTrans.mapHomologicalComplex (a.ordinaryReduction h) (.up ℤ)).app P).f i) := by
      intro i
      change IsIso ((a.ordinaryReduction h).app (P.X i))
      exact hi i
    exact HomologicalComplex.Hom.isIso_of_components _
  have := (a.scalar ((spCoefficientCommRings l E T).map (homOfLE h).op)).model.computes
    _ (coefficientLevelKFlat l E b q T n)
  have hc : IsIso ((a.reduction h).app (DerivedCategory.Q.obj P)) := by
    rw [a.reduction_rep h P]
    infer_instance
  exact isIso_app_of_iso (a.reduction h) e

end AlgebraicGeometry.ProEtale.SpFiniteOrientation
