/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.Algebra.Homology.System.SystemScalarModel
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
/-! # Exact scalar transport on strict etale systems -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf
  SheafOfModules.siteCoefficientTensor SheafOfModules.siteCoefficientTensorAdj
private theorem scalarSystemHom_ext
    {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O] {ell : O}
    {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def restrictionSquare {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B D E : Sheaf J RingCat.{u + 1}}
    (f : A ⟶ B) (g : D ⟶ E) (p : D ⟶ A) (q : E ⟶ B) (h : p ≫ f = g ≫ q) :
    restrictScalars.{u + 1} f ⋙ restrictScalars p ≅
      restrictScalars q ⋙ restrictScalars g :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) p f ≪≫ pushforwardCongr h ≪≫
    (pushforwardComp (F := 𝟭 C) (G := 𝟭 C) g q).symm

section ScalarOrdinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  {T : Scheme.{u}}
  (PA : StrictEtaleEvaluation T O ell)

private theorem scalarStageSquare {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h) ≫
        a.sheaf T n =
      a.sheaf T m ≫ coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h := by
  change (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ =
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change a.ring n (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) (a.ring m (Ideal.Quotient.mk _ x))
  rw [a.generators, a.generators]
  rfl

private abbrev scalarStageExtension (n : ℕ) :=
  siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
private abbrev scalarStageRestriction (n : ℕ) :=
  restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
private abbrev scalarStageAdj (n : ℕ) :=
  siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)

private def scalarRestrictionSquare {m n : ℕ} (h : n ≤ m) :
    scalarStageRestriction a (T := T) n ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ≅
      coefficientRestriction (J := T.smallEtaleTopology) O' mu h ⋙
        scalarStageRestriction a (T := T) m :=
  restrictionSquare
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T m))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (coefficientQuotientMap O ell (index.monotone h)))
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (coefficientQuotientMap O' mu h))
    (by
      simpa only [Functor.map_comp] using congrArg
        (sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (scalarStageSquare a (T := T) h))

private def scalarSuccessor {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ⋙
        scalarStageExtension a (T := T) m ⟶
      scalarStageExtension a (T := T) n ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O' mu h :=
  ((mateEquiv (scalarStageAdj a (T := T) n) (scalarStageAdj a (T := T) m)).symm
    (.mk _ _ _ _ (scalarRestrictionSquare a (T := T) h).hom)).natTrans

private def scalarOrdinary :
    strictEtaleCoefficientSystem T O ell ⥤ strictEtaleCoefficientSystem T O' mu where
  obj M := {
    level := fun n ↦ (scalarStageExtension a (T := T) n).obj (M.level (index n))
    transition := fun n ↦
      (scalarStageExtension a (T := T) (n + 1)).map
        ((PA.strictTransition (index.monotone (Nat.le_succ n))).app M) ≫
          (scalarSuccessor a (T := T) (Nat.le_succ n)).app (M.level (index n)) }
  map f := {
    app := fun n ↦ (scalarStageExtension a (T := T) n).map (f.app (index n))
    comm := by
      intro n
      let h := index.monotone (Nat.le_succ n)
      let Em := scalarStageExtension a (T := T) (n + 1)
      let En := scalarStageExtension a (T := T) n
      let RA := coefficientRestriction (J := T.smallEtaleTopology) O ell h
      let RB := coefficientRestriction (J := T.smallEtaleTopology) O' mu (Nat.le_succ n)
      let θ := scalarSuccessor a (T := T) (Nat.le_succ n)
      have h₁ := (PA.strictTransition h).naturality f
      have h₂ := θ.naturality (f.app (index n))
      change Em.map _ ≫ (Em.map _ ≫ θ.app _) = (Em.map _ ≫ θ.app _) ≫ RB.map _
      calc
        _ = Em.map (f.app (index (n + 1)) ≫ (PA.strictTransition h).app _) ≫
            θ.app _ := by rw [Em.map_comp, Category.assoc]
        _ = Em.map ((PA.strictTransition h).app _ ≫ RA.map (f.app (index n))) ≫
            θ.app _ := congrArg (fun k ↦ Em.map k ≫ θ.app _) h₁
        _ = Em.map ((PA.strictTransition h).app _) ≫
            (Em.map (RA.map (f.app (index n))) ≫ θ.app _) := by
          rw [Em.map_comp, Category.assoc]
        _ = Em.map ((PA.strictTransition h).app _) ≫
            (θ.app _ ≫ RB.map (En.map (f.app (index n)))) :=
          congrArg (fun k ↦ Em.map ((PA.strictTransition h).app _) ≫ k) h₂
        _ = _ := (Category.assoc _ _ _).symm }
  map_id M := by
    apply scalarSystemHom_ext
    funext n
    exact (scalarStageExtension a (T := T) n).map_id _
  map_comp f g := by
    apply scalarSystemHom_ext
    funext n
    exact (scalarStageExtension a (T := T) n).map_comp _ _

private instance scalarOrdinary_additive : (scalarOrdinary a PA).Additive where
  map_add {M N f g} := by
    apply scalarSystemHom_ext
    funext n
    change (scalarStageExtension a (T := T) n).map ((f + g).app (index n)) = _
    rw [show (f + g).app (index n) = f.app (index n) + g.app (index n) from
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell)
        (index n)).map_add]
    calc
      _ = (scalarStageExtension a (T := T) n).map (f.app (index n)) +
          (scalarStageExtension a (T := T) n).map (g.app (index n)) :=
        (scalarStageExtension a (T := T) n).map_add
      _ = _ := ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O')
        (ell := mu) n).map_add (f := (scalarOrdinary a PA).map f)
          (g := (scalarOrdinary a PA).map g)).symm

private def scalarUnit (n : ℕ) :
    coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        SheafOfModules.toSheaf.{u + 1} _ ⟶
      scalarOrdinary a PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n ⋙
          SheafOfModules.toSheaf.{u + 1} _ where
  app M := siteTensorUnitUnderlying (a.sheaf T n) (M.level (index n))
  naturality {M N} f := by
    change (SheafOfModules.toSheaf _).map (f.app (index n)) ≫
      siteTensorUnitUnderlying (a.sheaf T n) (N.level (index n)) =
        siteTensorUnitUnderlying (a.sheaf T n) (M.level (index n)) ≫
          (SheafOfModules.toSheaf _).map
            ((scalarStageExtension a (T := T) n).map (f.app (index n)))
    have h := (scalarStageAdj a (T := T) n).unit.naturality (f.app (index n))
    ext V x
    exact congrArg (fun k ↦ k.val.app V x) h

set_option maxRecDepth 10000 in
private theorem scalarUnit_transition (n : ℕ) (M : strictEtaleCoefficientSystem T O ell) :
    (scalarUnit a PA (n + 1)).app M ≫
        strictEtaleTransition (scalarOrdinary a PA |>.obj M) n =
      coefficientTransitionUnderlying (index.monotone (Nat.le_succ n))
        (PA.strictTransition (index.monotone (Nat.le_succ n))) M ≫
          (scalarUnit a PA n).app M := by
  have hn := (scalarStageAdj a (T := T) (n + 1)).unit.naturality
    ((PA.strictTransition (index.monotone (Nat.le_succ n))).app M)
  have hm := unit_mateEquiv_symm (scalarStageAdj a (T := T) n)
    (scalarStageAdj a (T := T) (n + 1))
    (.mk _ _ _ _ (scalarRestrictionSquare a (T := T) (Nat.le_succ n)).hom)
    (M.level (index n))
  ext V x
  have hh := congrArg (fun k ↦ k.val.app V x) hn
  have hu := congrArg (fun k ↦ k.val.app V
    (((PA.strictTransition (index.monotone (Nat.le_succ n))).app M).val.app V x)) hm
  change _ = _ at hh hu
  dsimp only [Functor.comp_map, Functor.id_map] at hh hu
  exact (congrArg (fun y ↦
    ((scalarSuccessor a (T := T) (Nat.le_succ n)).app (M.level (index n))).val.app V y)
      hh).symm.trans hu.symm


private theorem evaluation_jointlyReflects :
    JointlyReflectIsomorphisms
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).1
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := T.smallEtaleTopology) O' mu
          (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩
    · apply scalarSystemHom_ext
      funext n
      exact IsIso.hom_inv_id (f.app n)
    · apply scalarSystemHom_ext
      funext n
      exact IsIso.inv_hom_id (f.app n)


private theorem scalarOrdinary_exact
    (hflat : ∀ n, PreservesFiniteLimits (scalarStageExtension a (T := T) n)) :
    PreservesFiniteLimits (scalarOrdinary a PA) ∧
      PreservesFiniteColimits (scalarOrdinary a PA) := by
  have : ∀ n, PreservesFiniteLimits (scalarStageExtension a (T := T) n) := hflat
  have : ∀ n, PreservesFiniteColimits (scalarStageExtension a (T := T) n) :=
    fun n ↦ by
      let : PreservesColimitsOfSize.{0, 0} (scalarStageExtension a (T := T) n) :=
        (scalarStageAdj a (T := T) n).leftAdjoint_preservesColimits
      infer_instance
  have hlA (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).1
  have hcA (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O) (ell := ell) n).2
  have hlB (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O') (ell := mu) n).1
  have hcB (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n) :=
    (coefficientEvaluation_exact (J := T.smallEtaleTopology) (O := O') (ell := mu) n).2
  have hl (n : ℕ) : PreservesFiniteLimits
      (scalarOrdinary a PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n) := by
    change PreservesFiniteLimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        scalarStageExtension a (T := T) n)
    infer_instance
  have hc (n : ℕ) : PreservesFiniteColimits
      (scalarOrdinary a PA ⋙ coefficientEvaluation
        (J := T.smallEtaleTopology) (O := O') (ell := mu) n) := by
    change PreservesFiniteColimits
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        scalarStageExtension a (T := T) n)
    infer_instance
  constructor
  · constructor
    intro I _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨(evaluation_jointlyReflects (T := T) (O' := O') (mu := mu)).jointlyReflectsLimit
      (fun n ↦ isLimitOfPreserves
        (scalarOrdinary a PA ⋙ coefficientEvaluation
          (J := T.smallEtaleTopology) (O := O') (ell := mu) n) hc)⟩
  · constructor
    intro I _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨(evaluation_jointlyReflects (T := T) (O' := O') (mu := mu)).jointlyReflectsColimit
      (fun n ↦ isColimitOfPreserves
        (scalarOrdinary a PA ⋙ coefficientEvaluation
          (J := T.smallEtaleTopology) (O := O') (ell := mu) n) hc)⟩


private theorem scalarLevel (n : ℕ)
    (hflat : PreservesFiniteLimits (scalarStageExtension a (T := T) n)) :
    ∃ L : StrictEtaleLevelScalar a T n,
      ∀ K, IsIso (L.counit.app K) := by
  let E := siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
  have : PreservesFiniteLimits E := hflat
  have : PreservesFiniteColimits E := by
    let : PreservesColimitsOfSize.{0, 0} E :=
      (scalarStageAdj a (T := T) n).leftAdjoint_preservesColimits
    infer_instance
  let R := restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  have : PreservesFiniteLimits R := (systemScalarRestriction_exact (a.sheaf T n)).1
  have : PreservesFiniteColimits R := (systemScalarRestriction_exact (a.sheaf T n)).2
  obtain ⟨_, L, ε, hu, hc, adj, ht⟩ :=
    CategoryTheory.Adjunction.exists_leftDerived_adjunction E R
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n)) (fun _ ↦ True)
      (fun K ↦ ⟨K, 𝟙 K, trivial, inferInstance⟩)
      (fun f _ _ hf ↦ by
        let := hf
        infer_instance)
  exact ⟨{
    derived := L
    counit := ε
    isDerived := hu
    computes := fun K _ ↦ hc K trivial
    restriction := R.mapDerivedCategory
    restrictionFactors := R.mapDerivedCategoryFactors
    derivedAdj := adj
    transpose := ht }, fun K ↦ hc K trivial⟩


end ScalarOrdinary

/-- Exact termwise scalar extension on strict coefficient systems, retaining its
ordinary tensor unit, successor equation and normalized derived evaluation square.
Source: Zheng, Construction 4.1, and Construction 5.15.
(blueprint: lem-pur-strict-etale-exact-coefficient-transport).

Proof: form the componentwise tensor extension. The successor is the transpose
of the source successor under extension/restriction, followed by the tensor-unit
map for the lower coefficient stage. The coefficient generator square identifies
the two restrictions. Naturality and the triangle identities prove the functor
laws and the successor unit equation. Evaluation identifies this functor with
ordinary tensor at each level. Evaluation jointly reflects limits and colimits,
so left exactness at every stage and the scalar adjunction make the system functor
exact. Derive it termwise. Each level has exact tensor extension and exact
restriction, hence the derived adjunction exists. The derived-functor comparison
counit is invertible on every complex. The independently sized derived-square theorem
compares the given endpoint evaluation records using their universal counits. Its
representative equation, together with the ordinary tensor units just constructed,
fills all transport coherence fields.
-/
theorem nonempty_strictEtaleExactCoefficientTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    {T : Scheme.{u}}
    (PA : StrictEtaleEvaluation T O ell) (PB : StrictEtaleEvaluation T O' mu)
    (hflat : ∀ n, PreservesFiniteLimits (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))) :
    Nonempty (StrictEtaleCoefficientTransport a T PA PB) := by
  classical
  let F := scalarOrdinary a PA
  have : PreservesFiniteLimits F := (scalarOrdinary_exact a PA hflat).1
  have : PreservesFiniteColimits F := (scalarOrdinary_exact a PA hflat).2
  choose L hL using fun n ↦ scalarLevel a (T := T) n (hflat n)
  have hI (n : ℕ) : IsIso (L n).counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hL n
  let α (n : ℕ) : F ⋙ coefficientEvaluation
      (J := T.smallEtaleTopology) (O := O') (ell := mu) n ≅
      coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n) ⋙
        siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) := Iso.refl _
  choose δ hδ using fun n ↦ exists_derivedSquare_independentUniverses F
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := ell) (index n))
    (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n)
    (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    F.mapDerivedCategory (PA.evaluation (index n)) (PB.evaluation n) (L n).derived
    F.mapDerivedCategoryFactors (PA.evaluationFactors (index n)) (PB.evaluationFactors n)
    (asIso (L n).counit) (α n)
  let U : StrictEtaleCoefficientTransportData a T PA PB := {
    ordinary := F
    evaluation := α
    unit := scalarUnit a PA
    derived := F.mapDerivedCategory
    factors := F.mapDerivedCategoryFactors
    level := L
    derivedEvaluation := δ }
  refine ⟨⟨U, ?_⟩⟩
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, ?_, ?_⟩
  · intro n M
    simp only [U, α, scalarUnit, Iso.refl_inv, NatTrans.id_app]
    change _ = _ ≫ (SheafOfModules.toSheaf _).map (𝟙 _)
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  · intro n M
    exact scalarUnit_transition a PA n M
  · intro n K
    exact hδ n K



end AlgebraicGeometry
