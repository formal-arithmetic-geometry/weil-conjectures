/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientAugmentation
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Lean.Meta.CongrTheorems
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.CanonicalFinitePadicRestriction
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCyclicAugmentationZero
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.RootEndpointTranspose.ShiftHelpers.DiagonalRootEndpointTransposeCore
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalShiftedLimitProjection
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Quotient and normalized endpoint comparisons for cyclic coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

private instance diagonalForget_faithful (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (diagonalForget l X).Faithful := ⟨fun {M N} f g h ↦ by
  ext T x
  exact congrArg (fun k ↦ (k.hom.app T).hom x) h⟩

-- Build explicit congruence proofs at derived-functor conversion boundaries.
-- The kernel checks every generated equality; leaves use only definitional equality.

private meta def structuralProof (a b : Expr) : Nat → MetaM Expr
  | 0 => do
    unless ← isDefEq a b do throwError "nonconvertible leaf"
    mkHEqRefl a
  | fuel + 1 => do
    let a := (← instantiateMVars a).cleanupAnnotations
    let b := (← instantiateMVars b).cleanupAnnotations
    if a == b then return ← mkHEqRefl a
    let f := a.getAppFn
    if f.isConst && f == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs &&
        a.getAppNumArgs > 0 &&
        !([``Functor.mapDerivedCategory, ``DerivedCategory.singleFunctor,
          ``Functor.mapDerivedCategorySingleFunctor].contains f.constName!) then
      try
        let c ← mkHCongrWithArity f a.getAppNumArgs
        let mut proof := c.proof
        for ((x, y), kind) in (a.getAppArgs.zip b.getAppArgs).zip c.argKinds do
          match kind with
          | .eq =>
            proof := mkAppN proof #[x, y, ← mkEqOfHEq (← structuralProof x y fuel)]
          | .heq =>
            proof := mkAppN proof #[x, y, ← structuralProof x y fuel]
          | .fixed => proof := mkApp proof x
          | _ => throwError "unexpected congruence argument"
        if (← inferType proof).isHEq then return proof
        return ← mkHEqOfEq proof
      catch _ => pure ()
    unless ← isDefEq a b do throwError "nonconvertible terms"
    mkHEqRefl a

-- Transport proposition arguments explicitly instead of asking the kernel to
-- compare two fully expanded component maps of the same derived functor.

private meta def structuralExact (t : Syntax) : TacticM Unit := withMainContext do
  let t ← t.replaceM fun stx => do
    match stx with
    | .ident info raw name _ =>
      pure (some (.ident info raw name.eraseMacroScopes []))
    | _ => pure none
  let full ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let full ← instantiateMVars full
  if full.hasExprMVar then throwError "unresolved metavariables"
  let mut app := full.getAppFn
  for arg in full.getAppArgs do
    let fnType ← whnf (← inferType app)
    let .forallE _ expectedType _ _ := fnType | throwError "not a function"
    let actualType ← inferType arg
    let mut arg := arg
    if actualType != expectedType && (← isProp expectedType) then
      let h ← mkEqOfHEq (← structuralProof (← whnf actualType) (← whnf expectedType) 12)
      arg ← mkAppM ``Eq.mp #[h, arg]
    app := mkApp app arg
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  let actualType ← whnf (← inferType app)
  if actualType != target then
    let h ← mkEqOfHEq (← structuralProof actualType target 12)
    app ← mkAppM ``Eq.mp #[h, app]
  goal.assign app
  replaceMainGoal []

private theorem cyclic_discrete_map
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod l X)]
    {M N : DerivedCategory (DiagonalCompleted l X)} (f : M ⟶ N) :
    (cyclicDiscreteRestriction l X).map f =
      (diagonalCompletedRestriction l X).mapDerivedCategory.map f := by
  rfl

/-- The exact-single comparison followed by the specified shift, retained as named data. -/
@[irreducible] private def shifted_single_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : A) (j : ℤ) :
    F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor A 0).obj P)⟦j⟧) ≅
      ((DerivedCategory.singleFunctor B 0).obj (F.obj P))⟦j⟧ :=
  (F.mapDerivedCategory.commShiftIso j).app _ ≪≫
    (shiftFunctor _ j).mapIso ((F.mapDerivedCategorySingleFunctor 0).app P)

private theorem shifted_single_iso_hom
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : A) (j : ℤ) :
    (shifted_single_iso F P j).hom =
      (F.mapDerivedCategory.commShiftIso j).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app P)⟦j⟧' := by
  simp only [shifted_single_iso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]

private theorem shifted_single_map_injective
    {A B : Type*} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {M N : A} (j : ℤ)
    (f g : ((DerivedCategory.singleFunctor A 0).obj M)⟦j⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj N)⟦j⟧)
    (h : F.mapDerivedCategory.map f = F.mapDerivedCategory.map g) : f = g := by
  obtain ⟨f, rfl⟩ := (shiftFunctor (DerivedCategory A) j).map_surjective f
  obtain ⟨g, rfl⟩ := (shiftFunctor (DerivedCategory A) j).map_surjective g
  apply congrArg (shiftFunctor (DerivedCategory A) j).map
  obtain ⟨f, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective f
  obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective g
  have h0 : F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map f) =
      F.mapDerivedCategory.map ((DerivedCategory.singleFunctor A 0).map g) := by
    apply (shiftFunctor (DerivedCategory B) j).map_injective
    apply (cancel_epi ((F.mapDerivedCategory.commShiftIso j).hom.app _)).1
    rw [← F.mapDerivedCategory.commShiftIso_hom_naturality _ j,
      ← F.mapDerivedCategory.commShiftIso_hom_naturality _ j, h]
  congr 1
  apply F.map_injective
  apply (DerivedCategory.singleFunctor B 0).map_injective
  apply (cancel_epi ((F.mapDerivedCategorySingleFunctor 0).hom.app M)).1
  have hf := (F.mapDerivedCategorySingleFunctor 0).hom.naturality f
  have hg := (F.mapDerivedCategorySingleFunctor 0).hom.naturality g
  dsimp only [Functor.comp_map] at hf hg
  rw [← hf, ← hg, h0]

/-- Cancel the single of an ordinary epimorphism between shifted single objects.
Fullness of the shift and single embedding reduces this to ordinary cancellation;
faithful exact forgetting detects only these degree-zero morphisms. -/
private theorem shifted_single_cancel_epi
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.Faithful] {P M N : A} (q : P ⟶ M) [Epi q] (j : ℤ)
    (f g : ((DerivedCategory.singleFunctor A 0).obj M)⟦j⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj N)⟦j⟧)
    (h : F.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor A 0).map q)⟦j⟧' ≫ f) =
      F.mapDerivedCategory.map
        (((DerivedCategory.singleFunctor A 0).map q)⟦j⟧' ≫ g)) : f = g := by
  let S := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor (DerivedCategory A) j
  obtain ⟨f, rfl⟩ := S.map_surjective f
  obtain ⟨g, rfl⟩ := S.map_surjective g
  apply congrArg S.map
  apply (cancel_epi q).1
  apply S.map_injective
  apply shifted_single_map_injective F j
  simpa only [S, Functor.map_comp, Functor.comp_map] using h

/-- The projection path identified by the normalized root cone. -/
@[irreducible] private def endpoint_path_equation
    {A : Type*} [Category A] {X Y T Q P : A}
    (path : X ⟶ Y) (b : Y ≅ T) (cH : T ≅ Q) (cP : X ≅ P) (q : P ⟶ Q) : Prop :=
  path ≫ b.hom ≫ cH.hom = cP.hom ≫ q

private theorem target_limit_map_eq
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y)) [HasLimit H]
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H) :
    diagonalTargetLimitMap l Y D H b L t0 =
      diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
        L (Scheme.purTwistZlModule (diagonalSurface Y) l) H _ t0 b := by
  unfold diagonalTargetLimitMap
  rfl

private theorem shifted_limit_projection
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B)
    (J : DerivedCategory (ℕᵒᵖ ⥤ B))
    (t : F.obj P ≅ limit H)
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) (n : ℕ) :
    endpoint_path_equation
      (diagonalShiftedSingleLimitComparison F L P H J t b ≫ (L.projection n).app J)
      (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.mapIso b)
      (shifted_single_iso ((evaluation ℕᵒᵖ B).obj (op n)) H (2 : ℤ))
      (shifted_single_iso F P (2 : ℤ))
      (((DerivedCategory.singleFunctor B 0).map (t.hom ≫ limit.π H (op n)))⟦(2 : ℤ)⟧') := by
  unfold endpoint_path_equation
  simp only [Functor.mapIso_hom]
  simp only [shifted_single_iso_hom, Category.assoc]
  unfold diagonalShiftedSingleLimitComparison
  simp only [Category.assoc]
  erw [(L.projection n).naturality_assoc]
  rw [← ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map_comp_assoc,
    b.inv_hom_id,
    ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [DiagonalTrace.local_shifted_limit_projection]

private theorem root_limit_comparison_projection
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (H : DiagonalSystems l X) [HasLimit H]
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (n : ℕ) :
    (diagonalRootLimitComparison l X H roots).inv ≫
        (diagonalForget l X).map (limit.π H (op n)) ≫ roots.hom.app (op n) =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) := by
  simp [diagonalRootLimitComparison, Category.assoc, preservesLimitIso_inv_π_assoc]

private theorem root_system_limit_projection_epi
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤)))
    (H : DiagonalSystems l X) [HasLimit H]
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (n : ℕ) :
    Epi (limit.π H (op n)) := by
  let U := diagonalForget l X
  have : U.Faithful := diagonalForget_faithful l _
  apply U.epi_of_epi_map
  have hT (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x trivial).hom
  have : Epi (Scheme.rootTowerProjection X l n) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mp
      (Scheme.rootTower_finite_tensor X l hT n).1
  have : Epi (limit.π
      (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)) := by
    exact inferInstanceAs (Epi (Scheme.rootTowerProjection X l n))
  have hepi : Epi ((diagonalRootLimitComparison l X H roots).inv ≫
      U.map (limit.π H (op n)) ≫ roots.hom.app (op n)) := by
    rw [root_limit_comparison_projection]
    infer_instance
  have : Epi (U.map (limit.π H (op n)) ≫ roots.hom.app (op n)) :=
    epi_of_epi (diagonalRootLimitComparison l X H roots).inv _
  exact (epi_comp_iff_of_isIso _ (roots.hom.app (op n))).mp this

private theorem normalized_root_composite
    {C : Type*} [Category C] {P I J K L M N R S T : C}
    (α r : P ⟶ I) (m : I ⟶ J) (v : J ⟶ K) (q : K ⟶ L)
    (c : L ⟶ M) [Mono c] (d : J ⟶ N) (f : N ⟶ M)
    (t0 : P ⟶ R) (π : R ⟶ S) (t : S ⟶ L) (rn : S ⟶ T)
    (rp : P ⟶ T) (k : T ⟶ M)
    (hα : α = r) (hv : v ≫ q ≫ c = d ≫ f)
    (hp : (r ≫ m) ≫ d ≫ f = rp ≫ k)
    (hπ : t0 ≫ π ≫ rn = rp) (ht : t ≫ c = rn ≫ k) :
    α ≫ m ≫ v ≫ q = t0 ≫ π ≫ t := by
  apply (cancel_mono c).1
  calc
    (α ≫ m ≫ v ≫ q) ≫ c = α ≫ m ≫ d ≫ f := by
      simp only [Category.assoc]
      rw [hv]
    _ = rp ≫ k := by
      rw [hα]
      simpa only [Category.assoc] using hp
    _ = (t0 ≫ π ≫ rn) ≫ k := by rw [hπ]
    _ = (t0 ≫ π ≫ t) ≫ c := by
      simp only [Category.assoc]
      rw [ht]

/-- The actual ordinary root arrow underlying the finite endpoint is the supplied
root-cone projection. Integral root uniqueness, the finite kernel inclusion, and
both endpoint normalizations determine every factor of the composite. -/
private theorem ordinary_cyclic_root_projection
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    (eW : CompletedRealization l (diagonalSurface Y))
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (H : DiagonalSystems l (diagonalSurface Y)) [HasLimit H]
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (t : H.obj (op n) ≅ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (ht : DiagonalTrace.FiniteRootNormalization l Y hY H roots n t) :
    eW.underlying.inv.app (Scheme.purTwistZlModule (diagonalSurface Y) l) ≫
        eW.lineIso.hom.hom ≫ cyclicLineMap l n (diagonalSurface Y) ≫
        (cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n (diagonalSurface Y)) ≫
        (diagonalForget l (diagonalSurface Y)).map
          ((diagonalFiniteToPadic l n (diagonalSurface Y)).map p.lineEndpoint.iso.hom) =
      (diagonalForget l (diagonalSurface Y)).map
        (t0.hom ≫ limit.π H (op n) ≫ t.hom) := by
  let X := diagonalSurface Y
  let U := diagonalForget l X
  let Q := geoCartierLine (diagonalResidue l n) (l ^ (n + 1))
    (cartierResidue_cast l (n + 1)) X
  let c := diagonalFiniteForgetIso l n X
  have hr := congrArg IntegralRoots.hom
    (diagonalIntegralRoots_unique l X (bottomField l) eW.roots p.integralRoots)
  have hα := (eq_of_heq eW.line_normalization).trans hr
  have hp := p.lineEndpoint.normalization
  dsimp only [FiniteRealization.LineNormalization] at hp
  have ht' := ht
  unfold DiagonalTrace.FiniteRootNormalization at ht'
  have htmap := diagonalFiniteForgetIso_transport l n X
    (U.obj (H.obj (op n))) Q (U.map t.hom) _ ht'
  have hf := finiteRoots_toLine_eq_cartierProRootMap p.finiteRoots (diagonalResidue l n)
    (cartierResidue_cast l (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (diagonalSurface_power_unit l Y hY n)
  rw [← hf] at htmap
  have hπ : U.map t0.hom ≫ U.map (limit.π H (op n)) ≫ roots.hom.app (op n) =
      limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) := by
    rw [eq_of_heq ht0]
    exact root_limit_comparison_projection l X H roots n
  have hv : (cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n X) ≫
      U.map ((diagonalFiniteToPadic l n X).map p.lineEndpoint.iso.hom) ≫ c.inv.app Q =
    p.eW.underlying.inv.app (cyclicLine l n X) ≫
      (cartierForget (diagonalResidue l n) X).map p.lineEndpoint.iso.hom := by
    simp only [cyclicFiniteUnderlying, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]
    have hn := c.inv.naturality p.lineEndpoint.iso.hom
    dsimp only [Functor.comp_map] at hn
    rw [hn]
    simp only [c, X, Iso.hom_inv_id_app_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    normalized_root_composite
      (eW.underlying.inv.app (Scheme.purTwistZlModule X l) ≫ eW.lineIso.hom.hom)
      p.integralRoots.hom (cyclicLineMap l n X)
      ((cyclicFiniteUnderlying l Y n p).inv.app (cyclicLine l n X))
      (U.map ((diagonalFiniteToPadic l n X).map p.lineEndpoint.iso.hom))
      (c.inv.app Q) (p.eW.underlying.inv.app (cyclicLine l n X))
      ((cartierForget (diagonalResidue l n) X).map p.lineEndpoint.iso.hom)
      (U.map t0.hom) (U.map (limit.π H (op n))) (U.map t.hom)
      (roots.hom.app (op n))
      (limit.π (Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n))
      (p.finiteRoots.toLine (diagonalResidue l n) (cartierResidue_cast l (n + 1)))
      hα hv hp hπ htmap

private theorem whisker_left_shift_compatibility
    {A B C D E K : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category K]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    [HasShift D ℤ] [HasShift E ℤ] [HasShift K ℤ]
    (F : A ⥤ B) (T : B ⥤ C) (G : C ⥤ D) (H : D ⥤ E) (U : E ⥤ K) (V : C ⥤ K)
    [F.CommShift ℤ] [T.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    [U.CommShift ℤ] [V.CommShift ℤ]
    (d : G ⋙ H ⋙ U ≅ V) [NatTrans.CommShift d.hom ℤ] :
    NatTrans.CommShift
      ((show (F ⋙ T ⋙ G ⋙ H) ⋙ U ≅ F ⋙ T ⋙ V from
        Functor.isoWhiskerLeft (F ⋙ T) d).hom) ℤ := by
  let c : (F ⋙ (T ⋙ G ⋙ H)) ⋙ U ≅ F ⋙ T ⋙ V :=
    Functor.associator F (T ⋙ G ⋙ H) U ≪≫
      Functor.isoWhiskerLeft F
        (Functor.associator T (G ⋙ H) U ≪≫
          Functor.isoWhiskerLeft T (Functor.associator G H U ≪≫ d))
  have hc : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c]
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  have heq :
      (show (F ⋙ T ⋙ G ⋙ H) ⋙ U ≅ F ⋙ T ⋙ V from
        Functor.isoWhiskerLeft (F ⋙ T) d).hom = c.hom := by
    ext X
    simp only [c, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.comp_obj, Category.id_comp]
  rw [heq]
  exact hc

private theorem scalar_underlying_unit_shift
    (l : ℕ) [Fact l.Prime] (n : ℕ) (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb X)] :
    NatTrans.CommShift (scalarUnderlyingUnit (cyclicMap l n) X) ℤ := by
  let adj := UniformizerSquareData.scalarAdjunction (cyclicMap l n) X
  have : adj.CommShift ℤ :=
    RootEndpointTranspose.ShiftHelpers.scalarAdjunction_commShift _ _
  have : NatTrans.CommShift adj.unit ℤ := inferInstance
  let R := Mod.comap (D := DiagonalAb X) (coefficientMap (cyclicMap l n) X)
  let U := Mod.forget (D := DiagonalAb X)
    (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)
  let T := derivedScalars (cyclicMap l n) X
  let η : U.mapDerivedCategory ⟶
      T ⋙ (Mod.forget (condensedRingObj
        (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) X)).mapDerivedCategory :=
    (Functor.leftUnitor U.mapDerivedCategory).inv ≫
      Functor.whiskerRight adj.unit U.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft T (Functor.mapDerivedCategoryCompIso R U).inv
  have hη : NatTrans.CommShift η ℤ := by
    dsimp only [η]
    infer_instance
  have heq : scalarUnderlyingUnit (cyclicMap l n) X = η := by
    ext Z
    simp only [scalarUnderlyingUnit, η, adj, T, R, U, UniformizerSquareData.scalarAdjunction,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.associator_hom_app, Iso.trans_hom,
      Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  rw [heq]
  exact hη

private theorem cyclic_augmentation_shift
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    NatTrans.CommShift (cyclicEvaluationAugmentation l Y n eW p) ℤ := by
  have := scalar_underlying_unit_shift l n (diagonalSurface Y)
  have hcompleted : NatTrans.CommShift (cyclicCompletedUnderlying l Y eW).hom ℤ := by
    let C := diagonalCompletedRestriction l (diagonalSurface Y)
    let U := diagonalForget l (diagonalSurface Y)
    let W := Mod.forget (D := DiagonalAb (diagonalSurface Y))
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) (diagonalSurface Y))
    have h1 : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso C U).inv ℤ :=
      inferInstance
    have h2 : NatTrans.CommShift
        (Functor.mapDerivedCategoryNatIso eW.underlying.symm).hom ℤ := inferInstance
    have h3 : NatTrans.CommShift (Functor.mapDerivedCategoryCompIso eW.F W).hom ℤ :=
      inferInstance
    dsimp only [cyclicCompletedUnderlying]
    simp only [Iso.trans_hom, Iso.symm_hom]
    exact NatTrans.CommShift.comp (Functor.mapDerivedCategoryCompIso C U).inv
      ((Functor.mapDerivedCategoryNatIso eW.underlying.symm).hom ≫
        (Functor.mapDerivedCategoryCompIso eW.F W).hom) ℤ
  let A := eW.F.mapDerivedCategory
  let T := derivedScalars (cyclicMap l n) (diagonalSurface Y)
  let G := p.eW.F.mapDerivedCategory
  let H := (canonicalFinitePadicRestriction l n (diagonalSurface Y)).mapDerivedCategory
  let U := (diagonalForget l (diagonalSurface Y)).mapDerivedCategory
  let V := (Mod.forget (D := DiagonalAb (diagonalSurface Y)) (condensedRingObj
    (Profinite.continuousMapRingObj (ZMod (l ^ (n + 1)))) (diagonalSurface Y))).mapDerivedCategory
  let d : G ⋙ H ⋙ U ≅ V :=
    Functor.isoWhiskerLeft G
      (Functor.mapDerivedCategoryCompIso
        (canonicalFinitePadicRestriction l n (diagonalSurface Y))
        (diagonalForget l (diagonalSurface Y))).symm ≪≫
      (Functor.mapDerivedCategoryCompIso p.eW.F
        (canonicalFinitePadicRestriction l n (diagonalSurface Y) ⋙
          diagonalForget l (diagonalSurface Y))).symm ≪≫
      Functor.mapDerivedCategoryNatIso (cyclicFiniteUnderlying l Y n p)
  have hd : NatTrans.CommShift d.hom ℤ := by
    dsimp only [d]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom]
    infer_instance
  have hevaluation : NatTrans.CommShift (cyclicEvaluationUnderlying l Y n eW p).hom ℤ := by
    run_tac structuralExact (← `(term| whisker_left_shift_compatibility A T G H U V d))
  dsimp only [cyclicEvaluationAugmentation]
  infer_instance

private theorem shifted_underlying_endpoint
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (F G : A ⥤ B) (U : B ⥤ C)
    [F.CommShift ℤ] [G.CommShift ℤ] [U.CommShift ℤ]
    (η : F ⋙ U ⟶ G ⋙ U) [NatTrans.CommShift η ℤ]
    (P : A) {N : B} (f : F.obj P ⟶ N) (g : G.obj P ⟶ N)
    (h : η.app P ≫ U.map g = U.map f) (j : ℤ) :
    η.app (P⟦j⟧) ≫ U.map ((G.commShiftIso j).hom.app P ≫ g⟦j⟧') =
      U.map ((F.commShiftIso j).hom.app P ≫ f⟦j⟧') := by
  apply (cancel_mono ((U.commShiftIso j).hom.app N)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [U.commShiftIso_hom_naturality g j, U.commShiftIso_hom_naturality f j]
  have hs := (η.shift_app_comm j P).symm
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [reassoc_of% hs]
  rw [← (shiftFunctor C j).map_comp, h]

private theorem single_augmentation_shift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (V : A ⥤ B) (U : B ⥤ C) [V.Additive] [U.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ]
    (η : V.mapDerivedCategory ⋙ U.mapDerivedCategory ⟶ T ⋙ U.mapDerivedCategory)
    [NatTrans.CommShift η ℤ] (P : A) (N : B) (h : V.obj P ⟶ N)
    (z : T.obj ((DerivedCategory.singleFunctor A 0).obj P) ⟶
      (DerivedCategory.singleFunctor B 0).obj N)
    (hz : η.app ((DerivedCategory.singleFunctor A 0).obj P) ≫ U.mapDerivedCategory.map z ≫
        (U.mapDerivedCategorySingleFunctor 0).hom.app N =
      U.mapDerivedCategory.map ((V.mapDerivedCategorySingleFunctor 0).hom.app P) ≫
        (U.mapDerivedCategorySingleFunctor 0).hom.app (V.obj P) ≫
        (DerivedCategory.singleFunctor C 0).map (U.map h)) (j : ℤ) :
    η.app (((DerivedCategory.singleFunctor A 0).obj P)⟦j⟧) ≫
        U.mapDerivedCategory.map ((T.commShiftIso j).hom.app _ ≫ z⟦j⟧') =
      U.mapDerivedCategory.map
        ((shifted_single_iso V P j).hom ≫
          ((DerivedCategory.singleFunctor B 0).map h)⟦j⟧') := by
  rw [shifted_single_iso_hom]
  simp only [Category.assoc]
  have h0 : η.app ((DerivedCategory.singleFunctor A 0).obj P) ≫
      U.mapDerivedCategory.map z = U.mapDerivedCategory.map
        ((V.mapDerivedCategorySingleFunctor 0).hom.app P ≫
          (DerivedCategory.singleFunctor B 0).map h) := by
    apply (cancel_mono ((U.mapDerivedCategorySingleFunctor 0).hom.app N)).1
    simp only [Functor.map_comp, Category.assoc]
    rw [hz]
    have hn := (U.mapDerivedCategorySingleFunctor 0).hom.naturality h
    dsimp only [Functor.comp_map] at hn
    exact congrArg (U.mapDerivedCategory.map
      ((V.mapDerivedCategorySingleFunctor 0).hom.app P) ≫ ·) hn.symm
  simpa only [Functor.map_comp, Category.assoc] using
    shifted_underlying_endpoint V.mapDerivedCategory T U.mapDerivedCategory η
      ((DerivedCategory.singleFunctor A 0).obj P)
      ((V.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor B 0).map h) z h0 j

private theorem normalized_endpoint_cancel
    {A B : Type*} [Category A] [Category B] (U : A ⥤ B)
    {X P Q N R Y T G : A} (cP : X ≅ P) (cH : T ≅ Q) (b : Y ≅ T)
    (ta : R ≅ Y) (e : G ≅ R) (unit : X ⟶ R) (target : G ⟶ N)
    (q : P ⟶ Q) (t : Q ⟶ N) (α : U.obj X ⟶ U.obj G)
    (path : X ⟶ Y) (hp : unit ≫ ta.hom = path)
    (hq : endpoint_path_equation path b cH cP q)
    (he : α ≫ U.map e.hom = U.map unit)
    (ha : α ≫ U.map target = U.map (cP.hom ≫ q ≫ t))
    (cancel : ∀ f g : Q ⟶ N, U.map (q ≫ f) = U.map (q ≫ g) → f = g) :
    b.inv ≫ ta.inv ≫ e.inv ≫ target = cH.hom ≫ t := by
  unfold endpoint_path_equation at hq
  rw [← hp] at hq
  simp only [Category.assoc] at hq
  apply (cancel_epi cH.inv).1
  apply cancel
  apply (cancel_epi (U.map cP.hom)).1
  simp only [← U.map_comp]
  have hq' : cP.hom ≫ q ≫ cH.inv = unit ≫ ta.hom ≫ b.hom := by
    rw [← reassoc_of% hq]
    simp only [Iso.hom_inv_id, Category.comp_id]
  rw [reassoc_of% hq']
  simp only [Iso.hom_inv_id_assoc]
  have he' : U.map (unit ≫ e.inv) = α := by
    rw [U.map_comp, ← he, Category.assoc, ← U.map_comp, Iso.hom_inv_id,
      U.map_id, Category.comp_id]
  rw [← Category.assoc, U.map_comp, he', ha]
  simp only [Iso.inv_hom_id_assoc]

private theorem shifted_composition_endpoint
    {C D K : Type*} [Category C] [Category D] [Category K]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift K ℤ]
    (F : C ⥤ D) (G : D ⥤ K) [F.CommShift ℤ] [G.CommShift ℤ]
    {M : C} {N : D} {P : K} (f : F.obj M ⟶ N) (g : G.obj N ⟶ P) (k : ℤ) :
    G.map ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (G.commShiftIso k).hom.app N ≫ g⟦k⟧' =
      ((F ⋙ G).commShiftIso k).hom.app M ≫ (G.map f ≫ g)⟦k⟧' := by
  simp only [Functor.map_comp, Functor.commShiftIso_comp_hom_app,
    (shiftFunctor K k).map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]

private theorem commShift_associator_endpoint
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] (X : A) (j : ℤ) :
    (((F ⋙ G) ⋙ H).commShiftIso j).hom.app X =
      ((F ⋙ (G ⋙ H)).commShiftIso j).hom.app X := by
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rfl

private theorem generic_target_shift_endpoint
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : A ⥤ B) (T : DerivedCategory B ⥤ DerivedCategory C)
    (G : C ⥤ D) (H : D ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [T.CommShift ℤ] (n : ℕ) {P : A} {L : B} {N : C} {Q : D}
    (i : F.obj P ≅ L)
    (j : T.obj ((DerivedCategory.singleFunctor B 0).obj L) ⟶
      (DerivedCategory.singleFunctor C 0).obj N) (q : G.obj N ≅ Q) :
    completedFunctorTarget F (T ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory) n i
        (threeFunctorTarget T G H n ((T.commShiftIso (n : ℤ)).hom.app _ ≫ j⟦(n : ℤ)⟧') q) =
      ((F.mapDerivedCategory ⋙ T ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).commShiftIso
        (n : ℤ)).hom.app _ ≫
        (exactRealizationTargetZero F T G H i.hom j q.hom)⟦(n : ℤ)⟧' := by
  unfold completedFunctorTarget threeFunctorTarget exactRealizationTargetZero
  simp only [← Functor.map_comp]
  erw [shifted_composition_endpoint]
  erw [shifted_composition_endpoint]
  erw [shifted_composition_endpoint]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  erw [commShift_associator_endpoint T G.mapDerivedCategory H.mapDerivedCategory]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Category.assoc]

private theorem cyclic_target_shift
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (p : CyclicCartierFrame l Y n) :
    cyclicEvaluationTarget l Y n eW p =
      ((cyclicEvaluationFunctor l Y n eW p).commShiftIso (2 : ℤ)).hom.app _ ≫
        (cyclicEvaluationTargetZero l Y n eW p)⟦(2 : ℤ)⟧' := by
  run_tac structuralExact (← `(term| generic_target_shift_endpoint eW.F
    (derivedScalars (cyclicMap l n) (diagonalSurface Y)) p.eW.F
    (canonicalFinitePadicRestriction l n (diagonalSurface Y))
    2 eW.lineIso p.line.iso.hom p.lineEndpoint.iso))

private theorem normalized_cyclic_augmentation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eW : CompletedRealization l (diagonalSurface Y)) (n : ℕ)
    (p : CyclicCartierFrame l Y n) (H : DiagonalSystems l (diagonalSurface Y)) [HasLimit H]
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (t : H.obj (op n) ≅ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (ht : DiagonalTrace.FiniteRootNormalization l Y hY H roots n t) :
    (cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedCodomain l Y) ≫
        (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
          (cyclicEvaluationTarget l Y n eW p) =
      (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
        ((shifted_single_iso (diagonalCompletedRestriction l (diagonalSurface Y))
          (Scheme.purTwistZlModule (diagonalSurface Y) l) (2 : ℤ)).hom ≫
          ((DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).map
            (t0.hom ≫ limit.π H (op n) ≫ t.hom))⟦(2 : ℤ)⟧') := by
  let U := diagonalForget l (diagonalSurface Y)
  let V := diagonalCompletedRestriction l (diagonalSurface Y)
  let P := Scheme.purTwistZlModule (diagonalSurface Y) l
  have hz := cyclicEvaluationAugmentation_zeroTarget l Y n eW p
  rw [ordinary_cyclic_root_projection l Y hY eW n p H roots t0 ht0 t ht] at hz
  have hshift := cyclic_augmentation_shift l Y n eW p
  rw [cyclic_target_shift]
  run_tac structuralExact (← `(term| single_augmentation_shift V U
    (cyclicEvaluationFunctor l Y n eW p) (cyclicEvaluationAugmentation l Y n eW p)
    P _ (t0.hom ≫ limit.π H (op n) ≫ t.hom)
    (cyclicEvaluationTargetZero l Y n eW p) hz (2 : ℤ)))

/-- The shifted root endpoint equation for a quotient-unit-preserving comparison.
This is the target half of the normalized endpoint argument.

Source: coefficient changes (1), root endpoint; diagonal limit (3), normalized
root cone.
(blueprint: lem-diagonal-cyclic-quotient-normalized-target-endpoint).

Proof: the derived-limit unit composed with the n-th projection commutes with
shifts by its complex normalization, so hta identifies the shifted target-limit map
at n with the shifted single of t0.hom ≫ limit.π H (op n). ht0 identifies the
underlying arrow of t0 with the root limit comparison. IntegralRoots uniqueness
identifies the two integral-root maps; the finite root maps coincide because their
inclusions into the units sheaf agree and that inclusion is monic. With
p.lineEndpoint.normalization and ht, the ordinary underlying arrow of the
degree-zero target is the n-th root projection transported by t0 and t. The proved
degree-zero augmentation calculation (lem-diagonal-cyclic-augmentation-zero) and
shift compatibility of the scalar unit and the exact-functor comparisons transport
this to degree two. The root-tower projection is locally surjective, hence epic,
and faithful scalar forgetting makes limit.π H (op n) epic. Full faithfulness of
the single embedding and of the shift cancel this epimorphism between shifted
single objects after forgetting; the quotient-unit square he then gives the
displayed equation. Global faithfulness of derived scalar forgetting is not used. -/
theorem diagonalCyclicQuotient_normalizedTargetEndpoint
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (sourceIso : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (source_normalization :
      HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ sourceIso.hom.hom)
        ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
          (eP.underlying.inv.app (SheafOfModules.unit
            (Scheme.purTwistRing (ProjectiveLine Y)
              (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫
            eP.unitIso.hom.hom)))
 :
  letI : HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.ab (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.abSystems (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.completed (ℓ := l) (X := diagonalSurface Y)
  letI : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted l (diagonalSurface Y)) :=
    DiagonalTraceLocalizations.completedSystems (ℓ := l) (X := diagonalSurface Y)
  ∀ (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (M : DiagonalCompletedReduction l (diagonalSurface Y))
    (s0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (t0 : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (hs0 : DiagonalTrace.SupportedSourceConeNormalization l Y D.ordinary s0)
    (ht0 : HEq ((diagonalForget l (diagonalSurface Y)).map t0.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (n : ℕ) (p : CyclicCartierFrame l Y n)
    (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))))
    (t : H.obj (op n) ≅ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    (hs : DiagonalSourceNormalization l Y D.ordinary n s)
    (ht : DiagonalTrace.FiniteRootNormalization l Y hY H roots n t),
    let F : DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
      cyclicDiscreteRestriction l (diagonalSurface Y)
    let Rn : DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y)) :=
      cyclicCompletedQuotient l (diagonalSurface Y) M n
    let En : DerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y)) ⥤
        DerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y)) :=
      ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let K := D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))
    let J := D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)
    ∀ (sa : F.obj (Rn.obj (diagonalCompletedDomain l Y)) ≅ En.obj K)
      (ta : F.obj (Rn.obj (diagonalCompletedCodomain l Y)) ≅ En.obj J),
      F.map ((M.unit n).app (diagonalCompletedDomain l Y)) ≫ sa.hom =
        diagonalSourceLimitMap l Y D a L s0 ≫ (L.projection n).app K →
      F.map ((M.unit n).app (diagonalCompletedCodomain l Y)) ≫ ta.hom =
        diagonalTargetLimitMap l Y D H b L t0 ≫
            (L.projection n).app J →
      ∀ (e : cyclicEvaluationFunctor l Y n eW p ≅ Rn ⋙ F),
        (∀ X : DerivedCategory (DiagonalCompleted l (diagonalSurface Y)),
          (cyclicEvaluationAugmentation l Y n eW p).app X ≫
              (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map (e.hom.app X) =
            (diagonalForget l (diagonalSurface Y)).mapDerivedCategory.map
              (F.map ((M.unit n).app X))) →
        En.map b.inv ≫ ta.inv ≫ e.inv.app (diagonalCompletedCodomain l Y) ≫
            cyclicEvaluationTarget l Y n eW p =
          (En.commShiftIso (2 : ℤ)).hom.app _ ≫
            ((((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
              (op n)).mapDerivedCategorySingleFunctor 0).hom.app H)⟦(2 : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor _ 0).map t.hom)⟦(2 : ℤ)⟧' := by
  intro D H roots a b L M s0 t0 hs0 ht0 n p s t hs ht
  clear source_normalization hs0 hs
  dsimp (config := { proj := false }) only
  intro sa ta hsa hta e he
  simp only [cyclic_discrete_map] at hta he
  have : HasLimit H := inferInstance
  let U := diagonalForget l (diagonalSurface Y)
  let P := Scheme.purTwistZlModule (diagonalSurface Y) l
  let V := diagonalCompletedRestriction l (diagonalSurface Y)
  let E := (evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj (op n)
  let S := DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0
  let q := t0.hom ≫ limit.π H (op n)
  have : U.Faithful := diagonalForget_faithful l _
  have : Epi (limit.π H (op n)) :=
    root_system_limit_projection_epi l (diagonalSurface Y)
      (by simpa using diagonalSurface_power_unit l Y hY 0) H roots n
  have : Epi q := by dsimp only [q]; infer_instance
  let cH := shifted_single_iso E H (2 : ℤ)
  let cP := shifted_single_iso V P (2 : ℤ)
  let f := E.mapDerivedCategory.map b.inv ≫ ta.inv ≫
    e.inv.app (diagonalCompletedCodomain l Y) ≫ cyclicEvaluationTarget l Y n eW p
  let g := cH.hom ≫ (S.map t.hom)⟦(2 : ℤ)⟧'
  suffices f = g by
    have hh := this
    simp only [f, g, cH, shifted_single_iso_hom, Category.assoc] at hh
    run_tac structuralExact (← `(term| hh))
  rw [target_limit_map_eq] at hta
  have hq := shifted_limit_projection V L P H _ t0 b n
  have haug :
      (cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedCodomain l Y) ≫
        U.mapDerivedCategory.map (cyclicEvaluationTarget l Y n eW p) =
      U.mapDerivedCategory.map (cP.hom ≫ (S.map (q ≫ t.hom))⟦(2 : ℤ)⟧') := by
    dsimp only [cP, q]
    try simp only [Category.assoc]
    run_tac structuralExact (← `(term|
      normalized_cyclic_augmentation l Y hY eW n p H roots t0 ht0 t ht))
  have haug' := haug
  simp only [S.map_comp, (shiftFunctor _ (2 : ℤ)).map_comp] at haug'
  dsimp only [f, g]
  run_tac structuralExact (← `(term| normalized_endpoint_cancel U.mapDerivedCategory cP cH
    (E.mapDerivedCategory.mapIso b) ta
    (e.app (diagonalCompletedCodomain l Y))
    (V.mapDerivedCategory.map ((M.unit n).app (diagonalCompletedCodomain l Y)))
    (cyclicEvaluationTarget l Y n eW p) ((S.map q)⟦(2 : ℤ)⟧')
    ((S.map t.hom)⟦(2 : ℤ)⟧')
    ((cyclicEvaluationAugmentation l Y n eW p).app (diagonalCompletedCodomain l Y))
    (diagonalShiftedSingleLimitComparison V L P H _ t0 b ≫ (L.projection n).app _)
    hta hq
    (he (diagonalCompletedCodomain l Y))
    haug'
    (fun f g h ↦ by
      run_tac structuralExact (← `(term| shifted_single_cancel_epi U q (2 : ℤ) f g h)))))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
