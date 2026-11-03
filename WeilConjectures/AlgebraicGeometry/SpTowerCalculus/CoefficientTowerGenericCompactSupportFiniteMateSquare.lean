/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions
public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedProperTransition
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedOpenTransition
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Finite proper and open factors of the compact-support transition mate

The generic ideal-quotient coordinates are compared with the normalized tower
coordinates before the two finite equations are pasted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus
open AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

def genericCompactSupportRho (T : Scheme.{u})
    (C : SpTowerShriek.D l E T) {m n : ℕ} (v : m ≤ n) :
    (scalarExtensionFunctor (quotient l E v) T).obj
        ((SpTowerShriek.Ev l E T n).obj C) ⟶
      (SpTowerShriek.Ev l E T m).obj C :=
  ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) (quotient l E v))).homEquiv _ _).symm
      ((genericIntrinsicTransitions l E T v).app C)
def genericCompactSupportPushComparison
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) (n : ℕ) :
    (SpTowerShriek.Ev l E Y n).obj ((SpTowerShriek.F l E b o c).obj K) ⟶
      (directImageConstantPush (SpTowerShriek.R l E n) c.g).obj
        ((SpTowerShriek.Ev l E c.Z n).obj
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) :=
  (Functor.isoWhiskerLeft
      (SpTowerShriek.openD l E b (o.openOp c.i))
      ((o.geometry c.g).pushEvaluation n)).hom.app K
def genericCompactSupportOpenComparison
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) (n : ℕ) :
    (SpTowerShriek.Ev l E c.Z n).obj
        ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) ⟶
      (sfIntrinsicDerivedOpen (SpTowerShriek.R l E n) c.i).obj
        ((SpTowerShriek.Ev l E X n).obj K) :=
  (SpTowerShriek.openEvaluation l E b (o.openOp c.i) n).hom.app K

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian scalarExtensionFunctor

-- The coordinate transport is proved locally from public adjoint-uniqueness laws.
private theorem coordinate_transpose
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (q : R ≅ R')
    {X : C} {Y : D} (t : X ⟶ R.obj Y) :
    b.homEquiv _ _
        ((a.leftAdjointUniq (b.ofNatIsoRight q.symm)).inv.app X ≫
          (a.homEquiv _ _).symm t) = t ≫ q.hom.app Y := by
  have h := leftAdjointUniq_homEquiv_comp (b.ofNatIsoRight q.symm) a X Y
    ((a.homEquiv _ _).symm t)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  apply (cancel_mono (q.inv.app Y)).mp
  simpa only [Adjunction.leftAdjointUniq_inv_app, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id] using h

private theorem coordinate_mate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (q : R ≅ R')
    {X : C} {Y : D} (t : X ⟶ R.obj Y) :
    (a.leftAdjointUniq (b.ofNatIsoRight q.symm)).inv.app X ≫
        (a.homEquiv _ _).symm t =
      (b.homEquiv _ _).symm (t ≫ q.hom.app Y) := by
  apply (b.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  exact coordinate_transpose a b q t

private theorem coordinateReduction_mate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (q : R ≅ R')
    {X : C} {Y : D} (t : X ⟶ R.obj Y) :
    coordinateReduction (a.leftAdjointUniq (b.ofNatIsoRight q.symm))
        ((a.homEquiv _ _).symm t) =
      (b.homEquiv _ _).symm (t ≫ q.hom.app Y) :=
  coordinate_mate a b q t

private theorem transported_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : C ⥤ E} {R R' : E ⥤ D}
    (t : F ⟶ G ⋙ R) (q : R ≅ R') (X : C) :
    (t ≫ Functor.whiskerLeft G q.hom).app X = t.app X ≫ q.hom.app (G.obj X) := by
  rfl

private def nativeStrictTransition (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.Ev l E T n ⟶
      SpTowerShriek.Ev l E T m ⋙ scalarRestriction (quotientMap l E h) T :=
  SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h ≫
    Functor.whiskerLeft _ (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
      (coefficientMap_eq l E T h))).hom

private theorem derive_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    (Functor.mapDerivedCategoryNatIso (eqToIso h)).hom =
      (eqToIso (by cases h; rfl : F.mapDerivedCategory = G.mapDerivedCategory)).hom := by
  cases h
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem quotientMap_eq_quotient {m n : ℕ} (h : m ≤ n) :
    quotientMap l E h = quotient l E h := by
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u} :=
    { obj := fun n ↦ CommRingCat.of (SpTowerShriek.R l E n.unop)
      map := fun f ↦ CommRingCat.ofHom (quotient l E (leOfHom f.unop))
      map_id := by intro n; ext x; rfl
      map_comp := by intro i j k f g; ext x; rfl }
  let t : Functor.ofOpSequence
      (X := fun n ↦ CommRingCat.of (SpTowerShriek.R l E n))
      (fun n ↦ CommRingCat.ofHom
        (Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1))) ⟶ Q := by
    refine NatTrans.ofOpSequence (fun n ↦ 𝟙 _) ?_
    intro n
    simp only [Functor.ofOpSequence_map_homOfLE_succ, Category.comp_id]
    ext x
    rfl
  have ht := t.naturality (homOfLE h).op
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ CommRingCat.ofHom (quotient l E h) at ht
  simp only [Category.comp_id, Category.id_comp] at ht
  exact congrArg CommRingCat.Hom.hom ht

-- Keeping the map together with its equality proof makes coordinate transport
-- ordinary equality transport of data, without rewriting dependent proof arguments.
private abbrev QuotientCoordinates {m n : ℕ} (v : m ≤ n) :=
  {q : SpTowerShriek.R l E n →+* SpTowerShriek.R l E m //
    ∀ T : Scheme.{u},
      SemilinearSections.coefficientMap (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) v =
        proEtaleConstantRingMap (T := T) q}

private def normalizedCoordinates {m n : ℕ} (v : m ≤ n) : QuotientCoordinates l E v :=
  ⟨quotientMap l E v, fun T ↦ coefficientMap_eq l E T v⟩

private def genericCoordinates {m n : ℕ} (v : m ≤ n) : QuotientCoordinates l E v :=
  ⟨quotient l E v, fun T ↦ genericCoefficientMap_eq l E T v⟩

private theorem coordinates_eq {m n : ℕ} (v : m ≤ n) :
    normalizedCoordinates l E v = genericCoordinates l E v := by
  apply Subtype.ext
  exact quotientMap_eq_quotient l E v

private def coordinateTransition {m n : ℕ} {v : m ≤ n}
    (p : QuotientCoordinates l E v) (T : Scheme.{u}) :
    SpTowerShriek.Ev l E T n ⟶
      SpTowerShriek.Ev l E T m ⋙ scalarRestriction p.val T :=
  SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) v ≫
    Functor.whiskerLeft _ (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
      (p.property T))).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private def coordinateRho {m n : ℕ} {v : m ≤ n}
    (p : QuotientCoordinates l E v) (T : Scheme.{u}) (M : SpTowerShriek.D l E T) :
    (scalarExtensionFunctor p.val T).obj ((SpTowerShriek.Ev l E T n).obj M) ⟶
      (SpTowerShriek.Ev l E T m).obj M :=
  ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) p.val)).homEquiv _ _).symm
      ((coordinateTransition l E p T).app M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem coordinateRho_eq {m n : ℕ} {v : m ≤ n}
    (p : QuotientCoordinates l E v) (T : Scheme.{u}) (M : SpTowerShriek.D l E T) :
    coordinateRho l E p T M =
      ((proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) p.val)).homEquiv _ _).symm
          ((coordinateTransition l E p T).app M) := by
  rfl

attribute [local irreducible] quotientMap quotient

-- Explicit proof-irrelevant instance transport, as in the normalized open proof.
-- Each conversion is a kernel-checked heterogeneous congruence, avoiding expansion
-- of the localization construction while comparing its instance presentations.
section InstanceTransport
open Lean Meta Elab Tactic CategoryTheory

private theorem instanceProofsHEq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

private meta def nameCoordinateProjection (e : Expr) : MetaM Expr := do
  if e.getAppFn.isConstOf ``ReflQuiver.toQuiver ||
      e.getAppFn.isConstOf ``Subtype.val then
    return ← withDefault <| whnf e
  if e.getAppFn.isConstOf ``Abelian.toPreadditive then
    return ← withDefault <| whnf e
  let .proj n i f := e.getAppFn | return e
  if n == ``Abelian || n == ``ReflQuiver || n == ``Subtype then
    return ← withDefault <| whnf e
  let name := if n == ``CategoryTheory.Functor then
      if i == 0 then ``Functor.obj else ``Functor.map
    else if n == ``Iso then if i == 0 then ``Iso.hom else ``Iso.inv
    else if n == ``NatTrans && i == 0 then ``NatTrans.app
    else if n == ``ObjectProperty.FullSubcategory && i == 0 then
      ``ObjectProperty.FullSubcategory.obj
    else if n == ``InducedCategory.Hom && i == 0 then ``InducedCategory.Hom.hom
    else Name.anonymous
  if name.isAnonymous then return e
  let ty ← inferType f
  let ty ← if ty.getAppFn.isConstOf n then pure ty else whnf ty
  let p := mkAppN (.const name ty.getAppFn.constLevels!) (ty.getAppArgs.push f)
  return mkAppN p e.getAppArgs

private meta def reduceCoordinateObject : Nat → Expr → MetaM Expr
  | 0, e => pure e
  | fuel + 1, e => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Functor.obj && args.size == 6 then
      let f := args[4]!
      let h := f.getAppFn
      if h.isConstOf ``Functor.comp || h.isConstOf ``ObjectProperty.ι ||
          h.isConstOf ``ObjectProperty.lift || h.isConstOf ``Functor.id then
        if let some f' ← withDefault <| unfoldDefinition? f then
          let e' ← whnfCore (mkApp (.proj ``CategoryTheory.Functor 0 f') args[5]!)
          return ← reduceCoordinateObject fuel (← nameCoordinateProjection e')
    if fn.isConstOf ``ObjectProperty.FullSubcategory.obj then
      let arg := args.back!
      let arg' ← reduceCoordinateObject fuel (← nameCoordinateProjection arg)
      if arg' != arg then
        let e' := mkAppN fn (args.set! (args.size - 1) arg')
        if let some e'' ← withDefault <| unfoldDefinition? e' then
          return ← reduceCoordinateObject fuel (← whnfCore e'')
      if let some e' ← Lean.Expr.reduceProjStruct? e then return e'
    return e

private meta def instanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (norm : Bool) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    let entries ← cache.get
    if let some h := entries[(a, b)]? then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``instanceProofsHEq #[a, b]
      if let .letE _ _ val body _ := a then
        return ← instanceCongr cache norm fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← instanceCongr cache norm fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← instanceCongr cache norm fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← instanceCongr cache norm fuel a val
      if let .lam name ty body info := a then
        if let .lam _ ty' body' _ := b then
          if !body.hasLooseBVars && !body'.hasLooseBVars then
            let a' ← mkAppM ``Function.const #[ty, body]
            let b' ← mkAppM ``Function.const #[ty', body']
            return ← instanceCongr cache norm fuel a' b'
          unless ty == ty' do
            throwError "function domains differ: {ty} versus {ty'}"
          return ← withLocalDecl name info ty fun x => do
            let h ← instanceCongr cache norm fuel
              (body.instantiate1 x) (body'.instantiate1 x)
            let h ← mkAppM ``eq_of_heq #[h]
            let pf ← mkAppM ``funext #[← mkLambdaFVars #[x] h]
            mkAppM ``heq_of_eq #[pf]
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← instanceCongr cache norm fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← instanceCongr cache norm fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if norm then
        let a' ← nameCoordinateProjection a
        let b' ← nameCoordinateProjection b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
        let a' ← reduceCoordinateObject 30 a
        let b' ← reduceCoordinateObject 30 b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
      if af != bf then
        for d in (← getLCtx) do
          let dt ← withReducible <| whnf (← instantiateMVars d.type)
          let ht := dt.getAppArgs
          unless dt.getAppFn.isConstOf ``HEq && ht.size == 4 do continue
          let (a', b', h) ←
            if ht[1]!.getAppFn == af && ht[3]!.getAppFn == bf then
              pure (ht[1]!, ht[3]!, d.toExpr)
            else if ht[3]!.getAppFn == af && ht[1]!.getAppFn == bf then
              pure (ht[3]!, ht[1]!, ← mkAppM ``HEq.symm #[d.toExpr])
            else continue
          let branchCache ← IO.mkRef (← cache.get)
          let pf? ← observing? do
            let h₁ ← instanceCongr branchCache norm fuel a a'
            let h₂ ← instanceCongr branchCache norm fuel b' b
            mkAppM ``HEq.trans #[h₁, ← mkAppM ``HEq.trans #[h, h₂]]
          if let some pf := pf? then
            cache.set (← branchCache.get)
            return pf
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let cp ← mkAuxTheorem ct.type ct.proof (zetaDelta := true)
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← try instanceCongr cache norm fuel aa[i]! bb[i]!
            catch ex =>
              throwError "{ex.toMessageData}\nIn {af}, argument {i}"
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN cp ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af.isConstOf ``quotientMap && bf.isConstOf ``quotient then
        let aa := a.getAppArgs
        let q ← mkAppM ``quotientMap_eq_quotient #[aa[0]!, aa[2]!, aa.back!]
        return ← mkAppM ``heq_of_eq #[q]
      if bf.isConstOf ``quotientMap && af.isConstOf ``quotient then
        let bb := b.getAppArgs
        let q ← mkAppM ``quotientMap_eq_quotient #[bb[0]!, bb[2]!, bb.back!]
        return ← mkAppM ``heq_of_eq #[← mkAppM ``Eq.symm #[q]]
      if af != bf then
        if af.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory ||
            af.isConstOf ``SemilinearSections.hasDerived ||
            af.isConstOf ``SemilinearSections.moduleAbelian ||
            af.isConstOf ``proEtaleCoefficientRestrictScalars ||
            af.isConstOf ``proEtaleRingRestrictScalars ||
            af.isConstOf ``SemilinearSections.res ||
            af.isConstOf ``SemilinearSections.resD ||
            af.isConstOf ``scalarRestriction ||
            af.isConstOf ``SpTowerShriek.Ev ||
            af.isConstOf ``SpTowerShriek.ev ||
            af.isConstOf ``SemilinearSections.e ||
            af.isConstOf ``SpTowerShriek.openD ||
            af.isConstOf ``SpTowerShriek.push ||
            af.isConstOf ``SpTowerShriek.openEvaluation ||
            af.isConstOf ``sfIntrinsicDerivedOpen ||
            af.isConstOf ``Functor.mapDerivedCategorySquareIso ||
            af.isConstOf ``proEtaleConstantRingMap ||
            af.isConstOf ``ProjectionRestriction.derived ||
            af.isConstOf ``ProjectionRestriction.Mod ||
            af.isConstOf ``ProjectionRestriction.Der ||
            af.isConstOf ``SemilinearSections.ScalarData.T ||
            af.isConstOf ``AlgebraicGeometry.ProEtale.scalarExtensionFunctor ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleDerivedCategory ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules ||
            af.isConstOf ``ringedSiteModules ||
            af.isConstOf ``SemilinearSections.ring ||
            af.isConstOf ``SheafOfModules.derivedChangeRingIndependentCoefficients ||
            af.isConstOf ``SpTowerShriek.B ||
            af.isConstOf ``SpTowerShriek.S ||
            af.isConstOf ``SpTowerShriek.D ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleConstantRing ||
            af.isConstOf ``nativeStrictTransition ||
            af.isConstOf ``coordinateTransition ||
            af.isConstOf ``normalizedCoordinates ||
            af.isConstOf ``genericCoordinates ||
            af.isConstOf ``genericCompactSupportRho ||
            af.isConstOf ``inferInstance ||
            af.isConstOf ``AlgebraicGeometry.Scheme.reductionModules ||
            af.isConstOf ``AlgebraicGeometry.Scheme.reductionModuleRing ||
            af.isConstOf ``scalarExtension ||
            af.isConstOf ``directImageScalarExtension ||
            af.isConstOf ``directImageConstantPush ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingDerivedDirectImage ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleConstantRingPushforward ||
            af.isConstOf ``SemilinearSections.Systems ||
            af.isConstOf ``SemilinearSections.DS ||
            af.isConstOf ``SemilinearSections.D ||
            af.isConstOf ``SemilinearSections.Mod ||
            af.isConstOf ``SheafOfModules.instPreadditive then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory ||
            bf.isConstOf ``SemilinearSections.hasDerived ||
            bf.isConstOf ``SemilinearSections.moduleAbelian ||
            bf.isConstOf ``proEtaleCoefficientRestrictScalars ||
            bf.isConstOf ``proEtaleRingRestrictScalars ||
            bf.isConstOf ``SemilinearSections.res ||
            bf.isConstOf ``SemilinearSections.resD ||
            bf.isConstOf ``scalarRestriction ||
            bf.isConstOf ``SpTowerShriek.Ev ||
            bf.isConstOf ``SpTowerShriek.ev ||
            bf.isConstOf ``SemilinearSections.e ||
            bf.isConstOf ``SpTowerShriek.openD ||
            bf.isConstOf ``SpTowerShriek.push ||
            bf.isConstOf ``SpTowerShriek.openEvaluation ||
            bf.isConstOf ``sfIntrinsicDerivedOpen ||
            bf.isConstOf ``Functor.mapDerivedCategorySquareIso ||
            bf.isConstOf ``proEtaleConstantRingMap ||
            bf.isConstOf ``ProjectionRestriction.derived ||
            bf.isConstOf ``ProjectionRestriction.Mod ||
            bf.isConstOf ``ProjectionRestriction.Der ||
            bf.isConstOf ``SemilinearSections.ScalarData.T ||
            bf.isConstOf ``AlgebraicGeometry.ProEtale.scalarExtensionFunctor ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleDerivedCategory ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules ||
            bf.isConstOf ``ringedSiteModules ||
            bf.isConstOf ``SemilinearSections.ring ||
            bf.isConstOf ``SheafOfModules.derivedChangeRingIndependentCoefficients ||
            bf.isConstOf ``SpTowerShriek.B ||
            bf.isConstOf ``SpTowerShriek.S ||
            bf.isConstOf ``SpTowerShriek.D ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleConstantRing ||
            bf.isConstOf ``nativeStrictTransition ||
            bf.isConstOf ``coordinateTransition ||
            bf.isConstOf ``normalizedCoordinates ||
            bf.isConstOf ``genericCoordinates ||
            bf.isConstOf ``genericCompactSupportRho ||
            bf.isConstOf ``inferInstance ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModules ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModuleRing ||
            bf.isConstOf ``scalarExtension ||
            bf.isConstOf ``directImageScalarExtension ||
            bf.isConstOf ``directImageConstantPush ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingDerivedDirectImage ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleConstantRingPushforward ||
            bf.isConstOf ``SemilinearSections.Systems ||
            bf.isConstOf ``SemilinearSections.DS ||
            bf.isConstOf ``SemilinearSections.D ||
            bf.isConstOf ``SemilinearSections.Mod ||
            bf.isConstOf ``SheafOfModules.instPreadditive then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache norm fuel a b'
      throwError "unmatched instance data: {a} versus {b}"
    cache.modify (·.insert (a, b) h)
    return h

private meta def transportInstances (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    let q ← instanceCongr cache true 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
private meta def closeHEq : TacticM Unit := withMainContext do
  let t ← withReducible <| whnf (← instantiateMVars (← getMainTarget))
  let args := t.getAppArgs
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  if t.getAppFn.isConstOf ``HEq then
    let pf ← instanceCongr cache true 500 args[1]! args[3]!
    (← getMainGoal).assign pf
  else if t.getAppFn.isConstOf ``Eq then
    let h ← instanceCongr cache true 500 args[1]! args[2]!
    (← getMainGoal).assign (← mkAppM ``eq_of_heq #[h])
  else throwError "expected equality: {t}"

end InstanceTransport

private theorem scalarCoordinates_eq (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    scalarCoordinates l E b T h =
      ((b.calculus T).scalar h).adjunction.leftAdjointUniq
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) (quotientMap l E h))).ofNatIsoRight
          (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
            (coefficientMap_eq l E T h))).symm) := by
  unfold scalarCoordinates
  rfl

private theorem reduction_eq (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E T) :
    SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) M =
      (((b.calculus T).scalar h).adjunction.homEquiv _ _).symm
        ((SemilinearSections.derivedTransition (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M) := by
  rfl

private theorem nativeStrictTransition_app (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (M : SpTowerShriek.D l E T) :
    (nativeStrictTransition l E T h).app M =
      (SemilinearSections.derivedTransition (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M ≫
      (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
        (coefficientMap_eq l E T h))).hom.app ((SpTowerShriek.Ev l E T m).obj M) := by
  have htransport := transported_app
    (G := SpTowerShriek.Ev l E T m)
    (SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ)
      (coefficientMap_eq l E T h))) M
  dsimp only [nativeStrictTransition]
  run_tac transportInstances `htransport

set_option maxHeartbeats 1000000 in
-- Explicit derived-category coordinate congruences need a larger elaboration budget.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rho_eq_mate (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E T) :
    rho l E b T h M =
      ((proEtaleRingDerivedExtensionAdjunction
        (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _).symm
          ((nativeStrictTransition l E T h).app M) := by
  rw [nativeStrictTransition_app]
  have ht := coordinateReduction_mate ((b.calculus T).scalar h).adjunction
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h)))
    (eqToIso (congrArg (fun φ ↦ SemilinearSections.resD φ) (coefficientMap_eq l E T h)))
    ((SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M)
  simp only [rho, scalarCoordinates_eq, reduction_eq]
  run_tac transportInstances `ht

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rho_heq_coordinates (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n) (M : SpTowerShriek.D l E T) :
    HEq (rho l E b T v M)
      (coordinateRho l E (normalizedCoordinates l E v) T M) := by
  have hn := heq_of_eq (rho_eq_mate l E b T v M)
  have hp := heq_of_eq (coordinateRho_eq l E (normalizedCoordinates l E v) T M)
  refine HEq.trans hn (HEq.trans ?_ (HEq.symm hp))
  run_tac closeHEq

private theorem genericTransition_eq_coordinates (T : Scheme.{u})
    {m n : ℕ} (v : m ≤ n) :
    genericIntrinsicTransitions l E T v =
      coordinateTransition l E (genericCoordinates l E v) T := by
  simp only [genericIntrinsicTransitions, coordinateTransition, genericCoordinates,
    derive_transport]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem genericRho_heq_coordinates (T : Scheme.{u})
    {m n : ℕ} (v : m ≤ n) (M : SpTowerShriek.D l E T) :
    HEq (genericCompactSupportRho l E T M v)
      (coordinateRho l E (genericCoordinates l E v) T M) := by
  have hp := heq_of_eq (coordinateRho_eq l E (genericCoordinates l E v) T M)
  refine HEq.trans ?_ (HEq.symm hp)
  have hT := heq_of_eq (genericTransition_eq_coordinates l E T v)
  run_tac closeHEq

private theorem pushComparison_eq
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) (n : ℕ) :
    genericCompactSupportPushComparison l E b o c K n =
      ((o.geometry c.g).pushEvaluation n).hom.app
        ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) := by
  rfl

private theorem map_open_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ C) (Q : B ⥤ D) (S : A ⥤ B) (T : C ⥤ D)
    (gamma : P ⋙ T ⟶ S ⋙ Q)
    {M N : A} {L L' : B} (i : M ⟶ N) (j : L ⟶ L')
    (r : S.obj M ⟶ L) (s : S.obj N ⟶ L')
    (h : r ≫ j = S.map i ≫ s) :
    gamma.app M ≫ Q.map (r ≫ j) =
      T.map (P.map i) ≫ gamma.app N ≫ Q.map s := by
  have hn := gamma.naturality i
  dsimp only [Functor.comp_map] at hn
  rw [h, Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]

set_option maxHeartbeats 1000000 in
-- Explicit derived-category coordinate congruences need a larger elaboration budget.
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The finite proper square for the constant-ring compact-support mate.
This is the proper factor before the open comparison is pasted; it is strictly
weaker than the generic transition because it mentions only the push comparison.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI, 0D6D.
(blueprint: lem-sp-tower-generic-compact-support-finite-proper-square).
Proof: transpose the normalized proper transition through the constant scalar
adjunction and evaluate the push comparison. -/
theorem generic_compactSupport_finiteProperSquare
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n) :
    genericCompactSupportRho l E Y ((SpTowerShriek.F l E b o c).obj K) v ≫
      genericCompactSupportPushComparison l E b o c K m =
    (directImageScalarExtension (quotient l E v) Y).map
        (genericCompactSupportPushComparison l E b o c K n) ≫
      (directImageScalarComparison (quotient l E v) c.g).app
        ((SpTowerShriek.Ev l E c.Z n).obj
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
      (directImageConstantPush (SpTowerShriek.R l E m) c.g).map
        (genericCompactSupportRho l E c.Z
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v) := by
  have hp := normalized_proper_transition l E b (o.geometry c.g) v
    ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)
  have hnY := rho_heq_coordinates l E b Y v
    ((SpTowerShriek.push l E b (o.geometry c.g)).obj
      ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K))
  have hnZ := rho_heq_coordinates l E b c.Z v
    ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)
  have hc :
      coordinateRho l E (normalizedCoordinates l E v) Y
          ((SpTowerShriek.push l E b (o.geometry c.g)).obj
            ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
        genericCompactSupportPushComparison l E b o c K m =
      (scalarExtensionFunctor (normalizedCoordinates l E v).val Y).map
          (genericCompactSupportPushComparison l E b o c K n) ≫
        (directImageScalarComparison (normalizedCoordinates l E v).val c.g).app
            ((SpTowerShriek.Ev l E c.Z n).obj
              ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
          (directImageConstantPush (SpTowerShriek.R l E m) c.g).map
            (coordinateRho l E (normalizedCoordinates l E v) c.Z
              ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) := by
    simp only [pushComparison_eq, SpTowerShriek.F, Functor.comp_obj] at hp ⊢
    run_tac transportInstances `hp
  rw [coordinates_eq] at hc
  have hgY := genericRho_heq_coordinates l E Y v
    ((SpTowerShriek.push l E b (o.geometry c.g)).obj
      ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K))
  have hgZ := genericRho_heq_coordinates l E c.Z v
    ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)
  simp only [SpTowerShriek.F, Functor.comp_obj] at hc ⊢
  run_tac transportInstances `hc

set_option maxHeartbeats 1000000 in
-- Explicit derived-category coordinate congruences need a larger elaboration budget.
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The finite open square for the constant-ring compact-support mate.
This is the open factor after the direct-image restriction comparison; it is
strictly weaker than the generic transition because it mentions only the open
comparison and finite restriction maps.
Source: Zheng Construction 4.1; Stacks 0D6D, 0D6J.
(blueprint: lem-sp-tower-generic-compact-support-finite-open-square).
Proof: transpose the normalized open transition, use the open adjunction
unit evaluation, and cancel the finite open evaluation comparison. -/
theorem generic_compactSupport_finiteOpenSquare
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n) :
    (directImageScalarComparison (quotient l E v) c.g).app
        ((SpTowerShriek.Ev l E c.Z n).obj
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
      (directImageConstantPush (SpTowerShriek.R l E m) c.g).map
        (genericCompactSupportRho l E c.Z
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v ≫
          genericCompactSupportOpenComparison l E b o c K m) =
    (directImageScalarExtension (quotient l E v) Y).map
        ((directImageConstantPush (SpTowerShriek.R l E n) c.g).map
          (genericCompactSupportOpenComparison l E b o c K n)) ≫
      (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((SpTowerShriek.Ev l E X n).obj K) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (genericCompactSupportRho l E X K v) := by
  have ho := normalized_open_transition l E b (o.openOp c.i) v K
  have hnZ := rho_heq_coordinates l E b c.Z v
    ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)
  have hnX := rho_heq_coordinates l E b X v K
  have hc :
      coordinateRho l E (normalizedCoordinates l E v) c.Z
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) ≫
        genericCompactSupportOpenComparison l E b o c K m =
      (scalarExtensionFunctor (normalizedCoordinates l E v).val c.Z).map
          (genericCompactSupportOpenComparison l E b o c K n) ≫
        (reductionOpenScalarIso (normalizedCoordinates l E v).val c.i).hom.app
            ((SpTowerShriek.Ev l E X n).obj K) ≫
          (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) c.i).map
            (coordinateRho l E (normalizedCoordinates l E v) X K) := by
    simp only [genericCompactSupportOpenComparison] at ho ⊢
    run_tac transportInstances `ho
  rw [coordinates_eq] at hc
  have ho' : genericCompactSupportRho l E c.Z
      ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v ≫
      genericCompactSupportOpenComparison l E b o c K m =
      (scalarExtensionFunctor (quotient l E v) c.Z).map
          (genericCompactSupportOpenComparison l E b o c K n) ≫
        (reductionOpenScalarIso (quotient l E v) c.i).hom.app
          ((SpTowerShriek.Ev l E X n).obj K) ≫
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) c.i).map
          (genericCompactSupportRho l E X K v) := by
    have hgZ := genericRho_heq_coordinates l E c.Z v
      ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)
    have hgX := genericRho_heq_coordinates l E X v K
    run_tac transportInstances `hc
  have result := map_open_square
    (directImageConstantPush (SpTowerShriek.R l E n) c.g)
    (directImageConstantPush (SpTowerShriek.R l E m) c.g)
    (scalarExtensionFunctor (quotient l E v) c.Z)
    (scalarExtensionFunctor (quotient l E v) Y)
    (directImageScalarComparison (quotient l E v) c.g)
    (genericCompactSupportOpenComparison l E b o c K n)
    (genericCompactSupportOpenComparison l E b o c K m)
    (genericCompactSupportRho l E c.Z
      ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v)
    ((reductionOpenScalarIso (quotient l E v) c.i).hom.app
        ((SpTowerShriek.Ev l E X n).obj K) ≫
      (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) c.i).map
        (genericCompactSupportRho l E X K v)) ho'
  simpa only [reductionDirectImageComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    reductionCompactSupport, Functor.comp_map, Category.assoc, scalarExtensionFunctor,
    directImageScalarExtension, sfIntrinsicDerivedOpen] using result

lemma comparison_factor
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) (n : ℕ) :
    (SpTowerShriek.Fcomparison l E b o c n).hom.app K =
      genericCompactSupportPushComparison l E b o c K n ≫
        (directImageConstantPush (SpTowerShriek.R l E n) c.g).map
          (genericCompactSupportOpenComparison l E b o c K n) := by
  simp [SpTowerShriek.Fcomparison, genericCompactSupportPushComparison,
    genericCompactSupportOpenComparison]

set_option maxHeartbeats 1000000 in
-- The categorical reassociation expands several derived functor maps.
private theorem finiteMatePaste
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n)
    (hp : genericCompactSupportRho l E Y ((SpTowerShriek.F l E b o c).obj K) v ≫
      genericCompactSupportPushComparison l E b o c K m =
      (directImageScalarExtension (quotient l E v) Y).map
          (genericCompactSupportPushComparison l E b o c K n) ≫
        (directImageScalarComparison (quotient l E v) c.g).app
          ((SpTowerShriek.Ev l E c.Z n).obj
            ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
        (directImageConstantPush (SpTowerShriek.R l E m) c.g).map
          (genericCompactSupportRho l E c.Z
            ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v))
    (ho : (directImageScalarComparison (quotient l E v) c.g).app
        ((SpTowerShriek.Ev l E c.Z n).obj
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K)) ≫
      (directImageConstantPush (SpTowerShriek.R l E m) c.g).map
        (genericCompactSupportRho l E c.Z
          ((SpTowerShriek.openD l E b (o.openOp c.i)).obj K) v ≫
          genericCompactSupportOpenComparison l E b o c K m) =
      (directImageScalarExtension (quotient l E v) Y).map
          ((directImageConstantPush (SpTowerShriek.R l E n) c.g).map
            (genericCompactSupportOpenComparison l E b o c K n)) ≫
        (reductionDirectImageComparison (quotient l E v) c.i c.g).app
          ((SpTowerShriek.Ev l E X n).obj K) ≫
        (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
          (genericCompactSupportRho l E X K v)) :
    genericCompactSupportRho l E Y ((SpTowerShriek.F l E b o c).obj K) v ≫
      (SpTowerShriek.Fcomparison l E b o c m).hom.app K =
    (directImageScalarExtension (quotient l E v) Y).map
        ((SpTowerShriek.Fcomparison l E b o c n).hom.app K) ≫
      (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((SpTowerShriek.Ev l E X n).obj K) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (genericCompactSupportRho l E X K v) := by
  rw [comparison_factor, comparison_factor]
  rw [← Category.assoc, hp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [ho]
  simp only [Category.assoc, Functor.map_comp]
/-- The finite compact-support mate square, obtained by pasting the proper and
open finite squares.  The proof is an actual categorical cancellation: the
factorisation of `Fcomparison` is mapped through scalar extension and the
middle direct-image comparison is reassociated with the open square.
(blueprint: lem-sp-tower-generic-compact-support-finite-mate-square).
Proof: apply the two finite factor equations, reassociate, use functoriality
of scalar extension, and rewrite the comparison factorisation. -/
theorem generic_compactSupport_finiteMateSquare
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n) :
    genericCompactSupportRho l E Y ((SpTowerShriek.F l E b o c).obj K) v ≫
      (SpTowerShriek.Fcomparison l E b o c m).hom.app K =
    (scalarExtensionFunctor (quotient l E v) Y).map
        ((SpTowerShriek.Fcomparison l E b o c n).hom.app K) ≫
      (reductionDirectImageComparison (quotient l E v) c.i c.g).app
        ((SpTowerShriek.Ev l E X n).obj K) ≫
      (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map
        (genericCompactSupportRho l E X K v) := by
  apply finiteMatePaste l E b o c K v
  · exact generic_compactSupport_finiteProperSquare l E b o c K v
  · exact generic_compactSupport_finiteOpenSquare l E b o c K v

end AlgebraicGeometry.ProEtale.SpTowerCalculus
