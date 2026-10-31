/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Package
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierExchange
public import WeilConjectures.AlgebraicGeometry.DualityPullback.Mates

/-! # Coherent duality against pullback at finite coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-kv-formal/
cor-sf-duality-pullback.md and its proof (blueprint: cor-sf-duality-pullback).

The current source uses finite rings on the small etale site. Natural isomorphisms
are displayed through the fully faithful inclusion of the finite-Tor subcategory.
The identity and composition comparisons below are actual compactification maps and
their right-adjoint mates, not independently chosen comparison isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The two contravariant functors, restricted to the existing finite-Tor subcategory.
The target is displayed through its fully faithful ambient inclusion; stability is
part of the six-operations datum. Source: first formula of cor-sf-duality-pullback
(blueprint: cor-sf-duality-pullback). -/
abbrev finiteDualityPullbackIso {X Y S : Scheme.{u}}
    (aX : X ⟶ S) (aY : Y ⟶ S) (f : X ⟶ Y)
    [HasCompactification aX] [HasCompactification aY] [HasCompactification f] :=
  (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
      L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual Λ aX ≅
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
      verdierDual Λ aY ⋙ R(f)^![Λ]

/-- The identity compact-support comparison, using the identity-open compactification.
Source: unit identification in cor-sf-duality-pullback
(blueprint: cor-sf-duality-pullback). -/
def finiteDualitySupportId (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    R(𝟙 X)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 (DerivedCategoryModule Λ X) :=
  (rightDerivedLowerShriekIso Λ (Compactification.ofIsOpenImmersion (𝟙 X))).symm ≪≫
    Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} Λ) X) _ ≪≫
    Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso Λ X

/-- The exceptional identity is the unique mate of the actual compact-support unit.
Source: identity clause of cor-sf-duality-pullback
(blueprint: cor-sf-duality-pullback). -/
def finiteDualityExceptionalId (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    R(𝟙 X)^![Λ] ≅ 𝟭 (DerivedCategoryModule Λ X) :=
  ((rightDerivedUpperShriekAdjunction Λ (𝟙 X)).ofNatIsoLeft
    (finiteDualitySupportId Λ X)).rightAdjointUniq Adjunction.id

/-- Canonical compact-support composition in compatible compactification coordinates.
The coordinate e compactifies f followed by the open part of d. Refinement comparisons
relate e.restrict and d.comp e to the chosen compactifications. No isomorphism is
chosen from a mere existence theorem. Source: composition identification in
cor-sf-duality-pullback (blueprint: cor-sf-duality-pullback). -/
def finiteDualitySupportComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  (rightDerivedLowerShriekIso Λ (d.comp e)).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ e.restrict) _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerShriekIso Λ d)

/-- The exceptional compositor is precisely the right-adjoint mate of compact-support
composition. Source: composition clause of cor-sf-duality-pullback
(blueprint: cor-sf-duality-pullback). -/
def finiteDualityExceptionalComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    R(f ≫ g)^![Λ] ≅ R(g)^![Λ] ⋙ R(f)^![Λ] :=
  ((rightDerivedUpperShriekAdjunction Λ (f ≫ g)).ofNatIsoLeft
    (finiteDualitySupportComp Λ f g d e)).rightAdjointUniq
      ((rightDerivedUpperShriekAdjunction Λ f).comp (rightDerivedUpperShriekAdjunction Λ g))

/-- The family of duality-pullback comparisons over a fixed base field. Its arguments
spell out separated finite-type schemes, separated finite-type maps, and the equality
of their structure morphisms. Compactifiability is a coordinate prerequisite of the
existing functors and holds for these maps by Nagata.
Source: the setting and naturality in f (blueprint: cor-sf-duality-pullback). -/
abbrev FiniteDualityPullbackFamily (k : Type u) [Field k] :=
  ∀ {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f], f ≫ aY = aX → finiteDualityPullbackIso Λ aX aY f

/-- The specified five-arrow Hom action: bidual transpose, ordinary adjunction,
inverse canonical Verdier exchange, bidual transpose, exceptional adjunction.
All arrows are the existing constructions, with the compact-support composition
fixed by compatible compactification coordinates. Source: the adjoint-transform
proof of cor-sf-duality-pullback (blueprint: cor-sf-duality-pullback). -/
def finiteDualityPullbackHomAction {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact aY]
    [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]
    (d : Compactification aY) (e : Compactification (f ≫ d.i))
    (A : DerivedCategoryModule Λ X) (B : DerivedCategoryModule Λ Y)
    (h : A ⟶ (verdierDual Λ (f ≫ aY)).obj
      (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B))) :
    A ⟶ (R(f)^![Λ]).obj ((verdierDual Λ aY).obj (op B)) :=
  letI := isIso_projectionMap_of_finite Λ f
  let tX := (verdierDualDoubleDual Λ (f ≫ aY)).app
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B) ≫
      (verdierDual Λ (f ≫ aY)).map h.op
  let a := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv
    B ((verdierDual Λ (f ≫ aY)).obj (op A)) tX
  let b := a ≫ (verdierDualRightDerivedLowerShriekIso Λ f aY
    (finiteDualitySupportComp Λ f aY d e)).inv.app (op A)
  (rightDerivedUpperShriekAdjunction Λ f).homEquiv A
    ((verdierDual Λ aY).obj (op B))
      ((verdierDualDoubleDual Λ aY).app ((R(f)_![ModuleCat.{u + 1} Λ]).obj A) ≫
        (verdierDual Λ aY).map b.op)

variable (k : Type u) [Field k]

/-- Characterization of chi by the specified adjoint-transform Hom action. It rules
out replacing the canonical comparison by an arbitrary coherent family of isomorphisms.
Source: passing to adjoints in cor-sf-duality-pullback
(blueprint: cor-sf-duality-pullback). -/
def FiniteDualityPullbackNormalized (chi : FiniteDualityPullbackFamily Λ k) : Prop :=
  ∀ {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification (f ≫ aY)]
    (d : Compactification aY) (e : Compactification (f ≫ d.i))
    (A : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory)
    (B : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory)
    (h : A.obj ⟶ (verdierDual Λ (f ≫ aY)).obj
      (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B.obj))),
    h ≫ (chi (f ≫ aY) aY f rfl).hom.app (op B) =
      finiteDualityPullbackHomAction Λ f aY d e A.obj B.obj h

/-- The identity equation for the family, after the canonical pullback and exceptional
unit identifications. Source: naturality in f (blueprint: cor-sf-duality-pullback). -/
def FiniteDualityPullbackIdentity (chi : FiniteDualityPullbackFamily Λ k) : Prop :=
  ∀ {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [HasCompactification (𝟙 X)]
    (K : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).FullSubcategory),
    (chi aX aX (𝟙 X) (Category.id_comp aX)).hom.app (op K) ≫
      (finiteDualityExceptionalId Λ X).hom.app ((verdierDual Λ aX).obj (op K.obj)) =
    (verdierDual Λ aX).map
      (((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).inv.app K.obj).op)

/-- The composition equation in actual compactification coordinates. The pullback
compositor is contravariantly dualized, and the exceptional compositor is the mate
of the canonical compact-support compositor above. Source: naturality in f
(blueprint: cor-sf-duality-pullback). -/
def FiniteDualityPullbackComposition (chi : FiniteDualityPullbackFamily Λ k) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    (aZ : Z ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ] [HasCompactification aZ]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasCompactification f] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] [HasCompactification g] [HasCompactification (f ≫ g)]
    (hf : f ≫ aY = aX) (hg : g ≫ aZ = aY)
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z).FullSubcategory),
    (verdierDual Λ aX).map
        (((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app K.obj).op) ≫
      (chi aX aZ (f ≫ g)
        ((Category.assoc f g aZ).trans ((congrArg (fun t ↦ f ≫ t) hg).trans hf))).hom.app
          (op K) ≫
      (finiteDualityExceptionalComp Λ f g d e).hom.app
        ((verdierDual Λ aZ).obj (op K.obj)) =
    (chi aX aY f hf).hom.app
        (op ⟨(L((g)^*[ModuleCat.{u + 1} Λ])).obj K.obj,
          constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) g K.property⟩) ≫
      (R(f)^![Λ]).map ((chi aY aZ g hg).hom.app (op K))

section DerivedSelfAdjunction

attribute [local instance high] SymmetricCategory.toBraidedCategory

variable (A : Type*) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The internal-Hom self-adjunction, formed before specializing the coefficient category.
Source: the adjoint-transform construction in cor-sf-duality-pullback.
(blueprint: def-sf-duality-pullback-canonical-family). -/
@[irreducible]
def finiteDualityDerivedSelfAdjunction (T : Scheme.{u})
    (W : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((derivedHom A T).flip.obj W).rightOp ⊣ (derivedHom A T).flip.obj W := by
  letI := _root_.DerivedCategory.braidedCategory' (Sheaf T.smallEtaleTopology A)
  exact MonoidalClosed.ihomFlipSelfAdjunction W

/-- Its unit is the existing derived double-dual map. This is the generic internal-Hom
unit formula, with the derived braiding used by the source construction.
Source: cor-sf-duality-pullback, double-dual transposition.
(blueprint: def-sf-duality-pullback-canonical-family). -/
theorem finiteDualityDerivedSelfAdjunction_unit (T : Scheme.{u})
    (W K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (finiteDualityDerivedSelfAdjunction A T W).unit.app K =
      (derivedHomToIhomIhomNatTrans A T W).app K := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf T.smallEtaleTopology A)
  unfold finiteDualityDerivedSelfAdjunction
  exact MonoidalClosed.ihomFlipSelfAdjunction_unit_app W K

end DerivedSelfAdjunction

/-- Specialization of internal-Hom transposition to the Verdier dual functor.
Source: cor-sf-duality-pullback, adjoint transposition.
(blueprint: def-sf-duality-pullback-canonical-family). -/
@[irreducible]
def finiteVerdierSelfAdjunction {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] : (verdierDual Λ a).rightOp ⊣ verdierDual Λ a :=
  finiteDualityDerivedSelfAdjunction (ModuleCat.{u + 1} Λ) X (dualizingComplex Λ a)

open Lean Elab Tactic Meta

-- Congruence and heterogeneous proof irrelevance avoid unfolding derived instances.
private meta partial def finiteDualityCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData.headBeta
  let b := b.consumeMData.headBeta
  if let .letE _ _ v body _ := a then return ← finiteDualityCongrHEq (body.instantiate1 v) b
  if let .letE _ _ v body _ := b then return ← finiteDualityCongrHEq a (body.instantiate1 v)
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    return ← mkAppM ``proof_irrel_heq #[a, b]
  for name in [``finiteVerdierSelfAdjunction, ``verdierDualDoubleDual, ``verdierDual,
      `AlgebraicGeometry.Etale.finiteDualityPullbackComparison,
      ``finiteDualityPullbackHomAction] do
    if a.getAppFn.isConstOf name then
      if let some a' ← withTransparency .all (unfoldDefinition? a) then
        return ← finiteDualityCongrHEq a' b
    if b.getAppFn.isConstOf name then
      if let some b' ← withTransparency .all (unfoldDefinition? b) then
        return ← finiteDualityCongrHEq a b'
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    try
      let argsA := a.getAppArgs
      let argsB := b.getAppArgs
      let ct ← mkHCongrWithArity a.getAppFn argsA.size
      let mut ps := #[]
      for i in [:argsA.size] do
        let mut h ← finiteDualityCongrHEq argsA[i]! argsB[i]!
        if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
        ps := ps ++ #[argsA[i]!, argsB[i]!, h]
      let pf := mkAppN ct.proof ps
      if (← inferType pf).isHEq then return pf
      else return ← mkAppM ``heq_of_eq #[pf]
    catch _ => pure ()
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different duality expressions: {a} versus {b}"
  return ← mkHEqRefl a

/-- The Verdier self-adjunction has the canonical double-dual as unit.
Source: cor-sf-duality-pullback, double transposition.
(blueprint: def-sf-duality-pullback-canonical-family). -/
theorem finiteVerdierSelfAdjunction_unit {X S : Scheme.{u}} (a : X ⟶ S)
    [HasCompactification a] (K : DerivedCategoryModule Λ X) :
    (finiteVerdierSelfAdjunction Λ a).unit.app K = (verdierDualDoubleDual Λ a).app K := by
  have h := finiteDualityDerivedSelfAdjunction_unit (ModuleCat.{u + 1} Λ) X
    (dualizingComplex Λ a) K
  run_tac withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let decls := (← getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "no internal-Hom unit formula"
    let eq ← finiteDualityCongrHEq target (← instantiateMVars d.type)
    let eq ← mkAppM ``eq_of_heq #[eq]
    (← getMainGoal).assign (← mkAppM ``Eq.mpr #[eq, d.toExpr])

set_option maxRecDepth 4000 in
/-- The adjoint transform of canonical Verdier exchange in compatible coordinates.
The two self-adjunctions transpose internal-Hom pairings, so the transform is an
isomorphism even before restricting to finite Tor dimension.
Source: the five-arrow proof of cor-sf-duality-pullback.
(blueprint: def-sf-duality-pullback-canonical-family). -/
@[irreducible]
def finiteDualityPullbackComparison {X Y S : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ S)
    [QuasiCompact f] [QuasiCompact aY] [HasCompactification f]
    [HasCompactification aY] [HasCompactification (f ≫ aY)]
    (d : Compactification aY) (e : Compactification (f ≫ d.i)) :
    L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual Λ (f ≫ aY) ≅
      verdierDual Λ aY ⋙ R(f)^![Λ] := by
  letI := isIso_projectionMap_of_finite Λ f
  exact dualityPullbackMate
    (finiteVerdierSelfAdjunction Λ (f ≫ aY))
    (finiteVerdierSelfAdjunction Λ aY)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (rightDerivedUpperShriekAdjunction Λ f)
    (verdierDualRightDerivedLowerShriekIso Λ f aY (finiteDualitySupportComp Λ f aY d e))

set_option maxHeartbeats 200000 in
-- The concrete coefficient-instance conversions require this kernel allowance.
set_option maxRecDepth 4000 in
/-- The five-arrow formula for the coordinate comparison.
Proof: apply the general adjoint-transform Hom formula. The units of the two
internal-Hom self-adjunctions are exactly the displayed double-dual maps; the
remaining three operations are the ordinary adjunction, inverse exchange and
exceptional adjunction.
Source: cor-sf-duality-pullback, passing to adjoints.
(blueprint: def-sf-duality-pullback-canonical-family). -/
theorem finiteDualityPullbackComparison_hom {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ S) [QuasiCompact f] [QuasiCompact aY]
    [HasCompactification f] [HasCompactification aY] [HasCompactification (f ≫ aY)]
    (d : Compactification aY) (e : Compactification (f ≫ d.i))
    (A : DerivedCategoryModule Λ X) (B : DerivedCategoryModule Λ Y)
    (h : A ⟶ (verdierDual Λ (f ≫ aY)).obj
      (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B))) :
    h ≫ (finiteDualityPullbackComparison Λ f aY d e).hom.app (op B) =
      finiteDualityPullbackHomAction Λ f aY d e A B h := by
  let := isIso_projectionMap_of_finite Λ f
  have hformula := dualityPullbackMate_hom_of_units
    (finiteVerdierSelfAdjunction Λ (f ≫ aY)) (finiteVerdierSelfAdjunction Λ aY)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (rightDerivedUpperShriekAdjunction Λ f)
    (verdierDualRightDerivedLowerShriekIso Λ f aY
      (finiteDualitySupportComp Λ f aY d e)) A B h
    ((verdierDualDoubleDual Λ (f ≫ aY)).app
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B))
    ((verdierDualDoubleDual Λ aY).app ((R(f)_![ModuleCat.{u + 1} Λ]).obj A))
    (finiteVerdierSelfAdjunction_unit Λ (f ≫ aY) _)
    (finiteVerdierSelfAdjunction_unit Λ aY _)
  dsimp only [finiteDualityPullbackComparison, finiteDualityPullbackHomAction,
    Functor.comp_obj, Functor.op_obj, Functor.rightOp_obj] at hformula ⊢
  run_tac withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let decls := (← getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `hformula) |
      throwError "no adjoint-transform Hom formula"
    let eq ← finiteDualityCongrHEq target (← instantiateMVars d.type)
    let eq ← mkAppM ``eq_of_heq #[eq]
    (← getMainGoal).assign (← mkAppM ``Eq.mpr #[eq, d.toExpr])

/-- A fixed family built from the canonical exchange and existing compactification
coordinates. `ofComp` constructs the compatible compactification from the given
ones; right-adjoint uniqueness constructs each comparison. Thus no isomorphism is
chosen from a mere existence statement.
Source: cor-sf-duality-pullback, construction after passing to adjoints.
(blueprint: def-sf-duality-pullback-canonical-family). -/
@[irreducible]
def canonicalFiniteDualityPullbackFamily : FiniteDualityPullbackFamily Λ k := by
  intro X Y aX aY _ _ _ _ _ _ _ _ f _ _ _ _ hf
  subst aX
  let d := HasCompactification.compactification aY
  let e := (HasCompactification.compactification (f ≫ aY)).ofComp d
  exact Functor.isoWhiskerLeft _ (finiteDualityPullbackComparison Λ f aY d e)


set_option maxHeartbeats 100000 in
-- Evaluate the chosen-coordinate construction before taking its components.
/-- The canonical family is the restriction of its explicit ambient comparison.
Proof: evaluate its definition at the reflexive structure-map equality.
Source: cor-sf-duality-pullback, construction of the adjoint transform.
(blueprint: def-sf-duality-pullback-canonical-family). -/
theorem canonicalFiniteDualityPullbackFamily_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification (f ≫ aY)] :
    canonicalFiniteDualityPullbackFamily Λ k (f ≫ aY) aY f rfl =
      Functor.isoWhiskerLeft
        (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι.op
        (finiteDualityPullbackComparison Λ f aY (HasCompactification.compactification aY)
          ((HasCompactification.compactification (f ≫ aY)).ofComp
            (HasCompactification.compactification aY))) := by
  unfold canonicalFiniteDualityPullbackFamily
  rfl

set_option maxHeartbeats 800000 in
-- The component formula uses the opaque ambient Hom-action theorem.
/-- The restricted canonical family has the fixed-coordinate five-arrow Hom action.
Proof: evaluate the restriction isomorphism using the two whiskering component
formulas, then apply the ambient comparison's Hom formula.
Source: cor-sf-duality-pullback, the adjoint-transform Hom characterization.
(blueprint: def-sf-duality-pullback-canonical-family). -/
theorem canonicalFiniteDualityPullbackFamily_hom {X Y : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification (f ≫ aY)]
    (A : DerivedCategoryModule Λ X)
    (B : (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).FullSubcategory)
    (h : A ⟶ (verdierDual Λ (f ≫ aY)).obj
      (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B.obj))) :
    h ≫ (canonicalFiniteDualityPullbackFamily Λ k (f ≫ aY) aY f rfl).hom.app (op B) =
      finiteDualityPullbackHomAction Λ f aY (HasCompactification.compactification aY)
        ((HasCompactification.compactification (f ≫ aY)).ofComp
          (HasCompactification.compactification aY)) A B.obj h := by
  have hformula := dualityPullbackRestrict_hom_of_formula
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y)
    (finiteDualityPullbackComparison Λ f aY (HasCompactification.compactification aY)
      ((HasCompactification.compactification (f ≫ aY)).ofComp
        (HasCompactification.compactification aY)))
    (canonicalFiniteDualityPullbackFamily Λ k (f ≫ aY) aY f rfl)
    (canonicalFiniteDualityPullbackFamily_eq Λ k f aY) A B h
    (finiteDualityPullbackHomAction Λ f aY (HasCompactification.compactification aY)
      ((HasCompactification.compactification (f ≫ aY)).ofComp
        (HasCompactification.compactification aY)) A B.obj h)
    (finiteDualityPullbackComparison_hom Λ f aY
      (HasCompactification.compactification aY)
      ((HasCompactification.compactification (f ≫ aY)).ofComp
        (HasCompactification.compactification aY)) A B.obj h)
  run_tac withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let decls := (← getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `hformula) |
      throwError "no restriction Hom formula"
    let eq ← finiteDualityCongrHEq target (← instantiateMVars d.type)
    let eq ← mkAppM ``eq_of_heq #[eq]
    (← getMainGoal).assign (← mkAppM ``Eq.mpr #[eq, d.toExpr])


end AlgebraicGeometry.Etale
