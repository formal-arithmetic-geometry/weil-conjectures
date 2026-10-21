/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Data for semilinear transport of a sheaf tensor presentation

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2, 03EK and 03EL.
(blueprint: def-pur-semilinear-tensor-presentation-data)

A tensor ring presentation is encoded by its pushout cocone in commutative-ring
sheaves. This is the sheafified ring tensor, without a sectionwise pushout assumption.
The two cocone maps encode the supplied presentation isomorphism uniquely.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.TensorPresentationTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C E : Type u} [Category.{u} C] [Category.{u} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology E}

/-- Underlying sets of a commutative-ring sheaf. Source: Stacks 03D2.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev ringSets (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R

/-- Underlying sets of an abelian sheaf. Source: Stacks 03D2.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev abSets (H : Sheaf J AddCommGrpCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj H

/-- The supplied tensor-ring presentation, recorded by its two inclusions.
An isomorphism from the sheafified ring tensor to R is equivalently this pushout cocone.
Source: Stacks 03EK (blueprint: def-pur-semilinear-tensor-presentation-data). -/
structure Presentation {D A : Sheaf J CommRingCat.{u}} (da : D ⟶ A) where
  B : Sheaf J CommRingCat.{u}
  R : Sheaf J CommRingCat.{u}
  db : D ⟶ B
  iA : A ⟶ R
  iB : B ⟶ R
  pushout : IsPushout da db iA iB

/-- Forget a module's scalar action. Source: Stacks 03D2.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev moduleAb {A : Sheaf J CommRingCat.{u}}
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :=
  (toSheaf (RingedTensor.ringSheaf A)).obj M

/-- Restrict an A-module to D. Source: Stacks 03EK.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev restrictModule {D A : Sheaf J CommRingCat.{u}} (da : D ⟶ A)
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :=
  (RingedTensor.restriction da).obj M

/-- B as a D-module. Source: Stacks 03EK.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev coefficientModule {D B : Sheaf J CommRingCat.{u}} (db : D ⟶ B) :=
  restrictModule db (unit (RingedTensor.ringSheaf B))

/-- The existing sheafified tensor M tensor_D B. Source: Stacks 03EK.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
abbrev tensorModule {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    (P : Presentation da) (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :=
  (monoidalCategory D).tensorObj (restrictModule da M) (coefficientModule P.db)

/-- The actual sheafification-unit pure tensor. Source: Stacks 03EK.
(blueprint: def-pur-semilinear-tensor-presentation-data). -/
def pure {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    (P : Presentation da) (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (U : Cᵒᵖ) (m : M.val.obj U) (b : P.B.obj.obj U) : (tensorModule P M).val.obj U :=
  RingedTensor.pure D (restrictModule da M) (coefficientModule P.db) U m b

/-- Preservation of ring operations on all generalized elements is ring transport.
Source: Stacks 03D2 (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def IsRingTransport (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (e : F.obj (ringSets R) ≅ ringSets S) : Prop :=
  (∀ (T : Sheaf J (Type u)) (x y z : T ⟶ ringSets R),
    (∀ U t, @id (R.obj.obj U) (z.hom.app U t) =
      @id (R.obj.obj U) (x.hom.app U t) + @id (R.obj.obj U) (y.hom.app U t)) →
    ∀ U t, (F.map z ≫ e.hom).hom.app U t =
      @id (S.obj.obj U) ((F.map x ≫ e.hom).hom.app U t) +
        @id (S.obj.obj U) ((F.map y ≫ e.hom).hom.app U t)) ∧
  (∀ (T : Sheaf J (Type u)) (x y z : T ⟶ ringSets R),
    (∀ U t, @id (R.obj.obj U) (z.hom.app U t) =
      @id (R.obj.obj U) (x.hom.app U t) * @id (R.obj.obj U) (y.hom.app U t)) →
    ∀ U t, (F.map z ≫ e.hom).hom.app U t =
      @id (S.obj.obj U) ((F.map x ≫ e.hom).hom.app U t) *
        @id (S.obj.obj U) ((F.map y ≫ e.hom).hom.app U t)) ∧
  (∀ (T : Sheaf J (Type u)) (z : T ⟶ ringSets R),
    (∀ U t, @id (R.obj.obj U) (z.hom.app U t) = 0) →
    ∀ U t, @id (S.obj.obj U) ((F.map z ≫ e.hom).hom.app U t) = 0) ∧
  (∀ (T : Sheaf J (Type u)) (z : T ⟶ ringSets R),
    (∀ U t, @id (R.obj.obj U) (z.hom.app U t) = 1) →
    ∀ U t, @id (S.obj.obj U) ((F.map z ≫ e.hom).hom.app U t) = 1)

/-- Additivity of an inverse-image comparison, tested on universal sums.
Source: Stacks 03D2 (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def IsAdditiveTransport (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (H : Sheaf J AddCommGrpCat.{u}) (G : Sheaf K AddCommGrpCat.{u})
    (e : F.obj (abSets H) ≅ abSets G) : Prop :=
  ∀ (T : Sheaf J (Type u)) (x y z : T ⟶ abSets H),
    (∀ U t, @id (H.obj.obj U) (z.hom.app U t) =
      @id (H.obj.obj U) (x.hom.app U t) + @id (H.obj.obj U) (y.hom.app U t)) →
    ∀ U t, (F.map z ≫ e.hom).hom.app U t =
      @id (G.obj.obj U) ((F.map x ≫ e.hom).hom.app U t) +
        @id (G.obj.obj U) ((F.map y ≫ e.hom).hom.app U t)

/-- Semilinearity as preservation of the action graph on every test sheaf.
Source: Stacks 03D2 (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def IsSemilinearTransport (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (H : Sheaf J AddCommGrpCat.{u}) (G : Sheaf K AddCommGrpCat.{u})
    (hR : ∀ U : Cᵒᵖ, SMul (R.obj.obj U) (H.obj.obj U))
    (hS : ∀ U : Eᵒᵖ, SMul (S.obj.obj U) (G.obj.obj U))
    (c : F.obj (ringSets R) ≅ ringSets S)
    (e : F.obj (abSets H) ≅ abSets G) : Prop :=
  ∀ (T : Sheaf J (Type u)) (a : T ⟶ ringSets R) (x z : T ⟶ abSets H),
    (∀ U t, z.hom.app U t = @SMul.smul _ _ (hR U) (a.hom.app U t) (x.hom.app U t)) →
    ∀ U t, (F.map z ≫ e.hom).hom.app U t =
      @SMul.smul _ _ (hS U) ((F.map a ≫ c.hom).hom.app U t)
        ((F.map x ≫ e.hom).hom.app U t)

/-- A compatible ring comparison for two presentations.
Commutation with both inclusions is exactly c F(beta) = beta (a tensor b) sigma:
the canonical tensor comparison preserves pure tensors, and the inclusions generate
as a sheaf of rings, rather than necessarily on global sections.
Source: Stacks 03EL (blueprint: def-pur-semilinear-tensor-presentation-data). -/
structure Transport (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX} (Y : Presentation daY) (X : Presentation daX) where
  d : F.obj (ringSets DY) ≅ ringSets DX
  a : F.obj (ringSets AY) ≅ ringSets AX
  b : F.obj (ringSets Y.B) ≅ ringSets X.B
  c : F.obj (ringSets Y.R) ≅ ringSets X.R
  hd : IsRingTransport F DY DX d
  ha : IsRingTransport F AY AX a
  hb : IsRingTransport F Y.B X.B b
  hc : IsRingTransport F Y.R X.R c
  da_comm : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map daY) ≫ a.hom =
    d.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map daX
  db_comm : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.db) ≫ b.hom =
    d.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map X.db
  iA_comm : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iA) ≫ c.hom =
    a.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map X.iA
  iB_comm : F.map ((sheafCompose J (CategoryTheory.forget CommRingCat)).map Y.iB) ≫ c.hom =
    b.hom ≫ (sheafCompose K (CategoryTheory.forget CommRingCat)).map X.iB

/-- The R-action specified by the tensor-presentation formula, including restriction.
Source: Stacks 03CY, 03EK (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def IsTensorAction {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    (P : Presentation da) (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (h : ∀ U : Cᵒᵖ, Module (P.R.obj.obj U) ((tensorModule P M).val.obj U)) : Prop :=
  (∀ {U V : Cᵒᵖ} (f : U ⟶ V) (z : P.R.obj.obj U) (n : (tensorModule P M).val.obj U),
    (tensorModule P M).val.map f (@SMul.smul _ _ (h U).toSMul z n) =
      @SMul.smul _ _ (h V).toSMul (P.R.obj.map f z) ((tensorModule P M).val.map f n)) ∧
  ∀ (U : Cᵒᵖ) (x : A.obj.obj U) (v w : P.B.obj.obj U) (m : M.val.obj U),
    @SMul.smul _ _ (h U).toSMul (P.iA.hom.app U x * P.iB.hom.app U v) (pure P M U m w) =
      pure P M U (x • m) (v * w)

/-- The sectionwise pure pairing as a map of sheaves of sets.
Source: Stacks 03EK (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def pairing {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    (P : Presentation da) (M : SheafOfModules.{u} (RingedTensor.ringSheaf A)) :
    abSets (moduleAb M) ⊗ ringSets P.B ⟶ abSets (moduleAb (tensorModule P M)) :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun t ↦ pure P M U t.1 t.2)
     naturality := by
       intro U V f
       ext t
       exact (RingedTensor.pure_restrict D (restrictModule da M)
         (coefficientModule P.db) f t.1 t.2).symm }⟩

/-- The actual-adjoint pure-tensor normalization, using the product comparison of V.
Source: Stacks 03EL (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def HasAdjunctFormula (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : F ⊣ V)
    {DY AY : Sheaf J CommRingCat.{u}} {DX AX : Sheaf K CommRingCat.{u}}
    {daY : DY ⟶ AY} {daX : DX ⟶ AX} (Y : Presentation daY) (X : Presentation daX)
    (MY : SheafOfModules.{u} (RingedTensor.ringSheaf AY))
    (MX : SheafOfModules.{u} (RingedTensor.ringSheaf AX))
    (s : F.obj (abSets (moduleAb MY)) ≅ abSets (moduleAb MX))
    (b : F.obj (ringSets Y.B) ≅ ringSets X.B)
    (r : F.obj (abSets (moduleAb (tensorModule Y MY))) ≅
      abSets (moduleAb (tensorModule X MX))) : Prop :=
  letI := adj.rightAdjoint_preservesLimits
  pairing Y MY ≫ adj.homEquiv _ _ r.hom =
    prod.lift
      (CartesianMonoidalCategory.fst _ _ ≫ adj.homEquiv _ _ s.hom)
      (CartesianMonoidalCategory.snd _ _ ≫ adj.homEquiv _ _ b.hom) ≫
        inv (prodComparison V (abSets (moduleAb MX)) (ringSets X.B)) ≫
          V.map (CartesianMonoidalCategory.lift prod.fst prod.snd ≫ pairing X MX)

/-- A compatible change of coefficient presentations, with D and A fixed.
The two inclusion equations are equivalent to i beta = beta' (1 tensor q).
Source: Stacks 03EK (blueprint: def-pur-semilinear-tensor-presentation-data). -/
structure CoefficientChange {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    (P P' : Presentation da) where
  q : P.B ⟶ P'.B
  i : P.R ⟶ P'.R
  db_comm : P.db ≫ q = P'.db
  iA_comm : P.iA ≫ i = P'.iA
  iB_comm : P.iB ≫ i = q ≫ P'.iB

/-- The canonical coefficient map is specified on the actual pure pairing.
Its additive sheafification universal property determines it uniquely.
Source: Stacks 03EK (blueprint: def-pur-semilinear-tensor-presentation-data). -/
def IsTensorMap {D A : Sheaf J CommRingCat.{u}} {da : D ⟶ A}
    {P P' : Presentation da} (q : CoefficientChange P P')
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (j : moduleAb (tensorModule P M) ⟶ moduleAb (tensorModule P' M)) : Prop :=
  ∀ (U : Cᵒᵖ) (m : M.val.obj U) (v : P.B.obj.obj U),
    j.hom.app U (pure P M U m v) = pure P' M U m (q.q.hom.app U v)

end SheafOfModules.TensorPresentationTransport
