module

public import Sheaf.Paper.PointSystemTransportDescent
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Paper.PointSystemNormalizedComparisonData
import all Sheaf.Paper.CoefficientConstantTowerRoosComparison
import all Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import all Sheaf.CategoryTheory.StrictRoosDerivation
import Mathlib.Algebra.Group.Ext

/-! # Point restriction on the whole strict Roos cone

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model,
proof (3), whole-cone point-factor refinement; Stacks Tag 0941
(blueprint: lem-trf-point-restriction-whole-roos-square).

The existing `roosF` has coordinates `(b,a)` and differential
`(-db - (1-s)a, da)`. The index `n : ℕ` denotes exponent `n+1`.
All system complexes are unbounded and all transitions are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.checkUnivs false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.pointReductionModuleDerived
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u v w vB wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PointRestrictionWholeRoos

section Coordinates
variable {A : Type v} [Category.{w} A] [Abelian A] [HasCountableProducts A]

/-- Projection to level n of the shifted-product coordinate of the existing Roos cone.
Source: Stacks 0941 (blueprint: lem-trf-point-restriction-whole-roos-square). -/
def left (V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ) :=
  (roosχ V p).hom ≫ biprod.fst ≫
    (Pi.π (fun k : ℕ ↦ V.asFunctor.obj (op k)) n).f p

/-- Projection to level n of the unshifted-product coordinate of the existing Roos cone.
Source: Stacks 0941 (blueprint: lem-trf-point-restriction-whole-roos-square). -/
def right (V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) (n : ℕ) :=
  (roosχ V p).hom ≫ biprod.snd ≫
    (Pi.π (fun k : ℕ ↦ V.asFunctor.obj (op k)) n).f (p + 1)
end Coordinates

section
variable {A : Type v} [Category.{w} A] [Abelian A] [HasCountableProducts A]
@[reassoc] private theorem left_natural {V W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : V ⟶ W)
    (p : ℤ) (n : ℕ) :
    (roosF.map f).f (p + 1) ≫ left W p n =
      left V p n ≫ (f.f p).app (op n) := by
  dsimp only [left]
  rw [← Category.assoc, ← Category.assoc, roosF_map_χ]
  simp only [Category.assoc, biprod.map_fst_assoc]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Pi.map_π]
  simp only [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f]
@[reassoc] private theorem right_natural {V W : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : V ⟶ W)
    (p : ℤ) (n : ℕ) :
    (roosF.map f).f (p + 1) ≫ right W p n =
      right V p n ≫ (f.f (p + 1)).app (op n) := by
  dsimp only [right]
  rw [← Category.assoc, ← Category.assoc, roosF_map_χ]
  simp only [Category.assoc, biprod.map_snd_assoc]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, Pi.map_π]
  simp only [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_map_app_f]
private theorem coordinates_ext (V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ)
    {N : A} {f g : N ⟶ (roosF.obj V).X (p + 1)}
    (hl : ∀ n, f ≫ left V p n = g ≫ left V p n)
    (hr : ∀ n, f ≫ right V p n = g ≫ right V p n) : f = g := by
  apply (cancel_mono (roosχ V p).hom).mp
  apply biprod.hom_ext
  · apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval A (.up ℤ) p)
      (fun n : ℕ ↦ V.asFunctor.obj (op n))).hom_ext
    rintro ⟨n⟩
    simpa only [left, Category.assoc, Fan.mk_π_app, HomologicalComplex.eval_map] using hl n
  · apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval A (.up ℤ) (p + 1))
      (fun n : ℕ ↦ V.asFunctor.obj (op n))).hom_ext
    rintro ⟨n⟩
    simpa only [right, Category.assoc, Fan.mk_π_app, HomologicalComplex.eval_map] using hr n

variable {B : Type vB} [Category.{wB} B] [Abelian B] [HasCountableProducts B]
private theorem comparison_coordinates (Q : A ⥤ B) [Q.Additive]
    (V : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (P : (Q.mapHomologicalComplex (.up ℤ)).obj (roosP V) ⟶
      roosP ((((Functor.whiskeringRight ℕᵒᵖ A B).obj Q).mapHomologicalComplex (.up ℤ)).obj V))
    (k : (Q.mapHomologicalComplex (.up ℤ)).obj (roosF.obj V) ⟶
      roosF.obj ((((Functor.whiskeringRight ℕᵒᵖ A B).obj Q).mapHomologicalComplex
        (.up ℤ)).obj V))
    (hp : ∀ n : ℕ, P ≫ Pi.π _ n =
      (Q.mapHomologicalComplex (.up ℤ)).map (Pi.π _ n))
    (hd : ∀ p : ℤ,
      k.f (p + 1) ≫ (roosχ _ p).hom ≫ biprod.fst =
        Q.map ((roosχ V p).hom ≫ biprod.fst) ≫ P.f p ∧
      k.f (p + 1) ≫ (roosχ _ p).hom ≫ biprod.snd =
        Q.map ((roosχ V p).hom ≫ biprod.snd) ≫ P.f (p + 1))
    (p : ℤ) (n : ℕ) :
    k.f (p + 1) ≫ left _ p n = Q.map (left V p n) ∧
    k.f (p + 1) ≫ right _ p n = Q.map (right V p n) := by
  let V' := (((Functor.whiskeringRight ℕᵒᵖ A B).obj Q).mapHomologicalComplex
    (.up ℤ)).obj V
  have hp' (q : ℤ) := congrArg (fun f ↦ f.f q) (hp n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hp'
  constructor
  · have hh := congrArg (fun f ↦ f ≫ (Pi.π (fun j : ℕ ↦ V'.asFunctor.obj (op j)) n).f p) (hd p).1
    dsimp only [V'] at hh
    simpa only [left, Category.assoc, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, hp' p, ← Q.map_comp] using hh
  · have hh := congrArg
      (fun f ↦ f ≫ (Pi.π (fun j : ℕ ↦ V'.asFunctor.obj (op j)) n).f (p + 1)) (hd p).2
    dsimp only [V'] at hh
    simpa only [right, Category.assoc, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, hp' (p + 1), ← Q.map_comp] using hh

private theorem reindex_coordinates
    {W Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {N : CochainComplex A ℤ} (k : N ⟶ roosF.obj Z) (e : W ≅ Z)
    (p : ℤ) (n : ℕ) :
    (k ≫ roosF.map e.inv).f (p + 1) ≫ left W p n ≫
        (e.hom.f p).app (op n) = k.f (p + 1) ≫ left Z p n ∧
    (k ≫ roosF.map e.inv).f (p + 1) ≫ right W p n ≫
        (e.hom.f (p + 1)).app (op n) = k.f (p + 1) ≫ right Z p n := by
  constructor
  · simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Category.id_comp, Category.assoc]
    erw [left_natural_assoc]
    simp only [← Category.assoc, ← NatTrans.comp_app, ← HomologicalComplex.comp_f,
      e.inv_hom_id, HomologicalComplex.id_f, NatTrans.id_app, Category.comp_id]
    exact Category.comp_id _
  · simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Category.id_comp, Category.assoc]
    erw [right_natural_assoc]
    simp only [← Category.assoc, ← NatTrans.comp_app, ← HomologicalComplex.comp_f,
      e.inv_hom_id, HomologicalComplex.id_f, NatTrans.id_app, Category.comp_id]
    exact Category.comp_id _

private abbrev towerComplex (Q : A ⥤ B) [Q.Additive] :=
  ((Functor.whiskeringRight ℕᵒᵖ A B).obj Q).mapHomologicalComplex (.up ℤ)

private theorem restriction_square (S : A ⥤ B) [S.Additive]
    (F : A ⥤ A) [F.Additive] (σ : S ⟶ F ⋙ S)
    (κ : roosF ⋙ S.mapHomologicalComplex (.up ℤ) ≅ towerComplex S ⋙ roosF)
    (hκ : ∀ V p n,
      (κ.hom.app V).f (p + 1) ≫ left ((towerComplex S).obj V) p n =
        S.map (left V p n) ∧
      (κ.hom.app V).f (p + 1) ≫ right ((towerComplex S).obj V) p n =
        S.map (right V p n))
    (X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (e : Y ≅ (towerComplex F).obj X)
    (u : (towerComplex S).obj X ⟶ (towerComplex S).obj Y)
    (hu : ∀ i n, (u.f i).app (op n) ≫ S.map ((e.hom.f i).app (op n)) =
      σ.app ((X.X i).obj (op n)))
    (k : (F.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ⟶ roosF.obj Y)
    (hk : ∀ p n,
      k.f (p + 1) ≫ left Y p n ≫ (e.hom.f p).app (op n) = F.map (left X p n) ∧
      k.f (p + 1) ≫ right Y p n ≫ (e.hom.f (p + 1)).app (op n) =
        F.map (right X p n)) :
    roosF.map u ≫ κ.inv.app Y = κ.inv.app X ≫
      (NatTrans.mapHomologicalComplex σ (.up ℤ)).app (roosF.obj X) ≫
      (S.mapHomologicalComplex (.up ℤ)).map k := by
  apply (cancel_mono (κ.hom.app Y)).mp
  simp only [Category.assoc, κ.inv_hom_id_app, Category.comp_id]
  apply (cancel_epi (κ.hom.app X)).mp
  simp only [← Category.assoc, κ.hom_inv_id_app, Category.id_comp]
  apply HomologicalComplex.hom_ext
  intro j
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, j = p + 1 := ⟨j - 1, by omega⟩
  apply coordinates_ext ((towerComplex S).obj Y) p
  · intro n
    apply (cancel_mono (S.map ((e.hom.f p).app (op n)))).mp
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Category.id_comp, Category.assoc]
    erw [Category.id_comp]
    erw [left_natural_assoc]
    rw [← Category.assoc, (hκ X p n).1, hu]
    have hh := (hk p n).1
    have ht := (hκ Y p n).1
    erw [reassoc_of% ht]
    simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
    rw [← S.map_comp, ← S.map_comp, hh]
    exact σ.naturality (left X p n)
  · intro n
    apply (cancel_mono (S.map ((e.hom.f (p + 1)).app (op n)))).mp
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Category.id_comp, Category.assoc]
    erw [Category.id_comp]
    erw [right_natural_assoc]
    rw [← Category.assoc, (hκ X p n).2, hu]
    have hh := (hk p n).2
    have ht := (hκ Y p n).2
    erw [reassoc_of% ht]
    simp only [Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f]
    rw [← S.map_comp, ← S.map_comp, hh]
    exact σ.naturality (right X p n)

end



private theorem module_eq_identity {R : Type v} [Ring R] (M N : ModuleCat.{v} R)
    (e : M ⟶ N) (h : ∀ x : M, HEq (e x) x) : M = N := by
  let f : M → N := e.hom
  have ha : ∀ x y : M, f (x + y) = f x + f y := e.hom.map_add'
  have hs : ∀ (r : R) (x : M), f (r • x) = r • f x := e.hom.map_smul'
  change ∀ x : M, HEq (f x) x at h
  rcases M with @⟨X, a, m⟩
  rcases N with @⟨Y, b, n⟩
  have hc : Y = X := type_eq_of_heq (h 0)
  subst Y
  have he : f = id := funext (fun x ↦ eq_of_heq (h x))
  have hab : a = b := AddCommGroup.ext (funext fun x ↦ funext fun y ↦
    (congrFun he (a.add x y)).symm.trans
      ((ha x y).trans (congrArg₂ b.add (congrFun he x) (congrFun he y))))
  subst b
  have hmn : m = n := Module.ext' m n (fun r x ↦
    (congrFun he (m.smul r x)).symm.trans
      ((hs r x).trans (congrArg (n.smul r) (congrFun he x))))
  subst n
  rfl

private theorem hom_heq_of_identity_comp {R : Type v} [Ring R]
    {M N P : ModuleCat.{v} R} (e : N ⟶ P)
    (he : ∀ x : N, HEq (e x) x) (f : M ⟶ N) (g : M ⟶ P)
    (h : f ≫ e = g) : HEq f g := by
  have hp := module_eq_identity N P e he
  subst P
  have hi : e = 𝟙 N := by
    ext x
    exact eq_of_heq (he x)
  rw [hi, Category.comp_id] at h
  exact heq_of_eq h

private theorem sheaf_hom_heq_of_identity_comp
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}} {M N P : SheafOfModules.{v} R}
    (e : N ⟶ P) (f : M ⟶ N) (g : M ⟶ P) (h : f ≫ e = g) (W : Cᵒᵖ)
    (he : ∀ x, HEq ((e.val.app W) x) x) : HEq (f.val.app W) (g.val.app W) := by
  exact hom_heq_of_identity_comp _ he _ _ (congrArg (fun a ↦ a.val.app W) h)

private theorem normalized_transport
    {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
    (Q : C ⥤ D) (L : D ⥤ E) (H : C ⥤ E) (η : Q ⋙ L ≅ H)
    {X Y : C} {A B : D} (a : A ≅ Q.obj X) (b : B ≅ Q.obj Y)
    (u : A ⟶ B) (v : X ⟶ Y) (h : u ≫ b.hom = a.hom ≫ Q.map v) :
    L.map a.inv ≫ L.map u ≫ L.map b.hom ≫ η.hom.app Y =
      η.hom.app X ≫ H.map v := by
  calc
    _ = L.map (a.inv ≫ (u ≫ b.hom)) ≫ η.hom.app Y := by
      simp only [L.map_comp, Category.assoc]
    _ = L.map (Q.map v) ≫ η.hom.app Y := by rw [h, a.inv_hom_id_assoc]
    _ = _ := η.hom.naturality v

set_option linter.flexible false in
-- The final normalization cancels a definitional ordinary-limit interchange.
private theorem normalized_scalar (R : Type v) [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)] :
    ∃ η : DerivedCategory.Q ⋙ WeilConjectures.CoefTower.totalLimit R ≅
        roosF (A := ModuleCat.{v} R) ⋙ DerivedCategory.Q,
      ∀ V : CochainComplex (ℕᵒᵖ ⥤ ModuleCat.{v} R) ℤ,
        (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} R) ⥤ ModuleCat.{v} R).rightDerivedFunctorUnitQ V ≫
            η.hom.app V =
          DerivedCategory.Q.map
            ((limit.isoLimitCone
              ⟨HomologicalComplex.coneOfHasLimitEval V.asFunctor,
                HomologicalComplex.isLimitConeOfHasLimitEval V.asFunctor⟩).inv ≫ roosι V) := by
  let A := ModuleCat.{v} R
  let : HasFilteredColimitsOfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{v, v} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A) := {}
  let L : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let ν : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun X Y f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let β := (Functor.isoWhiskerRight (strictTowerLimitIso (A := A))
    DerivedCategory.Q).hom ≫ ν
  obtain ⟨e, he⟩ := normalizedRoosIso L.rightDerivedFunctor β (fun I hI ↦ by
    have := hI
    dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, ν]
    rw [Functor.rightDerivedFunctorUnitQ_eq]
    infer_instance)
  refine ⟨e.symm, ?_⟩
  intro V
  have heV := congr_app he V
  change DerivedCategory.Q.map (roosι V) ≫ e.hom.app V =
    DerivedCategory.Q.map ((strictTowerLimitIso (A := A)).hom.app V) ≫
      L.rightDerivedFunctorUnitQ V at heV
  apply (cancel_mono (e.hom.app V)).mp
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app,
    Category.comp_id, Functor.map_comp]
  rw [heV]
  simp only [← Category.assoc, ← Functor.map_comp]
  have hc : (limit.isoLimitCone
        ⟨HomologicalComplex.coneOfHasLimitEval V.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval V.asFunctor⟩).inv ≫
      ((strictTowerLimitIso (A := A)).hom.app V) = 𝟙 _ := by
    exact Iso.inv_hom_id _
  rw [hc]
  have hi := CategoryTheory.Functor.map_id DerivedCategory.Q
    ((HomologicalComplex.coneOfHasLimitEval V.asFunctor).pt)
  rw [hi]
  exact (Category.comp_id _).trans (Category.id_comp _).symm



variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing completed-module category at the geometric point.
Source: blueprint coefficient conventions
(blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev Ambient := SheafOfModules.{max u (t + 1)}
  (pointRestrictionRing l E (Spec (.of D.k)) none)

/-- Integral scalar modules in the common site/coefficient universe.
Source: blueprint coefficient conventions
(blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev Scalars := ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)

/-- The recorded strict coefficient-system category, with quotient-linear transitions.
Source: Stacks 0941 (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev Systems := coefficientSequenceModules l E (Spec (.of D.k))

/-- Levelwise restriction to completed scalars on complexes of entire strict systems.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev U := (coefficientSequenceRestriction l E (Spec (.of D.k))).mapHomologicalComplex (.up ℤ)

/-- Completed-module inverse image along the actual rth geometric Frobenius power.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev F (r : ℕ) := pointRestrictionInverseImage l E (PointSystemTransport.pointPower D r).hom
  none

/-- Exact sections with the constant integral scalar action, on unbounded complexes.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev T := (pointRestrictionSections l E D.k none).mapHomologicalComplex (.up ℤ)

/-- The same sections functor applied to whole strict towers.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev TT := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
  (pointRestrictionSections l E D.k none)).mapHomologicalComplex (.up ℤ)

/-- The actual levelwise inverse image on complexes of strict coefficient systems.
Source: blueprint proof (3) (blueprint: lem-trf-point-restriction-whole-roos-square). -/
abbrev G (r : ℕ) := (PointSystemTransport.pull D l E r).mapHomologicalComplex (.up ℤ)

attribute [local irreducible] roosF
  coefficientSequenceRestriction PointSystemTransport.pull
  PointSystemTransport.chainTransport PointSystemTransport.derivedTransport
  pointRestrictionScalarAt pointRestrictionCoefficientMap inverseImageCompletedCoefficientMap

attribute [local irreducible] left right roosχ limit
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceCommRingSheaf

private theorem hcongr_apply {α γ : Sort v} {β δ : Sort w} {f : α → β} {g : γ → δ}
    {x : α} {y : γ} (hcod : β = δ) (h : HEq f g) (hx : HEq x y) :
    HEq (f x) (g y) := by
  subst δ
  exact heq_of_eq (congr_heq h hx)

private theorem restriction_presheaf
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (S : Scheme.{t})
    (M : coefficientSequenceModules l E S) (n : ℕ) :
    (((coefficientSequenceRestriction l E S).obj M).obj (op n)).val.presheaf =
      (Prod.sectR n S.ProEt).op ⋙ M.val.presheaf := by
  exact congrArg (fun Q : coefficientSequenceModules l E S ⥤
      scalarReductionSource l E S ↦ (Q.obj M).val.presheaf)
    (coefficientSequenceRestriction_evaluation l E S n)
private theorem map_fun_heq {C : Type*} [Category C]
    {P Q : C ⥤ AddCommGrpCat.{u}} (h : P = Q) {X Y : C} (f : X ⟶ Y) :
    HEq (fun x ↦ P.map f x) (fun x ↦ Q.map f x) := by
  subst Q
  rfl

variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private theorem raw_restriction_heq (r : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k))) (n : ℕ) :
    HEq (fun x ↦ pointRestrictionRaw l E (PointSystemTransport.pointPower D r).hom none
      (((coefficientSequenceRestriction l E (Spec (.of D.k))).obj M).obj (op n)) x)
      (fun x ↦ M.val.map
        (Prod.mkHom (𝟙 n)
          (pointRestrictionArrow (PointSystemTransport.pointPower D r).hom)).op x) := by
  exact map_fun_heq (restriction_presheaf l E (Spec (.of D.k)) M n)
    (pointRestrictionArrow (PointSystemTransport.pointPower D r).hom).op

private theorem level_transport (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r)
    (c : PointSystemNormalizedComparison.Data D l E r)
    (σ : pointRestrictionSections l E D.k none ⟶
      F D l E r ⋙ pointRestrictionSections l E D.k none)
    (hσ : ∀ (N : Ambient D l E) (x : N.val.obj (op (ProEt.mk (𝟙 _)))),
      σ.app N x = pointRestrictionRaw l E (PointSystemTransport.pointPower D r).hom none N x)
    (M : CochainComplex (Systems D l E) ℤ) (i : ℤ) (n : ℕ) :
    (((PointSystemTransport.chainTransport D l E hl r hr).app M).f i).app (op n) ≫
      (pointRestrictionSections l E D.k none).map
        (((c.coefficient.hom.app M).f i).app (op n)) =
      σ.app ((((U D l E).obj M).X i).obj (op n)) := by
  ext x
  change (((((c.coefficient.hom.app M).f i).app (op n)).val.app
    (op (ProEt.mk (𝟙 _))))
      (((((PointSystemTransport.chainTransport D l E hl r hr).app M).f i).app (op n)) x)) = _
  have h := c.coefficient_sections M i n (ProEt.mk (𝟙 _))
    (((((PointSystemTransport.chainTransport D l E hl r hr).app M).f i).app (op n)) x)
  apply eq_of_heq
  refine h.trans ?_
  have hu := (PointSystemTransport.chainTransport_existsUnique D l E hl r hr).exists.choose_spec
    M i n
  have hrw := raw_restriction_heq D l E r (M.X i) n
  have hs : HEq
      (fun x ↦ σ.app ((((U D l E).obj M).X i).obj (op n)) x)
      (fun x ↦ pointRestrictionRaw l E (PointSystemTransport.pointPower D r).hom none
        ((((U D l E).obj M).X i).obj (op n)) x) :=
    heq_of_eq (funext (hσ _))
  have hh := hu.trans (hs.trans hrw).symm
  have hcod := type_eq_of_heq (c.coefficient_sections M i n (ProEt.mk (𝟙 _)) 0)
  have hhx := hcongr_apply hcod.symm hh (HEq.rfl : HEq x x)
  have hhx' := hhx
  dsimp only [ModuleCat.Hom.hom] at *
  with_unfolding_all exact hhx'



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def sectionsRoosComparison (r : ℕ)
    (c : PointSystemNormalizedComparison.Data D l E r) :
    roosF (A := Ambient D l E) ⋙ T D l E ≅
      TT D l E ⋙ roosF (A := ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) :=
  c.sections.kappa

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sectionsRoosComparison_coordinates
    (r : ℕ) (c : PointSystemNormalizedComparison.Data D l E r)
    (V : CochainComplex (ℕᵒᵖ ⥤ Ambient D l E) ℤ) (p : ℤ) (n : ℕ) :
      ((sectionsRoosComparison D l E r c).hom.app V).f (p + 1) ≫ left ((TT D l E).obj V) p n =
        (pointRestrictionSections l E D.k none).map (left V p n) ∧
      ((sectionsRoosComparison D l E r c).hom.app V).f (p + 1) ≫ right ((TT D l E).obj V) p n =
        (pointRestrictionSections l E D.k none).map (right V p n) :=
  comparison_coordinates _ V (c.sections.product V).hom
    ((sectionsRoosComparison D l E r c).hom.app V)
    (c.sections.product_projection V) (c.sections.diagonal V) p n

attribute [local irreducible] sectionsRoosComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def inverseImageRoosComparison (r : ℕ)
    (c : PointSystemNormalizedComparison.Data D l E r) :
    U D l E ⋙ roosF ⋙ (F D l E r).mapHomologicalComplex (.up ℤ) ≅
      G D l E r ⋙ U D l E ⋙ roosF := by
  let Q := ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (PointSystemNormalizedComparison.F D l E r)).mapHomologicalComplex (.up ℤ)
  exact Functor.isoWhiskerLeft (U D l E) c.inverseImage.kappa ≪≫
    (Functor.associator (U D l E) Q roosF).symm ≪≫
    Functor.isoWhiskerRight c.coefficient.symm roosF ≪≫
    Functor.associator (G D l E r) (U D l E) roosF

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverseImageRoosComparison_coordinates (r : ℕ)
    (c : PointSystemNormalizedComparison.Data D l E r)
    (M : CochainComplex (Systems D l E) ℤ) (p : ℤ) (n : ℕ) :
      ((inverseImageRoosComparison D l E r c).hom.app M).f (p + 1) ≫
          left ((U D l E).obj ((G D l E r).obj M)) p n ≫
          ((c.coefficient.hom.app M).f p).app (op n) =
        (F D l E r).map (left ((U D l E).obj M) p n) ∧
      ((inverseImageRoosComparison D l E r c).hom.app M).f (p + 1) ≫
          right ((U D l E).obj ((G D l E r).obj M)) p n ≫
          ((c.coefficient.hom.app M).f (p + 1)).app (op n) =
        (F D l E r).map (right ((U D l E).obj M) p n) := by
  unfold inverseImageRoosComparison
  have h₁ := reindex_coordinates (c.inverseImage.kappa.hom.app ((U D l E).obj M))
    (c.coefficient.app M) p n
  have h₂ := comparison_coordinates _ ((U D l E).obj M)
    (c.inverseImage.product ((U D l E).obj M)).hom
    (c.inverseImage.kappa.hom.app ((U D l E).obj M))
    (c.inverseImage.product_projection _) (c.inverseImage.diagonal _) p n
  exact ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

attribute [local irreducible] inverseImageRoosComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
set_option maxHeartbeats 800000 in
-- Product and cone comparisons require several independent universe transports.
/-- The whole restriction square, with both cone coordinates and normalized localization.

Source: blueprint main-20261015, prop-trf-rational-frobenius-integral-model, proof (3),
agent-written whole-Roos refinement; Stacks Tag 0941
(blueprint: lem-trf-point-restriction-whole-roos-square).

Proof: (1) Use lem-weil-point-automorphism-restriction-natural on every ambient module
complex, with the completed constant-scalar action. Its components are actual site
restriction, without boundedness or completeness. The strict system map is the specified
chainTransport of lem-trf-point-system-transport-descent, including the finite j maps.
(2) Sections preserve products sectionwise and are exact at the algebraically closed
point. Inverse image is an exact reindexing equivalence preserving products. Apply
lem-cbc-exact-product-functor-strict-limit to obtain both canonical product comparisons;
convert its signed coordinates by (x,y)=(a,-b). This gives the projection equations below.
(3) Strict transition compatibility gives (1-s')P=P(1-s) by each product projection.
The existing roosF map is consequently diagonal (Pb,Pa), with zero off-diagonal terms.
(4) Naturality of ambient restriction for each product projection identifies restriction
on the entire product with P. This is a universal-property calculation of actual maps.
(5) Apply that calculation separately in degrees p and p+1. Naturality for the two
biproduct projections gives the displayed equality of actual chain maps.
(6) The normalized comparison of lem-weil-strict-roos-comparison is natural on the
whole tower category, so its inverse eta intertwines the localized u with H(u).
Its ordinary-limit inclusion is (0,gamma); its derived-unit equation fixes normalization.
(7) All comparisons and sigma are natural transformations. Exactness and exact products
preserve quasi-isomorphisms, so the strict equations localize. Naturality also holds
for inverse quasi-isomorphisms and their zigzags, proving independence of representatives.
No equality of derived maps is inferred from their separate level evaluations. -/
theorem point_restriction_whole_roos_square (hl : l ≠ D.p) (r : ℕ) (hr : 1 ≤ r) :
    ∃ σ : pointRestrictionSections l E D.k none ⟶
        F D l E r ⋙ pointRestrictionSections l E D.k none,
      (∀ (N : Ambient D l E) (x : N.val.obj (op (ProEt.mk (𝟙 _)))),
        σ.app N x = pointRestrictionRaw l E (PointSystemTransport.pointPower D r).hom none
          N x) ∧
      ∃ (κT : roosF (A := Ambient D l E) ⋙ T D l E ≅
          TT D l E ⋙ roosF (A := ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)))
        (κF : U D l E ⋙ roosF ⋙ (F D l E r).mapHomologicalComplex (.up ℤ) ≅
          G D l E r ⋙ U D l E ⋙ roosF),
        (∀ (V : CochainComplex (ℕᵒᵖ ⥤ Ambient D l E) ℤ) (p : ℤ) (n : ℕ),
          (κT.hom.app V).f (p + 1) ≫ left ((TT D l E).obj V) p n =
            (pointRestrictionSections l E D.k none).map (left V p n) ∧
          (κT.hom.app V).f (p + 1) ≫ right ((TT D l E).obj V) p n =
            (pointRestrictionSections l E D.k none).map (right V p n)) ∧
        (∀ (M : CochainComplex (Systems D l E) ℤ) (p : ℤ) (n : ℕ)
          (W : (Spec (.of D.k)).ProEt),
          HEq (((κF.hom.app M).f (p + 1) ≫
              left ((U D l E).obj ((G D l E r).obj M)) p n).val.app (op W))
            (((F D l E r).map (left ((U D l E).obj M) p n)).val.app (op W)) ∧
          HEq (((κF.hom.app M).f (p + 1) ≫
              right ((U D l E).obj ((G D l E r).obj M)) p n).val.app (op W))
            (((F D l E r).map (right ((U D l E).obj M) p n)).val.app (op W))) ∧
        PointSystemTransport.HasRestrictionComponents D l E r
          (PointSystemTransport.chainTransport D l E hl r hr) ∧
        (∀ (V W : CochainComplex (ℕᵒᵖ ⥤ Ambient D l E) ℤ) (f : V ⟶ W),
          QuasiIso f → QuasiIso (roosF.map f)) ∧
        (∀ (V W : CochainComplex
            (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) ℤ) (f : V ⟶ W),
          QuasiIso f → QuasiIso (roosF.map f)) ∧
        (∀ M : CochainComplex (Systems D l E) ℤ,
          roosU ((PointSystemTransport.complexSections D l E).obj M) ≫
              roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) =
            roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M) ≫
              roosU ((PointSystemTransport.transportedComplexSections D l E r).obj M)) ∧
        (∀ (M : CochainComplex (Systems D l E) ℤ) (p : ℤ),
          (roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f
              (p + 1) ≫
              (roosχ ((PointSystemTransport.transportedComplexSections D l E r).obj M) p).hom =
            (roosχ ((PointSystemTransport.complexSections D l E).obj M) p).hom ≫
              biprod.map
                ((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f p)
                ((roosPmap ((PointSystemTransport.chainTransport D l E hl r hr).app M)).f
                  (p + 1))) ∧
        (∀ M : CochainComplex (Systems D l E) ℤ,
          roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M) ≫
              κT.inv.app ((U D l E).obj ((G D l E r).obj M)) =
            κT.inv.app ((U D l E).obj M) ≫
              (NatTrans.mapHomologicalComplex σ (.up ℤ)).app
                (roosF.obj ((U D l E).obj M)) ≫
              (T D l E).map (κF.hom.app M)) ∧
        (∃ (A B : DerivedCategory (Ambient D l E) ⥤
              DerivedCategory (ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)))
          (eA : DerivedCategory.Q ⋙ A ≅ T D l E ⋙ DerivedCategory.Q)
          (eB : DerivedCategory.Q ⋙ B ≅
            (F D l E r ⋙ pointRestrictionSections l E D.k none).mapHomologicalComplex
              (.up ℤ) ⋙ DerivedCategory.Q)
          (τ : A ⟶ B),
          ∀ K : CochainComplex (Ambient D l E) ℤ,
            τ.app (DerivedCategory.Q.obj K) ≫ eB.hom.app K =
              eA.hom.app K ≫ DerivedCategory.Q.map
                ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app K)) ∧
        ∃ η : DerivedCategory.Q ⋙ CoefTower.totalLimit (Scalars.{t, u} l E) ≅
            roosF (A := ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) ⋙ DerivedCategory.Q,
          (∀ V : CochainComplex
              (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) ℤ,
            (lim : (ℕᵒᵖ ⥤ ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)) ⥤
                ModuleCat.{max u (t + 1)} (Scalars.{t, u} l E)).rightDerivedFunctorUnitQ V ≫
                η.hom.app V =
              DerivedCategory.Q.map
                ((limit.isoLimitCone
                  ⟨HomologicalComplex.coneOfHasLimitEval V.asFunctor,
                    HomologicalComplex.isLimitConeOfHasLimitEval V.asFunctor⟩).inv ≫ roosι V)) ∧
          (∀ M : CochainComplex (Systems D l E) ℤ,
            (CoefTower.totalLimit (Scalars.{t, u} l E)).map
                ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.inv.app M) ≫
              (CoefTower.totalLimit (Scalars.{t, u} l E)).map
                ((PointSystemTransport.derivedTransport D l E hl r hr).app
                  (DerivedCategory.Q.obj M)) ≫
              (CoefTower.totalLimit (Scalars.{t, u} l E)).map
                ((PointSystemTransport.pull D l E r ⋙ PointSystemTransport.sections D l E)
                  |>.mapDerivedCategoryFactors.hom.app M) ≫
                η.hom.app ((PointSystemTransport.transportedComplexSections D l E r).obj M) =
              η.hom.app ((PointSystemTransport.complexSections D l E).obj M) ≫
                DerivedCategory.Q.map
                  (roosF.map ((PointSystemTransport.chainTransport D l E hl r hr).app M))) := by
  let H := (point_automorphism_restriction_natural l E D hl
    (PointSystemTransport.pointPower D r).hom none).2.2
  let σ := H.choose
  have hσ := H.choose_spec.1
  have hσD := H.choose_spec.2
  have c : PointSystemNormalizedComparison.Data D l E r := Classical.choice
    (PointSystemNormalizedComparison.point_system_normalized_comparison_data D l E hl r hr)
  let κT := sectionsRoosComparison D l E r c
  let κF := inverseImageRoosComparison D l E r c
  have hκT := sectionsRoosComparison_coordinates D l E r c
  have hκF := inverseImageRoosComparison_coordinates D l E r c
  refine ⟨σ, hσ, ?_⟩
  refine ⟨κT, κF, ?_⟩
  refine ⟨hκT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hσD, ?_⟩
  · intro M p n W
    constructor
    · exact sheaf_hom_heq_of_identity_comp
        (((c.coefficient.hom.app M).f p).app (op n)) _ _ (hκF M p n).1 (op W)
        (c.coefficient_sections M p n W)
    · exact sheaf_hom_heq_of_identity_comp
        (((c.coefficient.hom.app M).f (p + 1)).app (op n)) _ _ (hκF M p n).2 (op W)
        (c.coefficient_sections M (p + 1) n W)
  · unfold PointSystemTransport.chainTransport
    exact (PointSystemTransport.chainTransport_existsUnique D l E hl r hr).exists.choose_spec
  · intro V W f hf
    have := hf
    let : HasExactLimitsOfShape (Discrete ℕ) (Ambient D l E) :=
      (PointSystemNormalizedComparison.exact_products D l E).2.2.2.2.2.2.1
    exact roos_map_quasiIso f
  · intro V W f hf
    have := hf
    exact roos_map_quasiIso f
  · intro M
    exact roosU_natural _
  · intro M p
    exact roosF_map_χ _ p
  · intro M
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        exact @restriction_square
          (PointSystemNormalizedComparison.A D l E) _
          (PointSystemNormalizedComparison.ambientAbelian D l E) _
          (ModuleCat.{max u (t + 1)} (pointRestrictionScalars.{t, u} l E none)) _ _ _
          (pointRestrictionSections l E D.k none)
          (PointSystemNormalizedComparison.tAdditive D l E)
          (F D l E r) (PointSystemNormalizedComparison.fAdditive D l E r)
          σ κT hκT ((U D l E).obj M) ((U D l E).obj ((G D l E r).obj M))
          (c.coefficient.app M) ((PointSystemTransport.chainTransport D l E hl r hr).app M)
          (level_transport D l E hl r hr c σ hσ M) (κF.hom.app M) (hκF M)
  · obtain ⟨η, hη⟩ := normalized_scalar (Scalars.{t, u} l E)
    refine ⟨η, hη, ?_⟩
    intro M
    have h := (PointSystemTransport.point_system_transport_descent
      D l E hl r hr).2.exists.choose_spec.1 M
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        unfold PointSystemTransport.derivedTransport
        exact normalized_transport _ _ _ η
          ((PointSystemTransport.sections D l E).mapDerivedCategoryFactors.app M)
          ((PointSystemTransport.pull D l E r ⋙ PointSystemTransport.sections D l E)
            |>.mapDerivedCategoryFactors.app M)
          _ ((PointSystemTransport.chainTransport D l E hl r hr).app M) h

end WeilConjectures.PointRestrictionWholeRoos


