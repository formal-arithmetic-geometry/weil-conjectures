module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Data.PNat.Basic
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Simultaneous cofinal quotient models of K-flat sheaf complexes

Source: Stacks Project, sites-cohomology.tex, Tags 0G7E and 0D6D;
sites-modules.tex, Tags 03EK, 03CY and 05V4.
(blueprint: lem-sp-cofinal-quotient-kflat-bisystem).

The ordinary scalar extension uses the scalar-first convention: the paper's
`(p ⊗ x) ⊗ y` is written `y ⊗ (x ⊗ p)`. Natural transformations of the ordinary
functors give the semilinear chain maps by `NatTrans.mapHomologicalComplex`.
The two helpers below construct the comparison from the recorded normalization,
including the necessary transport from a composite ring map to the given delta.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v r w

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.SuccessiveDerivedQuotient

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [hD : ∀ A : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules A)]

/-- The prescribed quotient cancellation, with its actual target coefficient map.
Source: Stacks 03EK and 0D6D (blueprint: lem-sp-cofinal-quotient-kflat-bisystem).
This is the existing normalized ordinary comparison followed by equality transport;
it does not choose a new isomorphism. -/
noncomputable def cofinalQuotientTheta
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (β : R ⟶ S) (q : S ⟶ T) (δ : R ⟶ T) (h : β ≫ q = δ) :
    (p β).ordinary ⋙ (p q).ordinary ≅ (p δ).ordinary :=
  ν.ordinary β q ≪≫ eqToIso (congrArg (fun a ↦ (p a).ordinary) h)

/-- The actual chain isomorphism induced by quotient cancellation in every degree.
Source: Stacks 03EK and 0D6D (blueprint: lem-sp-cofinal-quotient-kflat-bisystem).
The functorial lift makes this natural in every chain map, with no quasi-isomorphism
condition and no boundedness condition. -/
noncomputable def cofinalQuotientChainTheta
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (β : R ⟶ S) (q : S ⟶ T) (δ : R ⟶ T) (h : β ≫ q = δ) :
    (p β).ordinary.mapHomologicalComplex (.up ℤ) ⋙
      (p q).ordinary.mapHomologicalComplex (.up ℤ) ≅
        (p δ).ordinary.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (cofinalQuotientTheta p ν β q δ h) (.up ℤ)

/-- The target-valued normalized derived cancellation for every derived object.
Source: Stacks 0D6D (blueprint: lem-sp-cofinal-quotient-kflat-bisystem).
Its natural-isomorphism type includes naturality in every derived morphism; the
normalization fixes its computation and coherence independently of representatives. -/
noncomputable def cofinalQuotientDerivedTheta
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (β : R ⟶ S) (q : S ⟶ T) (δ : R ⟶ T) (h : β ≫ q = δ) :
    (p β).derived ⋙ (p q).derived ≅ (p δ).derived :=
  ν.derived β q ≪≫ eqToIso (congrArg (fun a ↦ (p a).derived) h)

private theorem theta_hom
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (x : S.obj.obj U) (y : T.obj.obj U)
    (z : M.val.obj U) :
    ((cofinalQuotientTheta p ν a b c h).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U y
        (sectionTensor (p a) M U x z)) =
      sectionTensor (p c) M U ((b.hom.app U).hom x * y) z := by
  subst c
  simpa only [cofinalQuotientTheta, eqToIso_refl, Iso.trans_refl] using
    ν.ordinary_hom a b M U z x y

private theorem theta_inv
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (y : T.obj.obj U) (z : M.val.obj U) :
    ((cofinalQuotientTheta p ν a b c h).inv.app M).val.app U
      (sectionTensor (p c) M U y z) =
      sectionTensor (p b) ((p a).ordinary.obj M) U y
        (sectionTensor (p a) M U 1 z) := by
  subst c
  simpa only [cofinalQuotientTheta, eqToIso_refl, Iso.trans_refl] using
    ν.ordinary_inv a b M U z y

-- The scalar-extension unit followed by normalized tensor cancellation.
private noncomputable def coefficientStep
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    (p a).ordinary ⟶ (p c).ordinary ⋙ restriction b :=
  Functor.whiskerLeft (p a).ordinary (ν.ordinaryAdjunction b).unit ≫
    Functor.whiskerRight (cofinalQuotientTheta p ν a b c h).hom (restriction b)

private theorem coefficientStep_sections
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (x : S.obj.obj U) (z : M.val.obj U) :
    ((coefficientStep p ν a b c h).app M).val.app U
      (sectionTensor (p a) M U x z) =
      sectionTensor (p c) M U ((b.hom.app U).hom x) z := by
  change ((cofinalQuotientTheta p ν a b c h).hom.app M).val.app U
    (((ν.ordinaryAdjunction b).unit.app _).val.app U
      (sectionTensor (p a) M U x z)) = _
  rw [ν.ordinary_unit, theta_hom, mul_one]

attribute [irreducible] coefficientStep

-- Pure tensors generate the associated sheaf, also after restricting scalars.
private theorem restricted_tensor_ext
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    {A R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (c : A ⟶ S)
    (M : Modules R) (H : Modules A)
    (f g : (restriction c).obj ((p a).ordinary.obj M) ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (sectionTensor (p a) M U s x) =
        g.val.app U (sectionTensor (p a) M U s x)) : f = g := by
  let j := (restriction c).map (eqToHom ((p a).obj_eq M).symm)
  apply (cancel_epi j).mp
  apply (toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ H.isSheaf
  ext U z
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (a.hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s x => exact h U s x

-- The two adjunctions reduce equality on an iterated extension to its unit tensors.
private theorem double_tensor_ext
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (M : Modules R) (H : Modules T)
    (f g : (p b).ordinary.obj ((p a).ordinary.obj M) ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (x : S.obj.obj U) (y : T.obj.obj U) (z : M.val.obj U),
      f.val.app U (sectionTensor (p b) ((p a).ordinary.obj M) U y
        (sectionTensor (p a) M U x z)) =
      g.val.app U (sectionTensor (p b) ((p a).ordinary.obj M) U y
        (sectionTensor (p a) M U x z))) : f = g := by
  apply ((ν.ordinaryAdjunction b).homEquiv _ _).injective
  apply ((ν.ordinaryAdjunction a).homEquiv _ _).injective
  ext U z
  change f.val.app U (((ν.ordinaryAdjunction b).unit.app _).val.app U
    (((ν.ordinaryAdjunction a).unit.app M).val.app U z)) =
    g.val.app U (((ν.ordinaryAdjunction b).unit.app _).val.app U
      (((ν.ordinaryAdjunction a).unit.app M).val.app U z))
  rw [ν.ordinary_unit, ν.ordinary_unit]
  exact h U 1 1 z

private theorem first_transition_sections
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S S' T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (a' : R ⟶ S') (b : S ⟶ S') (q : S ⟶ T) (q' : S' ⟶ T)
    (c : R ⟶ T) (h : a ≫ q = c) (h' : a' ≫ q' = c) (hb : b ≫ q' = q)
    (M : Modules R) (U : Cᵒᵖ) (x : S.obj.obj U) (y : T.obj.obj U)
    (z : M.val.obj U) :
    (((cofinalQuotientTheta p ν a q c h).hom ≫
      (cofinalQuotientTheta p ν a' q' c h').inv).app M).val.app U
      (sectionTensor (p q) ((p a).ordinary.obj M) U y
        (sectionTensor (p a) M U x z)) =
      sectionTensor (p q') ((p a').ordinary.obj M) U y
        (sectionTensor (p a') M U ((b.hom.app U).hom x) z) := by
  have he : (q'.hom.app U).hom ((b.hom.app U).hom x) = (q.hom.app U).hom x :=
    congrArg (fun f : S ⟶ T ↦ (f.hom.app U).hom x) hb
  change ((cofinalQuotientTheta p ν a' q' c h').inv.app M).val.app U
    (((cofinalQuotientTheta p ν a q c h).hom.app M).val.app U _) = _
  rw [theta_hom, ← he, ← theta_hom p ν a' q' c h']
  exact congrArg (fun f ↦ f.val.app U
    (sectionTensor (p q') ((p a').ordinary.obj M) U y
      (sectionTensor (p a') M U ((b.hom.app U).hom x) z)))
    ((cofinalQuotientTheta p ν a' q' c h').hom_inv_id_app M)

private theorem second_transition_square
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (q : S ⟶ T) (q' : S ⟶ T') (d : T ⟶ T')
    (c : R ⟶ T) (c' : R ⟶ T') (h : a ≫ q = c) (h' : a ≫ q' = c')
    (hd : q ≫ d = q') (hc : c ≫ d = c') (M : Modules R) :
    (coefficientStep p ν q d q' hd).app ((p a).ordinary.obj M) ≫
      (restriction d).map ((cofinalQuotientTheta p ν a q' c' h').hom.app M) =
    (cofinalQuotientTheta p ν a q c h).hom.app M ≫
      (coefficientStep p ν c d c' hc).app M := by
  apply double_tensor_ext p ν a q M _
  intro U x y z
  change ((cofinalQuotientTheta p ν a q' c' h').hom.app M).val.app U
    (((coefficientStep p ν q d q' hd).app ((p a).ordinary.obj M)).val.app U _) =
    ((coefficientStep p ν c d c' hc).app M).val.app U
      (((cofinalQuotientTheta p ν a q c h).hom.app M).val.app U _)
  rw [coefficientStep_sections, theta_hom, theta_hom, coefficientStep_sections, map_mul]
  have he : (d.hom.app U).hom ((q.hom.app U).hom x) = (q'.hom.app U).hom x :=
    congrArg (fun f : S ⟶ T' ↦ (f.hom.app U).hom x) hd
  rw [he]

private noncomputable def restrictedStep
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c) :
    (p a).ordinary ⋙ restriction a ⟶ (p c).ordinary ⋙ restriction c :=
  Functor.whiskerRight (coefficientStep p ν a b c h) (restriction a) ≫
    Functor.whiskerLeft (p c).ordinary ((ν.restrictionComp a b).hom ≫
      eqToHom (congrArg (fun f ↦ restriction f) h))

private theorem restrictedStep_sections
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (x : S.obj.obj U) (z : M.val.obj U) :
    ((restrictedStep p ν a b c h).app M).val.app U
      (sectionTensor (p a) M U x z) =
      sectionTensor (p c) M U ((b.hom.app U).hom x) z := by
  subst c
  change ((ν.restrictionComp a b).hom.app _).val.app U
    (((coefficientStep p ν a b (a ≫ b) rfl).app M).val.app U _) = _
  rw [ν.restrictionComp_sections, coefficientStep_sections]

private theorem restrictedStep_apply
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (x : ((p a).ordinary.obj M).val.obj U) :
    ((restrictedStep p ν a b c h).app M).val.app U x =
      ((coefficientStep p ν a b c h).app M).val.app U x := by
  subst c
  dsimp only [restrictedStep, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, eqToHom_refl, Category.comp_id]
  exact ν.restrictionComp_sections a b _ U _

private theorem representative_transport
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P)
    (hf : ∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) :
    (ν.derived a b).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      eqToHom (congrArg (fun f ↦ (p f).derived.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) h) ≫
      (p c).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p b).counit.app (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (cofinalQuotientTheta p ν a b c h)
          (.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj P)) := by
  subst c
  simpa only [eqToHom_refl, Category.id_comp, cofinalQuotientTheta,
    eqToIso_refl, Iso.trans_refl] using ν.representative a b P hP hf

-- Keep the restricted module structure in the type throughout rewriting.
private noncomputable def restrictedTensor
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (z : M.val.obj U) :
    (((p a).ordinary ⋙ restriction a).obj M).val.obj U :=
  sectionTensor (p a) M U s z

private theorem restrictedTensor_step
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (z : M.val.obj U) :
    ((restrictedStep p ν a b c h).app M).val.app U (restrictedTensor p a M U s z) =
      restrictedTensor p c M U ((b.hom.app U).hom s) z :=
  restrictedStep_sections p ν a b c h M U s z

private theorem restrictedTensor_ext
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M H : Modules R)
    (f g : ((p a).ordinary ⋙ restriction a).obj M ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (z : M.val.obj U),
      f.val.app U (restrictedTensor p a M U s z) =
        g.val.app U (restrictedTensor p a M U s z)) : f = g :=
  restricted_tensor_ext p a a M H f g h

attribute [irreducible] restrictedStep restrictedTensor

private theorem coefficientStep_comp_sections
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (a' : R ⟶ T) (a'' : R ⟶ V)
    (b : S ⟶ T) (d : T ⟶ V) (c : S ⟶ V)
    (h : a ≫ b = a') (h' : a' ≫ d = a'') (h'' : a ≫ c = a'') (hb : b ≫ d = c)
    (M : Modules R) (U : Cᵒᵖ) (x : ((p a).ordinary.obj M).val.obj U) :
    ((coefficientStep p ν a' d a'' h').app M).val.app U
      (((coefficientStep p ν a b a' h).app M).val.app U x) =
      ((coefficientStep p ν a c a'' h'').app M).val.app U x := by
  have he : (restrictedStep p ν a b a' h).app M ≫
      (restrictedStep p ν a' d a'' h').app M =
      (restrictedStep p ν a c a'' h'').app M := by
    apply restrictedTensor_ext p a M _
    intro U s z
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [restrictedTensor_step, restrictedTensor_step, restrictedTensor_step]
    exact congrArg (fun y ↦ restrictedTensor p a'' M U y z)
      (congrArg (fun f : S ⟶ V ↦ (f.hom.app U).hom s) hb)
  have hv := congrArg (fun f ↦ f.val.app U x) he
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, restrictedStep_apply] using hv

private theorem coefficientStep_id_sections
    (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
    (ν : Normalization p) {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ S) (h : a ≫ b = a) (hb : b = 𝟙 S)
    (M : Modules R) (U : Cᵒᵖ) (x : ((p a).ordinary.obj M).val.obj U) :
    ((coefficientStep p ν a b a h).app M).val.app U x = x := by
  have he : (restrictedStep p ν a b a h).app M = 𝟙 _ := by
    apply restrictedTensor_ext p a M _
    intro U s z
    rw [restrictedTensor_step, hb]
    rfl
  have hv := congrArg (fun f ↦ f.val.app U x) he
  change ((restrictedStep p ν a b a h).app M).val.app U x = x at hv
  simpa only [restrictedStep_apply] using hv

/-- Simultaneous K-flat quotient models and both-index normalized cancellation.
Source: Stacks 0G7E, 0D6D, 03EK, 03CY and 05V4
(blueprint: lem-sp-cofinal-quotient-kflat-bisystem).

Proof: (1) Apply lem-pur-kflat-change-of-rings-all-independent to beta_N and delta_j.
Exact faithful restriction and balanced tensor cancellation prove this for every
K-flat complex, without flat terms. (2) Define the two transitions on pure tensors
by applying b or d to the coefficient. The beta and delta compatibility equations
make them balanced; restriction and the differential commute with these formulas.
(3) Cancellation sends y tensor (x tensor z) to q(x)y tensor z; its inverse sends
y tensor z to y tensor (1 tensor z). R-balancing uses beta followed by q = delta,
and B-balancing uses multiplicativity of q. Sheafification extends the balanced
maps uniquely, and their composites are identities on the generating tensors.
(4) For the first index use q_Mj b_NM = q_Nj, and for the second use d_jk q_Nj = q_Nk.
The mixed square has common value d(y) tensor (b(x) tensor z); naturality in a
chain map follows by applying it to z. The same tensor calculations prove identity
and composition laws. (5) For a flat-term K-flat representative use the canonical
computation counits of lem-pur-derived-change-of-rings. The representative equation
of lem-sfb-successive-derived-quotient-normalization identifies localization of the
chain cancellation with its target-valued derived comparison. Its naturality and
coherence give independence of representatives and every further reduction in both
indices. No coefficient-map flatness, boundedness or completeness is used. -/
theorem cofinal_quotient_kflat_bisystem
    (R : Sheaf J CommRingCat.{r}) (B D : ℕ+ᵒᵖ ⥤ Sheaf J CommRingCat.{r})
    (e : ℕ+) (β : ∀ N : ℕ+, R ⟶ B.obj (op N))
    (δ : ∀ j : ℕ+, R ⟶ D.obj (op j))
    (q : ∀ (N j : ℕ+) (_h : j ≤ e * N), B.obj (op N) ⟶ D.obj (op j))
    (hq : ∀ (N j : ℕ+) (h : j ≤ e * N), β N ≫ q N j h = δ j)
    (hβ : ∀ (N M : ℕ+) (h : M ≤ N), β N ≫ B.map (homOfLE h).op = β M)
    (hδ : ∀ (j k : ℕ+) (h : k ≤ j), δ j ≫ D.map (homOfLE h).op = δ k)
    (hqb : ∀ (N M j : ℕ+) (h : M ≤ N) (hN : j ≤ e * N) (hM : j ≤ e * M),
      B.map (homOfLE h).op ≫ q M j hM = q N j hN)
    (hqd : ∀ (N j k : ℕ+) (h : k ≤ j) (hj : j ≤ e * N) (hk : k ≤ e * N),
      q N j hj ≫ D.map (homOfLE h).op = q N k hk) :
    ∃ (p : ∀ {A A' : Sheaf J CommRingCat.{r}} (a : A ⟶ A'), Presentation a)
      (ν : Normalization p),
    (∀ (P : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (∀ N : ℕ+, CochainComplex.IsKFlatIndependentCoefficients
        (((p (β N)).ordinary.mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ j : ℕ+, CochainComplex.IsKFlatIndependentCoefficients
        (((p (δ j)).ordinary.mapHomologicalComplex (.up ℤ)).obj P))) ∧
    ∃ (b : ∀ (N M : ℕ+) (h : M ≤ N),
        (p (β N)).ordinary ⟶ (p (β M)).ordinary ⋙ restriction (B.map (homOfLE h).op))
      (d : ∀ (j k : ℕ+) (h : k ≤ j),
        (p (δ j)).ordinary ⟶ (p (δ k)).ordinary ⋙ restriction (D.map (homOfLE h).op))
      (s : ∀ (N M j : ℕ+) (_h : M ≤ N) (hN : j ≤ e * N) (hM : j ≤ e * M),
        (p (β N)).ordinary ⋙ (p (q N j hN)).ordinary ⟶
          (p (β M)).ordinary ⋙ (p (q M j hM)).ordinary)
      (t : ∀ (N j k : ℕ+) (h : k ≤ j) (hj : j ≤ e * N) (hk : k ≤ e * N),
        (p (β N)).ordinary ⋙ (p (q N j hj)).ordinary ⟶
          ((p (β N)).ordinary ⋙ (p (q N k hk)).ordinary) ⋙
            restriction (D.map (homOfLE h).op)),
    (∀ (N M : ℕ+) (h : M ≤ N) (A : Modules R) (U : Cᵒᵖ)
      (x : (B.obj (op N)).obj.obj U) (z : A.val.obj U),
      ((b N M h).app A).val.app U (sectionTensor (p (β N)) A U x z) =
        sectionTensor (p (β M)) A U ((B.map (homOfLE h).op).hom.app U x) z) ∧
    (∀ (j k : ℕ+) (h : k ≤ j) (A : Modules R) (U : Cᵒᵖ)
      (y : (D.obj (op j)).obj.obj U) (z : A.val.obj U),
      ((d j k h).app A).val.app U (sectionTensor (p (δ j)) A U y z) =
        sectionTensor (p (δ k)) A U ((D.map (homOfLE h).op).hom.app U y) z) ∧
    (∀ (N j : ℕ+) (h : j ≤ e * N) (A : Modules R) (U : Cᵒᵖ)
      (x : (B.obj (op N)).obj.obj U) (y : (D.obj (op j)).obj.obj U) (z : A.val.obj U),
      ((cofinalQuotientTheta p ν (β N) (q N j h) (δ j) (hq N j h)).hom.app A).val.app U
          (sectionTensor (p (q N j h)) ((p (β N)).ordinary.obj A) U y
            (sectionTensor (p (β N)) A U x z)) =
        sectionTensor (p (δ j)) A U ((q N j h).hom.app U x * y) z) ∧
    (∀ (N j : ℕ+) (h : j ≤ e * N) (A : Modules R) (U : Cᵒᵖ)
      (y : (D.obj (op j)).obj.obj U) (z : A.val.obj U),
      ((cofinalQuotientTheta p ν (β N) (q N j h) (δ j) (hq N j h)).inv.app A).val.app U
          (sectionTensor (p (δ j)) A U y z) =
        sectionTensor (p (q N j h)) ((p (β N)).ordinary.obj A) U y
          (sectionTensor (p (β N)) A U 1 z)) ∧
    (∀ (N M j : ℕ+) (h : M ≤ N) (hN : j ≤ e * N) (hM : j ≤ e * M)
      (A : Modules R) (U : Cᵒᵖ) (x : (B.obj (op N)).obj.obj U)
      (y : (D.obj (op j)).obj.obj U) (z : A.val.obj U),
      ((s N M j h hN hM).app A).val.app U
          (sectionTensor (p (q N j hN)) ((p (β N)).ordinary.obj A) U y
            (sectionTensor (p (β N)) A U x z)) =
        sectionTensor (p (q M j hM)) ((p (β M)).ordinary.obj A) U y
          (sectionTensor (p (β M)) A U ((B.map (homOfLE h).op).hom.app U x) z)) ∧
    (∀ (N j k : ℕ+) (h : k ≤ j) (hj : j ≤ e * N) (hk : k ≤ e * N)
      (A : Modules R) (U : Cᵒᵖ) (y : (D.obj (op j)).obj.obj U)
      (z : ((p (β N)).ordinary.obj A).val.obj U),
      ((t N j k h hj hk).app A).val.app U
          (sectionTensor (p (q N j hj)) ((p (β N)).ordinary.obj A) U y z) =
        sectionTensor (p (q N k hk)) ((p (β N)).ordinary.obj A) U
          ((D.map (homOfLE h).op).hom.app U y) z) ∧
    (∀ (N M j : ℕ+) (h : M ≤ N) (hN : j ≤ e * N) (hM : j ≤ e * M) (A : Modules R),
      (s N M j h hN hM).app A ≫
          (cofinalQuotientTheta p ν (β M) (q M j hM) (δ j) (hq M j hM)).hom.app A =
        (cofinalQuotientTheta p ν (β N) (q N j hN) (δ j) (hq N j hN)).hom.app A) ∧
    (∀ (N j k : ℕ+) (h : k ≤ j) (hj : j ≤ e * N) (hk : k ≤ e * N) (A : Modules R),
      (t N j k h hj hk).app A ≫
          (restriction (D.map (homOfLE h).op)).map
            ((cofinalQuotientTheta p ν (β N) (q N k hk) (δ k) (hq N k hk)).hom.app A) =
        (cofinalQuotientTheta p ν (β N) (q N j hj) (δ j) (hq N j hj)).hom.app A ≫
          (d j k h).app A) ∧
    (∀ (N M L : ℕ+) (hNM : M ≤ N) (hML : L ≤ M) (A : Modules R) (U : Cᵒᵖ)
      (x : ((p (β N)).ordinary.obj A).val.obj U),
      ((b M L hML).app A).val.app U (((b N M hNM).app A).val.app U x) =
        ((b N L (hML.trans hNM)).app A).val.app U x) ∧
    (∀ (N : ℕ+) (A : Modules R) (U : Cᵒᵖ)
      (x : ((p (β N)).ordinary.obj A).val.obj U),
      ((b N N le_rfl).app A).val.app U x = x) ∧
    (∀ (j k l : ℕ+) (hjk : k ≤ j) (hkl : l ≤ k) (A : Modules R) (U : Cᵒᵖ)
      (x : ((p (δ j)).ordinary.obj A).val.obj U),
      ((d k l hkl).app A).val.app U (((d j k hjk).app A).val.app U x) =
        ((d j l (hkl.trans hjk)).app A).val.app U x) ∧
    (∀ (j : ℕ+) (A : Modules R) (U : Cᵒᵖ)
      (x : ((p (δ j)).ordinary.obj A).val.obj U),
      ((d j j le_rfl).app A).val.app U x = x) ∧
    (∀ (N M j k : ℕ+) (hNM : M ≤ N) (hjk : k ≤ j)
      (hNj : j ≤ e * N) (hMj : j ≤ e * M) (hNk : k ≤ e * N) (hMk : k ≤ e * M)
      (A : Modules R),
      (s N M j hNM hNj hMj).app A ≫ (t M j k hjk hMj hMk).app A =
        (t N j k hjk hNj hNk).app A ≫
          (restriction (D.map (homOfLE hjk).op)).map ((s N M k hNM hNk hMk).app A)) ∧
    (∀ (N j : ℕ+) (h : j ≤ e * N) (P P' : CochainComplex (Modules R) ℤ) (f : P ⟶ P'),
      (((p (β N)).ordinary.mapHomologicalComplex (.up ℤ) ⋙
          (p (q N j h)).ordinary.mapHomologicalComplex (.up ℤ)).map f) ≫
          (cofinalQuotientChainTheta p ν (β N) (q N j h) (δ j) (hq N j h)).hom.app P' =
        (cofinalQuotientChainTheta p ν (β N) (q N j h) (δ j) (hq N j h)).hom.app P ≫
          ((p (δ j)).ordinary.mapHomologicalComplex (.up ℤ)).map f) ∧
    (∀ (N j : ℕ+) (h : j ≤ e * N) (P : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients P →
      (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
      ((ν.derived (β N) (q N j h)).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) ≫
          eqToHom (congrArg (fun a ↦ (p a).derived.obj
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P))) (hq N j h)) ≫
          (p (δ j)).counit.app ((HomotopyCategory.quotient _ _).obj P) =
        (p (q N j h)).derived.map
            ((p (β N)).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
          (p (q N j h)).counit.app
            (((p (β N)).ordinary.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ _).obj P)) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso
              (cofinalQuotientTheta p ν (β N) (q N j h) (δ j) (hq N j h)) (.up ℤ)).hom.app
                ((HomotopyCategory.quotient _ _).obj P))) := by
  classical
  obtain ⟨p, ⟨ν⟩⟩ := successive_derived_quotient_normalization (J := J)
  refine ⟨p, ν, ?_, ?_⟩
  · intro P hP
    constructor
    · intro N
      exact changeOfRings_isKFlat_independentCoefficients (β N) P
        (p (β N)).ordinary (p (β N)).obj_eq (p (β N)).map_eq hP
    · intro j
      exact changeOfRings_isKFlat_independentCoefficients (δ j) P
        (p (δ j)).ordinary (p (δ j)).obj_eq (p (δ j)).map_eq hP
  · let b := fun (N M : ℕ+) (h : M ≤ N) ↦
      coefficientStep p ν (β N) (B.map (homOfLE h).op) (β M) (hβ N M h)
    let d := fun (j k : ℕ+) (h : k ≤ j) ↦
      coefficientStep p ν (δ j) (D.map (homOfLE h).op) (δ k) (hδ j k h)
    let s := fun (N M j : ℕ+) (_h : M ≤ N) (hN : j ≤ e * N) (hM : j ≤ e * M) ↦
      (cofinalQuotientTheta p ν (β N) (q N j hN) (δ j) (hq N j hN)).hom ≫
        (cofinalQuotientTheta p ν (β M) (q M j hM) (δ j) (hq M j hM)).inv
    let t := fun (N j k : ℕ+) (h : k ≤ j) (hj : j ≤ e * N) (hk : k ≤ e * N) ↦
      Functor.whiskerLeft (p (β N)).ordinary
        (coefficientStep p ν (q N j hj) (D.map (homOfLE h).op) (q N k hk)
          (hqd N j k h hj hk))
    refine ⟨b, d, s, t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro N M h A U x z
      exact coefficientStep_sections p ν (β N) (B.map (homOfLE h).op)
        (β M) (hβ N M h) A U x z
    · intro j k h A U y z
      exact coefficientStep_sections p ν (δ j) (D.map (homOfLE h).op)
        (δ k) (hδ j k h) A U y z
    · intro N j h A U x y z
      exact theta_hom p ν _ _ _ _ A U x y z
    · intro N j h A U y z
      exact theta_inv p ν _ _ _ _ A U y z
    · intro N M j h hN hM A U x y z
      exact first_transition_sections p ν (β N) (β M) (B.map (homOfLE h).op)
        (q N j hN) (q M j hM) (δ j) (hq N j hN) (hq M j hM)
        (hqb N M j h hN hM) A U x y z
    · intro N j k h hj hk A U y z
      exact coefficientStep_sections p ν (q N j hj) (D.map (homOfLE h).op)
        (q N k hk) (hqd N j k h hj hk) ((p (β N)).ordinary.obj A) U y z
    · intro N M j h hN hM A
      dsimp only [s, NatTrans.comp_app]
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    · intro N j k h hj hk A
      exact second_transition_square p ν (β N) (q N j hj) (q N k hk)
        (D.map (homOfLE h).op) (δ j) (δ k) (hq N j hj) (hq N k hk)
        (hqd N j k h hj hk) (hδ j k h) A
    · intro N M L hNM hML A U x
      apply coefficientStep_comp_sections p ν (β N) (β M) (β L)
        (B.map (homOfLE hNM).op) (B.map (homOfLE hML).op)
        (B.map (homOfLE (hML.trans hNM)).op)
        (hβ N M hNM) (hβ M L hML) (hβ N L (hML.trans hNM)) _ A U x
      rw [← B.map_comp]
      rfl
    · intro N A U x
      exact coefficientStep_id_sections p ν (β N) (B.map (homOfLE le_rfl).op)
        (hβ N N le_rfl) (B.map_id _) A U x
    · intro j k l hjk hkl A U x
      apply coefficientStep_comp_sections p ν (δ j) (δ k) (δ l)
        (D.map (homOfLE hjk).op) (D.map (homOfLE hkl).op)
        (D.map (homOfLE (hkl.trans hjk)).op)
        (hδ j k hjk) (hδ k l hkl) (hδ j l (hkl.trans hjk)) _ A U x
      rw [← D.map_comp]
      rfl
    · intro j A U x
      exact coefficientStep_id_sections p ν (δ j) (D.map (homOfLE le_rfl).op)
        (hδ j j le_rfl) (D.map_id _) A U x
    · intro N M j k hNM hjk hNj hMj hNk hMk A
      apply double_tensor_ext p ν (β N) (q N j hNj) A _
      intro U x y z
      change ((t M j k hjk hMj hMk).app A).val.app U
        (((s N M j hNM hNj hMj).app A).val.app U _) =
        ((s N M k hNM hNk hMk).app A).val.app U
          (((t N j k hjk hNj hNk).app A).val.app U _)
      dsimp only [s, t, Functor.whiskerLeft_app]
      rw [first_transition_sections p ν _ _ _ _ _ _ _ _ (hqb N M j hNM hNj hMj)]
      erw [coefficientStep_sections p ν (q M j hMj) (D.map (homOfLE hjk).op)
        (q M k hMk) (hqd M j k hjk hMj hMk) _ U y _,
        coefficientStep_sections p ν (q N j hNj) (D.map (homOfLE hjk).op)
          (q N k hNk) (hqd N j k hjk hNj hNk) _ U y _]
      exact (first_transition_sections p ν _ _ _ _ _ _ _ _
        (hqb N M k hNM hNk hMk) A U x ((D.map (homOfLE hjk).op).hom.app U y) z).symm
    · intro N j h P P' f
      exact (cofinalQuotientChainTheta p ν (β N) (q N j h) (δ j) (hq N j h)).hom.naturality f
    · intro N j h P hP hf
      exact representative_transport p ν _ _ _ _ P hP hf

end SheafOfModules
