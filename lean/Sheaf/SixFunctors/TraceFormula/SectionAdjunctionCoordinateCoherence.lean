/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Section-coordinate coherence for adjoints of scheme module pushforward

Source: Stacks Project, Sheaves, Tags 0096–0097; Descent, Tag 03DR.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private theorem identityComparison
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    (((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
      (Modules.pushforwardComp (𝟙 A) b).symm).hom.app F) ≫
        eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b)) =
      (Adjunction.leftAdjointIdIso (adj (𝟙 A)) (Modules.pushforwardId A)).hom.app
        ((L b).obj F) := by
  have he : Modules.pushforwardComp (𝟙 A) b =
      Functor.isoWhiskerRight (Modules.pushforwardId A) (Modules.pushforward b) ≪≫
        Functor.leftUnitor (Modules.pushforward b) := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_comp_id (adj b) (adj (𝟙 A))
    (Modules.pushforwardComp (𝟙 A) b) (Modules.pushforwardId A) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hc
  erw [Category.comp_id] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

/-- The unit-normalized identity comparison cancels the unit on global sections.
Source: Stacks, Tag 03DR; the conjugate-isomorphism unit equation
(blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem unitId_sections {A : Scheme.{u}} (I : A.Modules ⥤ A.Modules)
    (adj : I ⊣ Modules.pushforward (𝟙 A)) (M : A.Modules) :
    (adj.unit.app M).app ⊤ ≫
      ((Adjunction.leftAdjointIdIso adj (Modules.pushforwardId A)).hom.app M).app ⊤ = 𝟙 _ := by
  have hu := unit_conjugateEquiv_symm Adjunction.id adj (Modules.pushforwardId A).inv M
  change (adj.unit.app M).app ⊤ ≫
    (((conjugateEquiv Adjunction.id adj).symm (Modules.pushforwardId A).inv).app M).app ⊤ = _
  have hs := congrArg (fun φ ↦ φ.app ⊤) hu
  change (𝟙 Γ(M, ⊤) ≫ 𝟙 _) = (adj.unit.app M).app ⊤ ≫
    (((conjugateEquiv Adjunction.id adj).symm (Modules.pushforwardId A).inv).app M).app ⊤ at hs
  erw [Category.id_comp] at hs
  exact hs.symm

/-- The global-section unit for an arbitrary left adjoint of scheme Modules.pushforward.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private def sectionsUnitOfAdjunction {A B : Scheme.{u}} (f : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ Modules.pushforward f) (G : B.Modules) :
    Γ(G, ⊤) ⟶ Γ(L.obj G, ⊤) :=
  (adj.unit.app G).app ⊤ ≫ (L.obj G).presheaf.map (homOfLE f.preimage_top.ge).op

/-- Identity restrictions for any family of left adjoints, before specializing to tensors.
Source: Stacks, Tag 03DR (blueprint: lem-sc-etale-qcoherent-presheaf-functorial). -/
private theorem identitySections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    sectionsUnitOfAdjunction (𝟙 A) (L (𝟙 A)) (adj (𝟙 A)) ((L b).obj F) ≫
      ((((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
        (Modules.pushforwardComp (𝟙 A) b).symm).hom.app F).app ⊤) ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b))).app ⊤ = 𝟙 _ := by
  have hc := identityComparison L adj b F
  have hs := unitId_sections (L (𝟙 A)) (adj (𝟙 A)) ((L b).obj F)
  have hi : homOfLE (𝟙 A : A ⟶ A).preimage_top.ge = 𝟙 (⊤ : TopologicalSpace.Opens A) := rfl
  unfold sectionsUnitOfAdjunction
  erw [hi, op_id, ((L (𝟙 A)).obj ((L b).obj F)).presheaf.map_id, Category.comp_id]
  have hct := congrArg (fun φ ↦ φ.app ⊤) hc
  change (((conjugateIsoEquiv (adj (𝟙 A ≫ b)) ((adj b).comp (adj (𝟙 A)))).symm
      (Modules.pushforwardComp (𝟙 A) b).symm).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b))).app ⊤ =
      ((Adjunction.leftAdjointIdIso (adj (𝟙 A)) (Modules.pushforwardId A)).hom.app
        ((L b).obj F)).app ⊤ at hct
  erw [hct]
  exact hs

private theorem identityComparisonRight
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules) :
    (((conjugateIsoEquiv (adj (b ≫ 𝟙 B)) ((adj (𝟙 B)).comp (adj b))).symm
      (Modules.pushforwardComp b (𝟙 B)).symm).hom.app F) ≫
        eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.comp_id b)) =
      (L b).map ((Adjunction.leftAdjointIdIso (adj (𝟙 B))
        (Modules.pushforwardId B)).hom.app F) := by
  have he : Modules.pushforwardComp b (𝟙 B) =
      Functor.isoWhiskerLeft (Modules.pushforward b) (Modules.pushforwardId B) ≪≫
        Functor.rightUnitor (Modules.pushforward b) := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_id_comp (adj (𝟙 B)) (adj b)
    (Modules.pushforwardComp b (𝟙 B)) (Modules.pushforwardId B) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hc
  erw [Category.comp_id] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

private def compOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    L b ⋙ L a ≅ L (a ≫ b) :=
  (conjugateIsoEquiv (adj (a ≫ b)) ((adj b).comp (adj a))).symm
    (Modules.pushforwardComp a b).symm

private theorem compOfAdjunction_assoc
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    ((compOfAdjunction L adj a b).hom.app ((L c).obj F)) ≫
      (compOfAdjunction L adj (a ≫ b) c).hom.app F ≫
      eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c)) =
    (L a).map ((compOfAdjunction L adj b c).hom.app F) ≫
      (compOfAdjunction L adj a (b ≫ c)).hom.app F := by
  have he : Functor.isoWhiskerLeft (Modules.pushforward a) (Modules.pushforwardComp b c) ≪≫
      Modules.pushforwardComp a (b ≫ c) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Modules.pushforwardComp a b) (Modules.pushforward c) ≪≫
        Modules.pushforwardComp (a ≫ b) c := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (adj c) (adj b) (adj a)
    (adj (b ≫ c)) (adj (a ≫ b)) (adj (a ≫ (b ≫ c)))
    (Modules.pushforwardComp b c) (Modules.pushforwardComp a b)
    (Modules.pushforwardComp (a ≫ b) c) (Modules.pushforwardComp a (b ≫ c)) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app] at hc
  erw [Category.id_comp] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc

private theorem inverseComparison {C : Type*} [Category* C]
    {M₀ M₁ M₂ M₃ : C} (e₀₁ : M₀ ≅ M₁) (e₁₂ : M₁ ≅ M₂) (e₃₂ : M₃ ≅ M₂)
    (h : M₀ ⟶ M₃) (he : e₀₁.hom ≫ e₁₂.hom = h ≫ e₃₂.hom) :
    e₁₂.inv ≫ e₀₁.inv ≫ h = e₃₂.inv := by
  calc
    e₁₂.inv ≫ e₀₁.inv ≫ h =
        e₁₂.inv ≫ e₀₁.inv ≫ (h ≫ e₃₂.hom) ≫ e₃₂.inv := by simp
    _ = e₁₂.inv ≫ e₀₁.inv ≫ (e₀₁.hom ≫ e₁₂.hom) ≫ e₃₂.inv := by rw [he]
    _ = e₃₂.inv := by simp

private theorem inverseRightSections
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules)
    (s : Γ((L (b ≫ 𝟙 B)).obj F, ⊤)) :
    ((L b).map ((Adjunction.leftAdjointIdIso (adj (𝟙 B))
      (Modules.pushforwardId B)).hom.app F)).app ⊤
        (((compOfAdjunction L adj b (𝟙 B)).inv.app F).app ⊤ s) = s := by
  have h := identityComparisonRight L adj b F
  have hh : (compOfAdjunction L adj b (𝟙 B)).hom.app F =
      (L b).map ((Adjunction.leftAdjointIdIso (adj (𝟙 B))
        (Modules.pushforwardId B)).hom.app F) := by
    erw [eqToHom_refl, Category.comp_id] at h
    exact h
  have he : (compOfAdjunction L adj b (𝟙 B)).inv.app F ≫
      (L b).map ((Adjunction.leftAdjointIdIso (adj (𝟙 B))
        (Modules.pushforwardId B)).hom.app F) = 𝟙 _ := by
    rw [← hh, Iso.inv_hom_id_app]
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app ⊤) he) s

private theorem inverseAssociativity
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    (compOfAdjunction L adj (a ≫ b) c).inv.app F ≫
      (compOfAdjunction L adj a b).inv.app ((L c).obj F) ≫
      (L a).map ((compOfAdjunction L adj b c).hom.app F) =
    (compOfAdjunction L adj a (b ≫ c)).inv.app F := by
  apply inverseComparison
    ((compOfAdjunction L adj a b).app ((L c).obj F))
    ((compOfAdjunction L adj (a ≫ b) c).app F)
    ((compOfAdjunction L adj a (b ≫ c)).app F)
  have h := compOfAdjunction_assoc L adj a b c F
  erw [eqToHom_refl, Category.comp_id] at h
  exact h

/-- Unit and associativity equations on sections for any chosen left adjoints.
Source: Stacks Project, Sheaves, Tags 0096–0097; Descent, Tag 03DR.
(blueprint: lem-trf-section-adjunction-coordinate-coherence)

Proof: The right adjoints are scheme module pushforwards. Their identity and
composition comparisons satisfy the unit and associativity equations sectionwise.
Mathlib's left-adjoint comparison transfers these equations to the left adjoints.
For the first equation, left unitality identifies composition with the identity
pullback with the identity comparison. Its adjunction-unit equation cancels that
comparison on sections, proving the normalized identity restriction is the identity.
For the second equation use right unitality and cancel the inverse composition map.
For the third equation take the component of left-adjoint composition associativity
and multiply by the inverses of the two composition comparisons. Equality transports
are the ones induced by scheme composition, and the restriction from inverse image
of the top open to the top open is the identity. Thus all three formulas hold on
actual global sections, for arbitrary modules and arbitrary scheme morphisms.
-/
theorem section_adjunction_coordinate_coherence
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ Modules.pushforward f) :
    let c : ∀ {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C),
        L b ⋙ L a ≅ L (a ≫ b) :=
      fun {_ _ _} a b ↦ Adjunction.leftAdjointCompIso (adj b) (adj a) (adj (a ≫ b))
        (Modules.pushforwardComp a b)
    let unit : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (F : B.Modules),
        Γ(F, ⊤) ⟶ Γ((L a).obj F, ⊤) :=
      fun {_ _} a F ↦ ((adj a).unit.app F).app ⊤ ≫
        ((L a).obj F).presheaf.map (homOfLE a.preimage_top.ge).op
    (∀ {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules),
      unit (𝟙 A) ((L b).obj F) ≫ ((c (𝟙 A) b).hom.app F).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.id_comp b))).app ⊤ = 𝟙 _) ∧
    (∀ {A B : Scheme.{u}} (b : A ⟶ B) (F : B.Modules)
      (s : Γ((L (b ≫ 𝟙 B)).obj F, ⊤)),
      ((L b).map ((Adjunction.leftAdjointIdIso (adj (𝟙 B))
        (Modules.pushforwardId B)).hom.app F)).app ⊤
          (((c b (𝟙 B)).inv.app F).app ⊤ s) = s) ∧
    (∀ {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : C ⟶ D) (F : D.Modules),
      (c (a ≫ b) d).inv.app F ≫ (c a b).inv.app ((L d).obj F) ≫
        (L a).map ((c b d).hom.app F) = (c a (b ≫ d)).inv.app F) := by
  exact ⟨identitySections L adj, inverseRightSections L adj, inverseAssociativity L adj⟩

end

end AlgebraicGeometry.Scheme
