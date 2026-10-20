/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Normalized composition of derived coefficient extensions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization).

The scalar-first tensor convention of `changeOfRings` writes the paper's
`(x ⊗ s) ⊗ t` as `t ⊗ (s ⊗ x)`. All the comparison maps below refer to the
existing sheafified extension, its universal left derived pair, and its
localization counit. The auxiliary presentations only bundle these interfaces.
-/

@[expose] public section

set_option autoImplicit false


universe u v r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module-sheaf category, with no new objects or morphisms.
Source: Stacks 03D7 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The existing restriction-of-scalars functor.
Source: Stacks 03D7 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)

/-- The sheafification image of a sectionwise scalar-first pure tensor.
Source: Stacks 03EK (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def pure {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (changeOfRings a M).val.obj U :=
  (CategoryTheory.toSheafify J (changeOfRingsPresheaf a M).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)

variable [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]

/-- A presentation of the already defined derived coefficient extension. The object and
map equations fix the ordinary functor, and the universal counit fixes the derived pair
up to its unique compatible isomorphism. This bundles the interfaces of 06YY and 07A6;
it introduces no alternative tensor product or derived-category construction.
Source: Stacks 06YY, 07A6 (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
structure Presentation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) where
  /-- The ordinary, sheafified scalar-extension functor. -/
  ordinary : Modules R ⥤ Modules S
  /-- Its objects are the recorded change-of-rings objects. -/
  obj_eq : ∀ M : Modules R, ordinary.obj M = changeOfRings a M
  /-- Its maps are the recorded sheafified tensor maps. -/
  map_eq : ∀ {M N : Modules R} (f : M ⟶ N), ordinary.map f =
    eqToHom (obj_eq M) ≫ changeOfRingsHom a M f ≫ eqToHom (obj_eq N).symm
  /-- Additivity needed for passage to homotopy categories. -/
  additive : ordinary.Additive
  /-- The unbounded left derived functor. -/
  derived : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S)
  /-- The universal left-derived computation morphism. -/
  counit : DerivedCategory.Qh ⋙ derived ⟶
    @Functor.mapHomotopyCategory _ _ _ _ _ _ _ ordinary additive (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh
  /-- The universal property, rather than a freely chosen computation map. -/
  universal : derived.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (Modules R) (ComplexShape.up ℤ))

attribute [instance] Presentation.additive

/-- A pure section of the presented ordinary extension, transported only by `obj_eq`.
Source: Stacks 03EK (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def sectionTensor {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation a) (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U)
    (x : M.val.obj U) : (p.ordinary.obj M).val.obj U :=
  (eqToHom (p.obj_eq M).symm).val.app U (pure a M U s x)


attribute [local irreducible] pure sectionTensor

/-- The canonical coefficient-change square made from two composition comparisons.
The equality is the commuting square of ring maps, not a chosen module comparison.
Source: Stacks 0D6D (blueprint: lem-sfb-successive-derived-quotient-normalization). -/
noncomputable def squareComparison
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
    (δ : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
      (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived)
    {R S R' S' : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (a' : R' ⟶ S')
    (α : R ⟶ R') (β : S ⟶ S') (h : a ≫ β = α ≫ a') :
    (p a).derived ⋙ (p β).derived ≅ (p α).derived ⋙ (p a').derived :=
  δ a β ≪≫ eqToIso (congrArg (fun f ↦ (p f).derived) h) ≪≫ (δ α a').symm

/-- The complete normalized, coherent family of successive extensions. The fields
spell out the tensor formulas, their descent through the universal counits, the
restriction identifications, the scalar-extension units, and coefficient naturality.
Source: Stacks 0D6D, 0G7E, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization). -/
structure Normalization
    (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a) where
  /-- The actual ordinary scalar-extension comparison, natural in the module. -/
  ordinary : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).ordinary ⋙ (p b).ordinary ≅ (p (a ≫ b)).ordinary
  /-- The forward tensor formula, in the scalar-first convention. -/
  ordinary_hom : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U),
    ((ordinary a b).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p (a ≫ b)) M U ((b.hom.app U).hom s * t) x
  /-- The inverse tensor formula. -/
  ordinary_inv : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U),
    ((ordinary a b).inv.app M).val.app U (sectionTensor (p (a ≫ b)) M U t x) =
      sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x)
  /-- The derived comparison is a natural isomorphism, not just objectwise existence. -/
  derived : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    (p a).derived ⋙ (p b).derived ≅ (p (a ≫ b)).derived
  /-- Canonical computation is invertible on each flat-term K-flat representative. -/
  computed : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P))
  /-- The second computation is also invertible on the extended representative. -/
  intermediate_computed : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    IsIso ((p b).counit.app
      (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)))
  /-- The derived comparison is represented by the displayed termwise tensor comparison. -/
  representative : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (derived a b).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (a ≫ b)).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p b).counit.app (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinary a b) (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary extension/restriction adjunctions. -/
  ordinaryAdjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    (p a).ordinary ⊣ restriction a
  /-- The units are the specified scalar-extension units. -/
  ordinary_unit : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
    (U : Cᵒᵖ) (x : M.val.obj U),
    ((ordinaryAdjunction a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x
  /-- Termwise restriction on unbounded derived categories. -/
  right : ∀ {R S : Sheaf J CommRingCat.{r}} (_a : R ⟶ S),
    DerivedCategory (Modules S) ⥤ DerivedCategory (Modules R)
  /-- Its canonical localization factorization. -/
  right_factors : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S),
    DerivedCategory.Qh ⋙ right a ≅
      (restriction a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  /-- The normalized derived coefficient adjunction. -/
  adjunction : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).derived ⊣ right a
  /-- Normalization of its unit through the universal derived computation. -/
  adjunction_normalization : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (adjunction a).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (right_factors a).hom.app
        (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) =
    DerivedCategory.Qh.map
      (((ordinaryAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P))
  /-- Ordinary composite restriction leaves every underlying section unchanged. -/
  restrictionComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    restriction b ⋙ restriction a ≅ restriction (a ≫ b)
  /-- It is the identity on underlying sheaves, not an arbitrary comparison. -/
  restrictionComp_sections : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (N : Modules T) (U : Cᵒᵖ) (x : N.val.obj U),
    ((restrictionComp a b).hom.app N).val.app U x = x
  /-- The induced comparison between derived restrictions. -/
  rightComp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    right b ⋙ right a ≅ right (a ≫ b)
  /-- The comparison is the localization of the ordinary identity on sections. -/
  rightComp_normalization : ∀ {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)),
    (rightComp a b).hom.app (DerivedCategory.Qh.obj H) ≫
      (right_factors (a ≫ b)).hom.app H =
    (right a).map ((right_factors b).hom.app H) ≫
      (right_factors a).hom.app
        (((restriction b).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (restrictionComp a b)
          (ComplexShape.up ℤ)).hom.app H)
  /-- The composite scalar-extension unit is the unit for the composite ring map. -/
  unit_comp : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (X : DerivedCategory (Modules R)),
    (adjunction a).unit.app X ≫
      (right a).map ((adjunction b).unit.app ((p a).derived.obj X)) ≫
      (rightComp a b).hom.app ((p b).derived.obj ((p a).derived.obj X)) ≫
      (right (a ≫ b)).map ((derived a b).hom.app X) = (adjunction (a ≫ b)).unit.app X
  /-- All parenthesizations of three successive extensions agree. This gives agreement
  for every finite iteration by the usual induction on parenthesizations. -/
  associative : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)),
    (p c).derived.map ((derived a b).hom.app X) ≫ (derived (a ≫ b) c).hom.app X =
      (derived b c).hom.app ((p a).derived.obj X) ≫ (derived a (b ≫ c)).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (Category.assoc a b c).symm)
  /-- Naturality in a commuting diagram of composable coefficient maps: pasting its
  two squares gives the outer square, compatibly with the composition comparison.
  The outer equality merely records the composite of the two commuting squares. -/
  coefficient_naturality : ∀ {R S T R' S' T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R' ⟶ S') (b' : S' ⟶ T')
    (α : R ⟶ R') (β : S ⟶ S') (γ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ γ = β ≫ b')
    (hab : (a ≫ b) ≫ γ = α ≫ (a' ≫ b')) (X : DerivedCategory (Modules R)),
    (p γ).derived.map ((derived a b).hom.app X) ≫
      (squareComparison p derived (a ≫ b) (a' ≫ b') α γ hab).hom.app X =
    (squareComparison p derived b b' β γ hb).hom.app ((p a).derived.obj X) ≫
      (p b').derived.map ((squareComparison p derived a a' α β ha).hom.app X) ≫
      (derived a' b').hom.app ((p α).derived.obj X)


private theorem presentation_exists {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    Nonempty (Presentation (hD := hD) a) := by
  obtain ⟨E, h, hm, hadd, _, _, LF, ε, hLF, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients a
  exact ⟨⟨E, h, hm, hadd, LF, ε, hLF⟩⟩


set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionComparison
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    restriction b ⋙ restriction a ≅ restriction (a ≫ b) := by
  refine NatIso.ofComponents (fun N ↦ ?_) ?_
  · let f : (restriction a).obj ((restriction b).obj N) ⟶
        (restriction (a ≫ b)).obj N := by
      refine { val := { app := fun U ↦ ?_, naturality := ?_ } }
      · exact ModuleCat.ofHom
          (X := ((restriction a).obj ((restriction b).obj N)).val.obj U)
          (Y := ((restriction (a ≫ b)).obj N).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
      · intros
        ext x
        rfl
    let g : (restriction (a ≫ b)).obj N ⟶
        (restriction a).obj ((restriction b).obj N) := by
      refine { val := { app := fun U ↦ ?_, naturality := ?_ } }
      · exact ModuleCat.ofHom
          (X := ((restriction (a ≫ b)).obj N).val.obj U)
          (Y := ((restriction a).obj ((restriction b).obj N)).val.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
      · intros
        ext x
        rfl
    exact { hom := f, inv := g
            hom_inv_id := by ext U x; rfl
            inv_hom_id := by ext U x; rfl }
  · intro N N' f
    ext U x
    rfl

omit [EssentiallySmall.{r} C] hD in
set_option backward.isDefEq.respectTransparency false in
private theorem pure_smul {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Modules R) (U : Cᵒᵖ) (s t : S.obj.obj U) (x : M.val.obj U) :
    pure a M U (s * t) x = s • pure a M U t x := by
  unfold pure
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (changeOfRingsPresheaf a M)
  change (η.app U) ((s * t) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x) =
    s • (η.app U) (t ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)
  change (η.app U) (s • (t ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] x)) = _
  exact (η.app U).hom.map_smul s _

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem sectionTensor_smul {R S : Sheaf J CommRingCat.{r}} {a : R ⟶ S}
    (p : Presentation (hD := hD) a) (M : Modules R) (U : Cᵒᵖ)
    (s t : S.obj.obj U) (x : M.val.obj U) :
    sectionTensor p M U (s * t) x = s • sectionTensor p M U t x := by
  unfold sectionTensor
  rw [pure_smul, map_smul]

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_adjunction_exists
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (p : Presentation (hD := hD) a) :
    ∃ adj : p.ordinary ⊣ restriction a,
      ∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U),
        (adj.unit.app M).val.app U x = sectionTensor p M U 1 x := by
  obtain ⟨_, _, ho⟩ := sheafRingCoefficientOrdinaryAdjunction a
  obtain ⟨adj, hadj⟩ := ho p.ordinary p.obj_eq p.map_eq
  refine ⟨adj, ?_⟩
  intro M U x
  have h := hadj M (p.ordinary.obj M) (eqToHom (p.obj_eq M).symm) U x
  simpa [sectionTensor, pure, Adjunction.homEquiv_id] using h

attribute [local irreducible] changeOfRings changeOfRingsPresheaf

private theorem comparison_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D}
    {U : B ⥤ A} {V : D ⥤ B} {W : D ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (e : V ⋙ U ≅ W) (X : A) :
    a.unit.app X ≫ U.map (b.unit.app (F.obj X)) ≫
      e.hom.app (G.obj (F.obj X)) ≫
      W.map ((Adjunction.leftAdjointCompIso a b c e).hom.app X) = c.unit.app X := by
  have h := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c e).inv X
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at h
  have h' := congrArg
    (fun f ↦ f ≫ W.map ((Adjunction.leftAdjointCompIso a b c e).hom.app X)) h
  simpa [Adjunction.comp_unit_app, Category.assoc, ← W.map_comp] using h'

private theorem comparison_transport
    {A B D I : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {U : B ⥤ A} {V : D ⥤ B}
    (L : I → A ⥤ D) (W : I → D ⥤ A) (d : ∀ i, L i ⊣ W i)
    (a : F ⊣ U) (b : G ⊣ V) (i j : I) (h : i = j) (e : V ⋙ U ≅ W i) (X : A) :
    (Adjunction.leftAdjointCompIso a b (d j) (e ≪≫ eqToIso (congrArg W h))).hom.app X =
      (Adjunction.leftAdjointCompIso a b (d i) e).hom.app X ≫
        eqToHom (congrArg (fun i ↦ (L i).obj X) h) := by
  subst j
  simp

private theorem comparison_transpose
    {A B D : Type*} [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D}
    {U : B ⥤ A} {V : D ⥤ B} {W : D ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (e : V ⋙ U ≅ W)
    (X : A) (Y : D) (f : H.obj X ⟶ Y) :
    (a.comp b).homEquiv X Y ((Adjunction.leftAdjointCompIso a b c e).hom.app X ≫ f) =
      c.homEquiv X Y f ≫ e.inv.app Y := by
  have h := unit_conjugateEquiv_symm c (a.comp b) e.inv X
  change c.unit.app X ≫ e.inv.app (H.obj X) =
    (a.comp b).unit.app X ≫
      (V ⋙ U).map ((Adjunction.leftAdjointCompIso a b c e).hom.app X) at h
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← h]
  rw [Category.assoc, ← e.inv.naturality, Adjunction.homEquiv_unit, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem mate_composition
    {A B D A' B' D' : Type*}
    [Category A] [Category B] [Category D] [Category A'] [Category B'] [Category D']
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D}
    {U : B ⥤ A} {V : D ⥤ B} {W : D ⥤ A}
    {F' : A' ⥤ B'} {G' : B' ⥤ D'} {H' : A' ⥤ D'}
    {U' : B' ⥤ A'} {V' : D' ⥤ B'} {W' : D' ⥤ A'}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W)
    (da : F' ⊣ U') (db : G' ⊣ V') (dc : H' ⊣ W')
    (qA : A ⥤ A') (qB : B ⥤ B') (qD : D ⥤ D')
    (rA : qB ⋙ U' ≅ U ⋙ qA) (rB : qD ⋙ V' ≅ V ⋙ qB)
    (rC : qD ⋙ W' ≅ W ⋙ qA)
    (εA : qA ⋙ F' ⟶ F ⋙ qB) (εB : qB ⋙ G' ⟶ G ⋙ qD)
    (εC : qA ⋙ H' ⟶ H ⋙ qD)
    (ha : ∀ (M : A) (N : B) (f : F.obj M ⟶ N),
      da.homEquiv _ _ (εA.app M ≫ qB.map f) =
        qA.map (a.homEquiv M N f) ≫ rA.inv.app N)
    (hb : ∀ (M : B) (N : D) (f : G.obj M ⟶ N),
      db.homEquiv _ _ (εB.app M ≫ qD.map f) =
        qB.map (b.homEquiv M N f) ≫ rB.inv.app N)
    (hc : ∀ (M : A) (N : D) (f : H.obj M ⟶ N),
      dc.homEquiv _ _ (εC.app M ≫ qD.map f) =
        qA.map (c.homEquiv M N f) ≫ rC.inv.app N)
    (e : V ⋙ U ≅ W) (de : V' ⋙ U' ≅ W')
    (he : ∀ N : D,
      de.hom.app (qD.obj N) ≫ rC.hom.app N =
        U'.map (rB.hom.app N) ≫ rA.hom.app (V.obj N) ≫ qA.map (e.hom.app N))
    (M : A)
    (α : G.obj (F.obj M) ⟶ H.obj M)
    (hα : (a.comp b).homEquiv M (H.obj M) α =
      c.unit.app M ≫ e.inv.app (H.obj M))
    (δ : (F' ⋙ G').obj (qA.obj M) ⟶ H'.obj (qA.obj M))
    (hδ : (da.comp db).homEquiv _ _ (δ ≫ εC.app M) =
      dc.homEquiv _ _ (εC.app M) ≫ de.inv.app (qD.obj (H.obj M))) :
    δ ≫ εC.app M = G'.map (εA.app M) ≫ εB.app (F.obj M) ≫ qD.map α := by
  dsimp only [Functor.comp_obj, Functor.comp_map] at *
  have hcinv : rC.inv.app (H.obj M) ≫ de.inv.app (qD.obj (H.obj M)) =
      qA.map (e.inv.app (H.obj M)) ≫ rA.inv.app (V.obj (H.obj M)) ≫
        U'.map (rB.inv.app (H.obj M)) := by
    apply (cancel_epi (de.hom.app (qD.obj (H.obj M)) ≫ rC.hom.app (H.obj M))).mp
    conv_lhs => simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [he]
    simp only [Category.assoc]
    erw [← qA.map_comp_assoc, Iso.hom_inv_id_app, qA.map_id, Category.id_comp,
      Iso.hom_inv_id_app_assoc, ← U'.map_comp, Iso.hom_inv_id_app, U'.map_id]
    rfl
  have hr : (da.comp db).homEquiv _ _
      (G'.map (εA.app M) ≫ εB.app (F.obj M) ≫ qD.map α) =
      qA.map ((a.comp b).homEquiv M (H.obj M) α) ≫
        rA.inv.app (V.obj (H.obj M)) ≫ U'.map (rB.inv.app (H.obj M)) := by
    rw [Adjunction.comp_homEquiv]
    change da.homEquiv _ _ (db.homEquiv _ _
      (G'.map (εA.app M) ≫ εB.app (F.obj M) ≫ qD.map α)) = _
    erw [db.homEquiv_naturality_left, hb]
    erw [← Category.assoc, da.homEquiv_naturality_right, ha]
    simp only [Adjunction.comp_homEquiv, Category.assoc]
    rfl
  apply ((da.comp db).homEquiv _ _).injective
  change (da.comp db).homEquiv (qA.obj M) (qD.obj (H.obj M)) _ =
    (da.comp db).homEquiv (qA.obj M) (qD.obj (H.obj M)) _
  erw [hδ, hr, hα, qA.map_comp, Category.assoc]
  have h := hc M (H.obj M) (𝟙 _)
  simp only [qD.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
  rw [Adjunction.homEquiv_unit] at h
  rw [← Category.assoc, h, Category.assoc, hcinv]
  simp only [Category.assoc]

private theorem adjunction_unit_computation
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {F : A ⥤ B} {U : B ⥤ A} {F' : A' ⥤ B'} {U' : B' ⥤ A'}
    (a : F ⊣ U) (da : F' ⊣ U') (qA : A ⥤ A') (qB : B ⥤ B')
    (r : qB ⋙ U' ≅ U ⋙ qA) (ε : qA ⋙ F' ⟶ F ⋙ qB)
    (hc : ∀ (M : A) (N : B) (f : F.obj M ⟶ N),
      da.homEquiv _ _ (ε.app M ≫ qB.map f) =
        qA.map (a.homEquiv M N f) ≫ r.inv.app N) (M : A) :
    da.unit.app (qA.obj M) ≫ U'.map (ε.app M) ≫ r.hom.app (F.obj M) =
      qA.map (a.unit.app M) := by
  dsimp only [CategoryTheory.Functor.comp_obj] at *
  have h := hc M (F.obj M) (𝟙 _)
  simp only [qB.map_id] at h
  erw [Category.comp_id, Adjunction.homEquiv_id] at h
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun f ↦ f ≫ r.hom.app (F.obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app] at h'
  erw [Category.comp_id] at h'
  exact h'

omit [EssentiallySmall.{r} C] hD in
private theorem restriction_limits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction a) :=
  (sheafRingCoefficientOrdinaryAdjunction a).choose

omit [EssentiallySmall.{r} C] hD in
private theorem restriction_colimits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteColimits (restriction a) :=
  (sheafRingCoefficientOrdinaryAdjunction a).choose_spec.choose

attribute [local instance] restriction_limits restriction_colimits

attribute [local irreducible] Functor.mapDerivedCategory

private noncomputable def rightComparison
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (restriction b).mapDerivedCategory ⋙ (restriction a).mapDerivedCategory ≅
      (restriction (a ≫ b)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (restriction b) (restriction a)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (restrictionComparison a b)

omit [EssentiallySmall.{r} C] in
private theorem rightComparison_normalization
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (H : HomotopyCategory (Modules T) (ComplexShape.up ℤ)) :
    (rightComparison (hD := hD) a b).hom.app (DerivedCategory.Qh.obj H) ≫
      (restriction (a ≫ b)).mapDerivedCategoryFactorsh.hom.app H =
    (restriction a).mapDerivedCategory.map
        ((restriction b).mapDerivedCategoryFactorsh.hom.app H) ≫
      (restriction a).mapDerivedCategoryFactorsh.hom.app
        (((restriction b).mapHomotopyCategory (ComplexShape.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (restrictionComparison a b)
          (ComplexShape.up ℤ)).hom.app H) := by
  dsimp only [rightComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fach]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rfl


section DerivedCoherence

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {D₀ D₁ D₂ D₃ : Type*}
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  (F : D₀ ⥤ D₁) (G : D₁ ⥤ D₂) (H : D₂ ⥤ D₃)
  (U : D₀ ⥤ D₂) (V : D₁ ⥤ D₃) (T : D₀ ⥤ D₃)
  [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [T.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

set_option backward.isDefEq.respectTransparency false in
private theorem derive_coherence (a : U ≅ F ⋙ G) (b : T ≅ U ⋙ H)
    (c : V ≅ G ⋙ H) (d : T ≅ F ⋙ V)
    (hab : b ≪≫ Functor.isoWhiskerRight a H = d ≪≫ Functor.isoWhiskerLeft F c) :
    (Functor.mapDerivedCategoryTriangleIso b ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryTriangleIso a)
          H.mapDerivedCategory) =
      (Functor.mapDerivedCategoryTriangleIso d ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso c)) := by
  apply Iso.ext
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hab
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hwr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hwl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have ha := Functor.mapDerivedCategoryCompIso_assoc F G H
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hwr, ← reassoc_of% hwl, ← ha, reassoc_of% hm]

set_option backward.isDefEq.respectTransparency false in
private theorem derive_tower_transport (T' : D₀ ⥤ D₃) [T'.Additive]
    [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
    (a : U ≅ F ⋙ G) (b : T ≅ U ⋙ H) (c : V ≅ G ⋙ H) (d : T' ≅ F ⋙ V)
    (e : T = T')
    (hab : ∀ X, H.map (a.inv.app X) ≫ b.inv.app X ≫
      eqToHom (congrArg (fun L ↦ L.obj X) e) = c.inv.app (F.obj X) ≫ d.inv.app X)
    (K : DerivedCategory D₀) :
    H.mapDerivedCategory.map ((Functor.mapDerivedCategoryTriangleIso a).inv.app K) ≫
        (Functor.mapDerivedCategoryTriangleIso b).inv.app K ≫
        eqToHom (by subst T'; rfl) =
      (Functor.mapDerivedCategoryTriangleIso c).inv.app (F.mapDerivedCategory.obj K) ≫
        (Functor.mapDerivedCategoryTriangleIso d).inv.app K := by
  subst T'
  have hi : (Functor.isoWhiskerRight a H).symm ≪≫ b.symm =
      (Functor.isoWhiskerLeft F c).symm ≪≫ d.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext X
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_refl,
      Category.comp_id] using hab X
  have hf := congrArg Iso.symm hi
  change b ≪≫ Functor.isoWhiskerRight a H = d ≪≫ Functor.isoWhiskerLeft F c at hf
  have hd := derive_coherence F G H U V T a b c d hf
  have hk := congrArg (fun z ↦ z.inv.app K) hd
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToHom_refl, Category.comp_id] using hk

end DerivedCoherence

omit [EssentiallySmall.{r} C] hD
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem restriction_transport_sections
    {R S : Sheaf J CommRingCat.{r}} (a b : R ⟶ S) (h : a = b)
    (N : Modules S) (U : Cᵒᵖ) (x : N.val.obj U) :
    (eqToHom (congrArg (fun f ↦ (restriction f).obj N) h)).val.app U x = x := by
  subst b
  rfl

omit [EssentiallySmall.{r} C] in
private theorem rightComparison_assoc
    {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) :
    Functor.isoWhiskerLeft (restriction c).mapDerivedCategory (rightComparison (hD := hD) a b) ≪≫
      rightComparison (a ≫ b) c =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (rightComparison b c) (restriction a).mapDerivedCategory ≪≫
        rightComparison a (b ≫ c) ≪≫
          eqToIso (congrArg (fun f : R ⟶ V ↦ (restriction f).mapDerivedCategory)
            (Category.assoc a b c).symm) := by
  have ho (N : Modules V) :
      (restriction a).map ((restrictionComparison b c).hom.app N) ≫
          (restrictionComparison a (b ≫ c)).hom.app N ≫
          eqToHom (congrArg (fun f : R ⟶ V ↦ (restriction f).obj N)
            (Category.assoc a b c).symm) =
        (restrictionComparison a b).hom.app ((restriction c).obj N) ≫
          (restrictionComparison (a ≫ b) c).hom.app N := by
    ext U x
    change (eqToHom (congrArg (fun f : R ⟶ V ↦ (restriction f).obj N)
      (Category.assoc a b c).symm)).val.app U x = x
    exact restriction_transport_sections _ _ (Category.assoc a b c).symm N U x
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have h := derive_tower_transport (restriction c) (restriction b) (restriction a)
    (restriction (b ≫ c)) (restriction (a ≫ b)) (restriction (a ≫ b ≫ c))
    (restriction ((a ≫ b) ≫ c))
    (restrictionComparison b c).symm (restrictionComparison a (b ≫ c)).symm
    (restrictionComparison a b).symm (restrictionComparison (a ≫ b) c).symm
    (congrArg (fun f : R ⟶ V ↦ restriction f) (Category.assoc a b c).symm) ho X
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv,
    ← Functor.mapDerivedCategoryNatIso_symm, Iso.symm_symm_eq, NatTrans.comp_app] at h
  simpa only [rightComparison, Functor.mapDerivedCategoryTriangleIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, eqToIso.hom, eqToHom_app, Category.id_comp] using h.symm


private theorem presentation_computed
    {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (p : Presentation (hD := hD) a)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    IsIso (p.counit.app ((HomotopyCategory.quotient _ _).obj P)) := by
  obtain ⟨E₀, h₀, hm₀, hadd₀, _, _, LF₀, ε₀, hLF₀, _, hc₀⟩ :=
    derivedChangeOfRingsIndependentCoefficients a
  have he : E₀ = p.ordinary := by
    refine CategoryTheory.Functor.ext (fun M ↦ (h₀ M).trans (p.obj_eq M).symm) ?_
    intro M N f
    rw [hm₀, p.map_eq]
    simp
  subst E₀
  let := p.universal
  let := hLF₀
  let i := Functor.leftDerivedUnique LF₀ p.derived p.counit ε₀
    (HomotopyCategory.quasiIso (Modules R) (ComplexShape.up ℤ))
  have hc := hc₀ P hP
  have hi := Functor.leftDerivedNatTrans_app p.derived LF₀ p.counit ε₀
    (HomotopyCategory.quasiIso (Modules R) (ComplexShape.up ℤ))
    (𝟙 (p.ordinary.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))
    ((HomotopyCategory.quotient _ _).obj P)
  change i.hom.app _ ≫ ε₀.app _ = p.counit.app _ ≫ _ at hi
  simp only [NatTrans.id_app, Category.comp_id] at hi
  rw [← hi]
  infer_instance


section Family

variable (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation (hD := hD) a)
  (oa : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), (p a).ordinary ⊣ restriction a)
  (hu : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (M : Modules R)
    (U : Cᵒᵖ) (x : M.val.obj U),
      ((oa a).unit.app M).val.app U x = sectionTensor (p a) M U 1 x)

private noncomputable abbrev ordinaryComparison
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :
    (p a).ordinary ⋙ (p b).ordinary ≅ (p (a ≫ b)).ordinary :=
  Adjunction.leftAdjointCompIso (oa a) (oa b) (oa (a ≫ b)) (restrictionComparison a b)


include hu in
omit [EssentiallySmall.{r} C] in
private theorem ordinaryComparison_hom_one
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((ordinaryComparison p oa a b).hom.app M).val.app U
        (sectionTensor (p b) ((p a).ordinary.obj M) U 1
          (sectionTensor (p a) M U 1 x)) = sectionTensor (p (a ≫ b)) M U 1 x := by
  have h := congrArg (fun f ↦ f.val.app U x)
    (comparison_unit (oa a) (oa b) (oa (a ≫ b)) (restrictionComparison a b) M)
  change ((ordinaryComparison p oa a b).hom.app M).val.app U
      (((oa b).unit.app ((p a).ordinary.obj M)).val.app U
        (((oa a).unit.app M).val.app U x)) =
    ((oa (a ≫ b)).unit.app M).val.app U x at h
  simpa only [hu] using h

include hu in
omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryComparison_hom
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (t : T.obj.obj U) :
    ((ordinaryComparison p oa a b).hom.app M).val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U s x)) =
      sectionTensor (p (a ≫ b)) M U ((b.hom.app U).hom s * t) x := by
  have ha : sectionTensor (p a) M U s x = s • sectionTensor (p a) M U 1 x := by
    simpa only [mul_one] using sectionTensor_smul (p a) M U s 1 x
  have hb (y : ((p a).ordinary.obj M).val.obj U) :
      sectionTensor (p b) ((p a).ordinary.obj M) U t y =
        t • sectionTensor (p b) ((p a).ordinary.obj M) U 1 y := by
    simpa only [mul_one] using sectionTensor_smul (p b) ((p a).ordinary.obj M) U t 1 y
  have hs (y : ((p a).ordinary.obj M).val.obj U) :
      sectionTensor (p b) ((p a).ordinary.obj M) U 1 (s • y) =
        (b.hom.app U).hom s • sectionTensor (p b) ((p a).ordinary.obj M) U 1 y := by
    have h := (((oa b).unit.app ((p a).ordinary.obj M)).val.app U).hom.map_smul s y
    change (((oa b).unit.app ((p a).ordinary.obj M)).val.app U) (s • y) =
      (b.hom.app U).hom s •
        (show ((p b).ordinary.obj ((p a).ordinary.obj M)).val.obj U from
          (((oa b).unit.app ((p a).ordinary.obj M)).val.app U) y) at h
    simpa only [hu] using h
  rw [hb, ha, map_smul, hs, map_smul, ordinaryComparison_hom_one p oa hu]
  erw [smul_smul, mul_comm t, ← sectionTensor_smul]
  simp only [mul_one]

include hu in
omit [EssentiallySmall.{r} C] in
private theorem ordinaryComparison_inv
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (t : T.obj.obj U) :
    ((ordinaryComparison p oa a b).inv.app M).val.app U
      (sectionTensor (p (a ≫ b)) M U t x) =
    sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x) := by
  have h := ordinaryComparison_hom p oa hu a b M U x 1 t
  simp only [map_one, one_mul] at h
  have h' := congrArg (((ordinaryComparison p oa a b).inv.app M).val.app U) h
  have hi := congrArg (fun f ↦ f.val.app U
      (sectionTensor (p b) ((p a).ordinary.obj M) U t (sectionTensor (p a) M U 1 x)))
    ((ordinaryComparison p oa a b).hom_inv_id_app M)
  exact h'.symm.trans hi

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_homotopy_transpose
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D}
    {U : B ⥤ A} {V : D ⥤ B} {W : D ⥤ A}
    [F.Additive] [G.Additive] [H.Additive] [U.Additive] [V.Additive] [W.Additive]
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (e : V ⋙ U ≅ W)
    (P : CochainComplex A ℤ) :
    ((a.mapHomotopyCategory (ComplexShape.up ℤ)).comp
        (b.mapHomotopyCategory (ComplexShape.up ℤ))).homEquiv
      ((HomotopyCategory.quotient _ _).obj P)
      ((H.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))
      ((Functor.mapHomotopyCategoryCompIso (Adjunction.leftAdjointCompIso a b c e)
        (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj P)) =
    (c.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
        ((HomotopyCategory.quotient _ _).obj P) ≫
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
        ((H.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj P)) := by
  have hbase (M : A) := (unit_conjugateEquiv_symm c (a.comp b) e.inv M).symm
  have h := Adjunction.mapHomotopyCategory_unit_app_comp (ComplexShape.up ℤ)
    (a.comp b) c (Adjunction.leftAdjointCompIso a b c e).hom e.inv hbase
    ((HomotopyCategory.quotient _ _).obj P)
  have hc := Adjunction.mapHomotopyCategory_comp_unit_app (ComplexShape.up ℤ)
    a b ((HomotopyCategory.quotient _ _).obj P)
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  dsimp only [CategoryTheory.Functor.comp_obj] at hc
  erw [CategoryTheory.Functor.map_id] at hc
  simp only [Category.comp_id] at hc
  rw [hc] at h
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  dsimp only [CategoryTheory.Functor.comp_obj] at *
  exact h

end Family

omit [EssentiallySmall.{r} C] hD
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem restrictionComparison_sections
    {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (N : Modules T) (U : Cᵒᵖ) (x : N.val.obj U) :
    ((restrictionComparison a b).hom.app N).val.app U x = x := by
  rfl

attribute [local irreducible] restrictionComparison rightComparison

-- The preceding APIs avoid unfolding the localization and mate constructions in the family proof.
attribute [local irreducible] Functor.mapHomotopyCategory Adjunction.mapHomotopyCategory
  Adjunction.leftAdjointCompIso DerivedCategory.Qh Functor.mapHomotopyCategoryCompIso
  NatTrans.mapHomotopyCategory Functor.mapDerivedCategoryFactorsh

section Coefficient

omit [EssentiallySmall.{r} C] hD
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

variable (D : Sheaf J CommRingCat.{r} → Type*) [∀ R, Category (D R)]
  (L : ∀ {R S : Sheaf J CommRingCat.{r}} (_a : R ⟶ S), D R ⥤ D S)
  (δ : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T),
    L a ⋙ L b ≅ L (a ≫ b))

private noncomputable abbrev coefficientSquare
    {R S R' S' : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (a' : R' ⟶ S')
    (α : R ⟶ R') (β : S ⟶ S') (h : a ≫ β = α ≫ a') :
    L a ⋙ L β ≅ L α ⋙ L a' :=
  δ a β ≪≫ eqToIso (congrArg (fun f ↦ L f) h) ≪≫ (δ α a').symm

private theorem comparison_congr_left {R S T : Sheaf J CommRingCat.{r}}
    (a a' : R ⟶ S) (h : a = a') (b : S ⟶ T) (X : D R) :
    (L b).map (eqToHom (congrArg (fun f ↦ (L f).obj X) h)) ≫
        (δ a' b).hom.app X =
      (δ a b).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (L f).obj X) (congrArg (fun f ↦ f ≫ b) h)) := by
  cases h
  simp

private theorem comparison_congr_right {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b b' : S ⟶ T) (h : b = b') (X : D R) :
    eqToHom (congrArg (fun f ↦ (L f).obj ((L a).obj X)) h) ≫
        (δ a b').hom.app X =
      (δ a b).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (L f).obj X) (congrArg (fun f ↦ a ≫ f) h)) := by
  cases h
  simp

private theorem coefficient_pasting
    (hassoc : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : D R),
    (L c).map ((δ a b).hom.app X) ≫ (δ (a ≫ b) c).hom.app X =
      (δ b c).hom.app ((L a).obj X) ≫ (δ a (b ≫ c)).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (L f).obj X) (Category.assoc a b c).symm)) :
    ∀ {R S T R' S' T' : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R' ⟶ S') (b' : S' ⟶ T')
    (α : R ⟶ R') (β : S ⟶ S') (γ : T ⟶ T')
    (ha : a ≫ β = α ≫ a') (hb : b ≫ γ = β ≫ b')
    (hab : (a ≫ b) ≫ γ = α ≫ (a' ≫ b')) (X : D R),
    (L γ).map ((δ a b).hom.app X) ≫
      (coefficientSquare (D := D) L δ (a ≫ b) (a' ≫ b') α γ hab).hom.app X =
    (coefficientSquare (D := D) L δ b b' β γ hb).hom.app ((L a).obj X) ≫
      (L b').map ((coefficientSquare (D := D) L δ a a' α β ha).hom.app X) ≫
      (δ a' b').hom.app ((L α).obj X) := by
  intro R S T R' S' T' a b a' b' α β γ ha hb hab X
  dsimp only [CategoryTheory.Functor.comp_obj] at *
  apply (cancel_mono ((δ α (a' ≫ b')).hom.app X)).mp
  simp only [coefficientSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  have hA := hassoc α a' b' X
  have hB := hassoc a β b' X
  have hC := hassoc a b γ X
  simp only [eqToHom_refl, Category.comp_id] at hA hB hC
  rw [← hA]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [comparison_congr_left (D := D) L δ (a ≫ β) (α ≫ a') ha b' X]
  rw [reassoc_of% hB]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% (comparison_congr_right (D := D) L δ a (b ≫ γ) (β ≫ b') hb X)]
  rw [← reassoc_of% hC]
  simp only [eqToHom_trans]

end Coefficient

/-- Successive derived scalar extensions have their canonical tensor comparison, inverse,
unit normalization, coefficient naturality and coherent finite iteration. This is a
family statement, so naturality concerns arbitrary derived morphisms as well as changing
coefficient rings. No ring map is required to be flat or surjective, and no complex is
required to be bounded. Ordinary rings are the specialization to the singleton category
with the bottom (identity-cover) topology.

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YS, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization).

Proof:
1. Present every existing scalar extension and its universal left-derived pair using
`derivedChangeOfRingsIndependentCoefficients`. Obtain ordinary extension/restriction
adjunctions with their specified pure-tensor units.
2. Restriction along a composite has a sectionwise identity comparison. Take its left
adjoint mate to obtain the ordinary extension comparison. Its unit formula handles
1 tensor (1 tensor x); linearity over the two coefficient rings gives the general
forward formula. Applying the inverse comparison gives the inverse formula.
3. Use the derived Hom comparison to choose derived adjunctions compatible with the
prescribed universal counits on every homotopy-category input. Exact derivation of
restriction gives its composition comparison. Take the left adjoint mate for the
derived extension comparison; the mate identity gives unit_comp.
4. Compatibility of mates with composition, applied to the global Hom comparison,
gives representative. Uniqueness of universal derived pairs transports the existing
K-flat computation to each presented counit. The first and composite counits
are therefore invertible on a flat-term K-flat input. Cancel the two outer isomorphisms
in representative to deduce
intermediate_computed, without another K-flat-preservation argument.
5. Ordinary restriction comparisons are identities on underlying sections. Exact
derivation preserves their associativity, and the composition law for mates transfers
this to the derived extension comparisons. Track equality transports of ring maps
explicitly. Coefficient naturality follows by pasting the two square comparisons,
using associativity three times and cancelling inverse comparison maps.
6. Every construction uses the existing sheafified scalar extension. Thus specialization
to the singleton identity-cover site gives ordinary scalar extension as stated. -/
theorem successive_derived_quotient_normalization :
    ∃ p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a,
      Nonempty (Normalization p) := by
  classical
  obtain ⟨p⟩ : Nonempty
      (∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation (hD := hD) a) :=
    ⟨fun a ↦ Classical.choice (presentation_exists a)⟩
  choose oa hu using fun {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) ↦
    ordinary_adjunction_exists a (p a)
  choose da hda using fun {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) ↦
    sheafRingDerivedHomComparison a (p a).ordinary (p a).obj_eq (p a).map_eq
      (oa a) (p a).derived (p a).counit (p a).universal
  let δ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T) :=
    Adjunction.leftAdjointCompIso (da a) (da b) (da (a ≫ b)) (rightComparison a b)
  have hassoc : ∀ {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (X : DerivedCategory (Modules R)),
    (p c).derived.map ((δ a b).hom.app X) ≫ (δ (a ≫ b) c).hom.app X =
      (δ b c).hom.app ((p a).derived.obj X) ≫ (δ a (b ≫ c)).hom.app X ≫
        eqToHom (congrArg (fun f ↦ (p f).derived.obj X) (Category.assoc a b c).symm) := by
    intro R S T V a b c X
    have h := Adjunction.leftAdjointCompIso_assoc
      (da a) (da b) (da c) (da (a ≫ b)) (da (b ≫ c)) (da ((a ≫ b) ≫ c))
      (rightComparison a b) (rightComparison b c)
      (rightComparison a (b ≫ c) ≪≫ eqToIso
        (congrArg (fun f : R ⟶ V ↦ (restriction f).mapDerivedCategory)
          (Category.assoc a b c).symm)) (rightComparison (a ≫ b) c)
      (rightComparison_assoc a b c)
    have ht := comparison_transport (fun f : R ⟶ V ↦ (p f).derived)
      (fun f : R ⟶ V ↦ (restriction f).mapDerivedCategory) (fun f ↦ da f)
      (da a) (da (b ≫ c)) (a ≫ b ≫ c) ((a ≫ b) ≫ c) (Category.assoc a b c).symm
      (rightComparison a (b ≫ c)) X
    have hh := congrArg (fun e ↦ e.hom.app X) h
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Category.id_comp] at hh
    rw [ht] at hh
    exact hh.symm
  have hrep : ∀ {R S T : Sheaf J CommRingCat.{r}} (a : R ⟶ S) (b : S ⟶ T)
    (P : CochainComplex (Modules R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
    (∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)) →
    (δ a b).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p (a ≫ b)).counit.app ((HomotopyCategory.quotient _ _).obj P) =
    (p b).derived.map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (p b).counit.app (((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (ordinaryComparison p oa a b)
          (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj P)) := by
    intro R S T a b P hP hf
    let M := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
    let α := (Functor.mapHomotopyCategoryCompIso
      (Adjunction.leftAdjointCompIso (oa a) (oa b) (oa (a ≫ b))
        (restrictionComparison a b)) (ComplexShape.up ℤ)).hom.app M
    have hα := comparison_homotopy_transpose (oa a) (oa b) (oa (a ≫ b))
      (restrictionComparison a b) P
    have hδ := comparison_transpose (da a) (da b) (da (a ≫ b))
      (rightComparison a b) (DerivedCategory.Qh.obj M)
      (DerivedCategory.Qh.obj
        (((p (a ≫ b)).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj M))
      ((p (a ≫ b)).counit.app M)
    exact mate_composition
      ((oa a).mapHomotopyCategory (ComplexShape.up ℤ))
      ((oa b).mapHomotopyCategory (ComplexShape.up ℤ))
      ((oa (a ≫ b)).mapHomotopyCategory (ComplexShape.up ℤ))
      (da a) (da b) (da (a ≫ b))
      DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh
      (restriction a).mapDerivedCategoryFactorsh
      (restriction b).mapDerivedCategoryFactorsh
      (restriction (a ≫ b)).mapDerivedCategoryFactorsh
      (p a).counit (p b).counit (p (a ≫ b)).counit
      (hda a) (hda b) (hda (a ≫ b))
      (Functor.mapHomotopyCategoryCompIso (restrictionComparison a b) (ComplexShape.up ℤ))
      (rightComparison a b) (rightComparison_normalization a b)
      M α hα ((δ a b).hom.app (DerivedCategory.Qh.obj M)) hδ
  refine ⟨p, ⟨{
    ordinary := ordinaryComparison p oa
    ordinary_hom := ordinaryComparison_hom p oa hu
    ordinary_inv := ordinaryComparison_inv p oa hu
    derived := δ
    computed := fun a P hP _hf ↦ presentation_computed a (p a) P hP
    intermediate_computed := ?_
    representative := hrep
    ordinaryAdjunction := oa
    ordinary_unit := hu
    right := fun a ↦ (restriction a).mapDerivedCategory
    right_factors := fun a ↦ (restriction a).mapDerivedCategoryFactorsh
    adjunction := da
    adjunction_normalization := ?_
    restrictionComp := restrictionComparison
    restrictionComp_sections := restrictionComparison_sections
    rightComp := rightComparison
    rightComp_normalization := rightComparison_normalization
    unit_comp := fun a b X ↦ comparison_unit (da a) (da b) (da (a ≫ b))
      (rightComparison a b) X
    associative := hassoc
    coefficient_naturality := coefficient_pasting
      (D := fun R ↦ DerivedCategory (Modules R)) (fun a ↦ (p a).derived) δ hassoc }⟩⟩
  · intro R S T a b P hP hf
    let M := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
    let A := ((p a).ordinary.mapHomotopyCategory (ComplexShape.up ℤ)).obj M
    let f := (p b).derived.map ((p a).counit.app M)
    let g := (p b).counit.app A
    let k := DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (ordinaryComparison p oa a b)
        (ComplexShape.up ℤ)).hom.app M)
    have ha := presentation_computed a (p a) P hP
    have hab := presentation_computed (a ≫ b) (p (a ≫ b)) P hP
    have hfgk : IsIso (f ≫ g ≫ k) := by
      rw [← hrep a b P hP hf]
      infer_instance
    have hgk : IsIso (g ≫ k) := IsIso.of_isIso_comp_left f (g ≫ k)
    exact IsIso.of_isIso_comp_right g k
  · intro R S a P hP hf
    have hunit := adjunction_unit_computation
      ((oa a).mapHomotopyCategory (ComplexShape.up ℤ)) (da a)
      DerivedCategory.Qh DerivedCategory.Qh (restriction a).mapDerivedCategoryFactorsh
      (p a).counit (hda a) ((HomotopyCategory.quotient _ _).obj P)
    exact hunit

end SheafOfModules.SuccessiveDerivedQuotient
