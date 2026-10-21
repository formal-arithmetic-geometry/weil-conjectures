/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SheafTensorStructure
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.CategoryTheory.SheafTensorClosed
import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf

/-! # Coherent reconstruction of lax module direct images

Source: Stacks Project, Tag 03D6, definition-pushforward, and the internal-module
refinement in Steps 1–9 of the DAG proof. The generalized coefficient restriction
uses the localized tensor and actual counit transport, with independent site universes
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u uC vC uD vD uH vH uA vA
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
attribute [instance] Sheaf.monoidalCategory Sheaf.braidedCategory

namespace CategoryTheory.Sheaf

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A] [BraidedCategory A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]

/-- Restriction on coefficient sheaves, without a continuity assumption on set sheaves.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def coefficientRestriction (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op) hF

/-- The actual sheafification counit identifies sheafified restriction with restriction.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def coefficientRestrictionCounitIso (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj F.op ⋙
      presheafToSheaf J A ≅ coefficientRestriction F hF :=
  Functor.isoWhiskerLeft (coefficientRestriction F hF)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (coefficientRestriction F hF).rightUnitor

/-- The lax restriction structure transported along the actual counit from inclusion,
pointwise restriction and strong monoidal sheafification. Source: blueprint
pushforward-composition proof, second sentence
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable instance coefficientRestrictionLaxMonoidal (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    (coefficientRestriction F hF).LaxMonoidal :=
  Functor.LaxMonoidal.transport (coefficientRestrictionCounitIso F hF)

/-- Generator normalization and uniqueness for independently sized sites, in the
localized tensor convention. Source: blueprint pushforward-composition proof,
second sentence (blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. The inclusion tensorator is the adjunction mate of the inverse strong
sheafification tensorator followed by the two counits. The triangle identities
identify it with the actual unit transported to the localized tensor. Expanding
counit transport on restriction cancels the inverse counits with these units,
leaving the restricted inclusion tensorator. The unit calculation is identical.
The sheafification Hom bijections make precomposition with these two generators
injective, so both extensions are unique. This is the same calculation as
`generatorRestriction_comparison`, without identifying site and coefficient
universes or replacing the localized tensor by a retensored copy. -/
theorem coefficientRestriction_comparison
    [Abelian A] [IsGrothendieckAbelian.{vA} A] [MonoidalClosed A]
    [UnivLE.{max uC vC, vA}] [UnivLE.{max uD vD, vA}]
    (F : C ⥤ D)
    (hF : ∀ M : Sheaf K A, Presheaf.IsSheaf J (F.op ⋙ M.obj)) :
    (∀ M N : Sheaf K A,
      Functor.LaxMonoidal.μ (sheafToPresheaf J A)
          ((coefficientRestriction F hF).obj M) ((coefficientRestriction F hF).obj N) ≫
        (Functor.LaxMonoidal.μ (coefficientRestriction F hF) M N).hom =
          Functor.whiskerLeft F.op (Functor.LaxMonoidal.μ (sheafToPresheaf K A) M N) ∧
      ∀ f g : (coefficientRestriction F hF).obj M ⊗
          (coefficientRestriction F hF).obj N ⟶ (coefficientRestriction F hF).obj (M ⊗ N),
        Functor.LaxMonoidal.μ (sheafToPresheaf J A) _ _ ≫ f.hom =
          Functor.LaxMonoidal.μ (sheafToPresheaf J A) _ _ ≫ g.hom → f = g) ∧
    (Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫
        (Functor.LaxMonoidal.ε (coefficientRestriction F hF)).hom =
          Functor.whiskerLeft F.op (Functor.LaxMonoidal.ε (sheafToPresheaf K A)) ∧
      ∀ f g : 𝟙_ (Sheaf J A) ⟶ (coefficientRestriction F hF).obj (𝟙_ (Sheaf K A)),
        Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ f.hom =
          Functor.LaxMonoidal.ε (sheafToPresheaf J A) ≫ g.hom → f = g) := by
  sorry

end CategoryTheory.Sheaf

namespace CategoryTheory.InternalAbelianSheafModule

/-- Sectionwise direct image for a ring-presheaf map whose underlying abelian
restriction preserves sheaves. The source and target ring presheaves are sheaves.
Source: Stacks Tag 03D6, DAG proof Step 4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def coefficientModulePushforward
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D)
    (hF : ∀ M : Sheaf K AddCommGrpCat.{u}, Presheaf.IsSheaf J (F.op ⋙ M.obj))
    {BC : Sheaf J RingCat.{u}} {BD : Sheaf K RingCat.{u}}
    (φ : BC.obj ⟶ F.op ⋙ BD.obj) : SheafOfModules.{u} BD ⥤ SheafOfModules.{u} BC where
  obj M :=
    { val := (PresheafOfModules.pushforward φ).obj M.val
      isSheaf := hF ((SheafOfModules.toSheaf _).obj M) }
  map f := ⟨(PresheafOfModules.pushforward φ).map f.val⟩

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [UnivLE.{max uC vC, u}] [UnivLE.{max uD vD, u}]
  [HasSheafify J AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  [(K.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (F : C ⥤ D)
  (hF : ∀ M : Sheaf K AddCommGrpCat.{u}, Presheaf.IsSheaf J (F.op ⋙ M.obj))
  (RC : Sheaf J AddCommGrpCat.{u}) (RD : Sheaf K AddCommGrpCat.{u})
  [MonObj RC] [IsCommMonObj RC] [MonObj RD] [IsCommMonObj RD]
  (ψ : RC ⟶ (Sheaf.coefficientRestriction F hF).obj RD) [IsMonHom ψ]

include hF in
/-- The sectionwise direct image of the reconstructed ring presheaf is a sheaf.
Source: Stacks Tag 03D6, DAG proof Step 1
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Forget the reconstructed ring to its abelian presheaf. This is exactly
F.op composed with RD.obj, a sheaf by hF. The forgetful functor reflects the sheaf
condition for algebraic structures, so the ring presheaf is a sheaf. -/
theorem laxSectionRingImage_isSheaf :
    Presheaf.IsSheaf J (F.op ⋙ sectionRings.{u, uD, vD} K RD) := by
  sorry

/-- The direct image ring sheaf has exactly the section rings B_D(FV).
Source: Stacks Tag 03D6, DAG proof Step 1
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingImage : Sheaf J CommRingCat.{u} :=
  ⟨F.op ⋙ sectionRings.{u, uD, vD} K RD, laxSectionRingImage_isSheaf F hF RD⟩

/-- The ring map is uniquely determined by the given additive section maps.
Source: Stacks Tag 03D6; DAG proof Steps 1–2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Precompose the transported multiplication and unit with the actual tensor
and unit generators. The generator comparison gives the original products and
units on RD(FV). The monoid-map laws for ψ therefore say its additive components
preserve products and one. Naturality gives a ring-presheaf map, hence a map of
ring sheaves. Equality of the additive components proves uniqueness. -/
theorem laxSectionRingMap_existsUnique :
    ∃! φ : sectionRings.{u, uC, vC} J RC ⟶ F.op ⋙ sectionRings.{u, uD, vD} K RD,
      ∀ U : Cᵒᵖ, (φ.app U).hom.toAddMonoidHom = (ψ.hom.app U).hom := by
  sorry

/-- The unique reconstructed coefficient map, selected from its uniqueness theorem.
Source: Stacks Tag 03D6, DAG proof Step 2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingMap :
    sectionRings.{u, uC, vC} J RC ⟶ F.op ⋙ sectionRings.{u, uD, vD} K RD :=
  Classical.choose (laxSectionRingMap_existsUnique F hF RC RD ψ).exists

/-- The same unique reconstructed coefficient map, bundled as a map of ring sheaves.
Source: Stacks Tag 03D6, DAG proof Step 2
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionRingSheafMap :
    sectionRingSheaf.{u, uC, vC} J RC ⟶ laxSectionRingImage.{u, uC, vC, uD, vD} F hF RD :=
  ⟨laxSectionRingMap F hF RC RD ψ⟩

/-- Direct image of internal modules is mapMod followed by restriction of scalars.
Source: Stacks Tag 03D6, DAG proof Step 3
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxInternalPushforward :
    Mod (Sheaf K AddCommGrpCat.{u}) RD ⥤ Mod (Sheaf J AddCommGrpCat.{u}) RC :=
  (Sheaf.coefficientRestriction F hF).mapMod RD ⋙ Mod.comap ψ

/-- Sectionwise direct image using only preservation of abelian sheaves.
Source: Stacks Tag 03D6, DAG proof Step 4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionPushforward :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, uD, vD} K RD)) ⥤
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf.{u, uC, vC} J RC)) :=
  coefficientModulePushforward F hF
    (Functor.whiskerRight (laxSectionRingMap F hF RC RD ψ)
      (forget₂ CommRingCat RingCat))
/-- The comparison is the unique natural isomorphism with identity section maps.
Source: Stacks Tag 03D6, DAG proof Steps 3–4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. On a tensor generator the internal pushed action is ψ_V(r)n, by naturality
and the generator normalization. This is exactly the sectionwise action. Identity
section maps are therefore linear in both directions and natural in the module.
Their composites are identities; a comparison with these section maps is unique. -/
theorem laxSectionComparison_existsUnique :
    ∃! r : laxInternalPushforward F hF RC RD ψ ⋙
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor ≅
        (sectionModuleEquivalence.{u, uD, vD} K RD).functor ⋙ laxSectionPushforward F hF RC RD ψ,
      ∀ (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
        (x : M.X.obj.obj (F.op.obj U)), ((r.hom.app M).val.app U).hom x = x := by
  sorry

/-- The reconstructed pushed action is multiplication by ψ_V(r) on sections.
Source: Stacks Tag 03D6, DAG proof Step 3
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Precompose the internal action with the tensor generator. Naturality moves
ψ to the sectionwise tensor. Generator normalization for F then replaces its lax
tensorator by the restricted generator on D. The resulting action is ψ_V(r)n. -/
theorem laxInternalPushforward_sectionAction
    (M : Mod (Sheaf K AddCommGrpCat.{u}) RD) (U : Cᵒᵖ)
    (r : (sectionRings.{u, uC, vC} J RC).obj U) (x : M.X.obj.obj (F.op.obj U)) :
    r • (@id (((sectionModuleEquivalence.{u, uC, vC} J RC).functor.obj
        ((laxInternalPushforward F hF RC RD ψ).obj M)).val.obj U) x) =
      ((ψ.hom.app U).hom r : (sectionRings.{u, uD, vD} K RD).obj (F.op.obj U)) •
        (@id (((sectionModuleEquivalence.{u, uD, vD} K RD).functor.obj M).val.obj
          (F.op.obj U)) x) := by
  sorry

/-- The uniquely normalized internal/sectionwise direct-image comparison.
Source: Stacks Tag 03D6, DAG proof Steps 3–4
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
noncomputable def laxSectionComparison :
    laxInternalPushforward F hF RC RD ψ ⋙ (sectionModuleEquivalence.{u, uC, vC} J RC).functor ≅
      (sectionModuleEquivalence.{u, uD, vD} K RD).functor ⋙ laxSectionPushforward F hF RC RD ψ :=
  Classical.choose (laxSectionComparison_existsUnique F hF RC RD ψ).exists

section Composition

variable {H : Type uH} [Category.{vH} H] {L : GrothendieckTopology H}
  [UnivLE.{max uH vH, u}] [HasSheafify L AddCommGrpCat.{u}]
  [(L.W (A := AddCommGrpCat.{u})).IsMonoidal]
  (G : D ⥤ H)
  (hG : ∀ M : Sheaf L AddCommGrpCat.{u}, Presheaf.IsSheaf K (G.op ⋙ M.obj))
  (T : C ⥤ H)
  (hT : ∀ M : Sheaf L AddCommGrpCat.{u}, Presheaf.IsSheaf J (T.op ⋙ M.obj))
  (κ : T ≅ F ⋙ G)

/-- The compositor on an underlying sheaf is restriction along κ, contravariantly.
Source: DAG proof Step 5, general-site compositor calculation
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxRestrictionCompositor (M : Sheaf L AddCommGrpCat.{u}) :
    (Sheaf.coefficientRestriction F hF).obj
        ((Sheaf.coefficientRestriction G hG).obj M) ≅
      (Sheaf.coefficientRestriction T hT).obj M :=
  ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op κ) M.obj)

/-- The actual compositor respects the transported monoid structures.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Precompose its tensor equation with the actual sheafification generator.
The generator comparisons for F, G and T reduce it to naturality of the generator
along κ. The unit equation reduces to naturality of the unit generator. Uniqueness
of sheaf extensions gives the monoidal equations, hence the monoid-map laws. -/
@[instance] theorem laxRestrictionCompositor_isMonHom
    (RH : Sheaf L AddCommGrpCat.{u}) [MonObj RH] :
    IsMonHom (laxRestrictionCompositor F hF G hG T hT κ RH).hom := by
  sorry

variable (RH : Sheaf L AddCommGrpCat.{u}) [MonObj RH] [IsCommMonObj RH]
  (θ : RD ⟶ (Sheaf.coefficientRestriction G hG).obj RH) [IsMonHom θ]

/-- The coefficient map of the composite, with the actual κ component.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxCompositeCoefficient : RC ⟶ (Sheaf.coefficientRestriction T hT).obj RH :=
  ψ ≫ (Sheaf.coefficientRestriction F hF).map θ ≫
    (laxRestrictionCompositor F hF G hG T hT κ RH).hom

/-- The composite coefficient is a monoid morphism.
Source: DAG proof Step 5
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. ψ and θ are monoid morphisms; lax monoidal transport preserves the latter
property. The compositor is a monoid morphism by the generator calculation.
Compose these three monoid morphisms. -/
@[instance] theorem laxCompositeCoefficient_isMonHom :
    IsMonHom (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ) := by
  sorry

/-- Reconstructed ring maps and normalized module comparisons commute with arbitrary
specified compositors, including the literal composite.
Source: Stacks Tag 03D6, DAG proof Steps 5–7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Step 5 gives the monoid compositor. On sections the composite ring map has
additive map RH(κ_V) θ_FV ψ_V; uniqueness of reconstruction proves the ring equality.
For a module N, semilinear naturality along κ_V identifies its two actions, so
N(κ_V) and its inverse give linear compositors on both sides. Full faithfulness of
reconstruction also lifts the sectionwise compositor internally. Every path in
the comparison square sends n to N(κ_V)(n), proving the asserted square. -/
theorem laxSectionPushforward_composition :
    laxSectionRingMap T hT RC RH
        (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ) =
      laxSectionRingMap F hF RC RD ψ ≫
        Functor.whiskerLeft F.op (laxSectionRingMap G hG RD RH θ) ≫
          Functor.whiskerRight (NatTrans.op κ.hom) (sectionRings.{u, uH, vH} L RH) ∧
    ∃ i : laxInternalPushforward G hG RD RH θ ⋙
        laxInternalPushforward F hF RC RD ψ ≅
        laxInternalPushforward T hT RC RH
          (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ),
    ∃ s : laxSectionPushforward G hG RD RH θ ⋙
        laxSectionPushforward F hF RC RD ψ ≅
        laxSectionPushforward T hT RC RH
          (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ),
      (∀ (M : Mod (Sheaf L AddCommGrpCat.{u}) RH) (U : Cᵒᵖ),
        (i.hom.app M).hom.hom.app U = M.X.obj.map (κ.hom.app U.unop).op) ∧
      (∀ (M : SheafOfModules.{u}
          ((sheafCompose L (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uH, vH} L RH)))
          (U : Cᵒᵖ),
        ((s.hom.app M).val.app U).hom.toAddMonoidHom =
          (M.val.presheaf.map (κ.hom.app U.unop).op).hom) ∧
      (∀ M : Mod (Sheaf L AddCommGrpCat.{u}) RH,
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor.map (i.hom.app M) ≫
          (laxSectionComparison T hT RC RH
            (laxCompositeCoefficient F hF RC RD ψ G hG T hT κ RH θ)).hom.app M =
        (laxSectionComparison F hF RC RD ψ).hom.app
            ((laxInternalPushforward G hG RD RH θ).obj M) ≫
          (laxSectionPushforward F hF RC RD ψ).map
            ((laxSectionComparison G hG RD RH θ).hom.app M) ≫
          s.hom.app ((sectionModuleEquivalence.{u, uH, vH} L RH).functor.obj M)) := by
  sorry

end Composition

omit [UnivLE.{max uD vD, u}]

/-- Reconstruction and its fixed quasi-inverse are additive and exact, and reflect
exact sequences in both directions. This applies separately on every site.
Source: Stacks Tag 03DA, DAG proof Steps 8–9
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Reconstruction preserves the underlying additive maps, hence their sums.
Faithfulness, bilinearity of composition and the equivalence counit imply
additivity of its quasi-inverse. Additive equivalences preserve kernels and
cokernels, and hence exact sequences. Equivalences preserve all finite limits and
colimits. Applying the opposite equivalence and its unit/counit reflects exactness,
since exactness is invariant under isomorphism of short complexes. -/
theorem sectionModuleEquivalence_additive_exact :
    (sectionModuleEquivalence.{u, uC, vC} J RC).functor.Additive ∧
    (sectionModuleEquivalence.{u, uC, vC} J RC).inverse.Additive ∧
    PreservesFiniteLimits (sectionModuleEquivalence.{u, uC, vC} J RC).functor ∧
    PreservesFiniteColimits (sectionModuleEquivalence.{u, uC, vC} J RC).functor ∧
    PreservesFiniteLimits (sectionModuleEquivalence.{u, uC, vC} J RC).inverse ∧
    PreservesFiniteColimits (sectionModuleEquivalence.{u, uC, vC} J RC).inverse ∧
    (∀ S : ShortComplex (Mod (Sheaf J AddCommGrpCat.{u}) RC),
      S.Exact ↔ (S.map (sectionModuleEquivalence.{u, uC, vC} J RC).functor).Exact) ∧
    (∀ S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uC, vC} J RC))),
      S.Exact ↔ (S.map (sectionModuleEquivalence.{u, uC, vC} J RC).inverse).Exact) := by
  sorry

/-- The identity coefficient map has identity additive sections, with its actual
transported target monoid. Source: DAG proof Step 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence). -/
def laxIdentityCoefficient : RC ⟶
    (Sheaf.coefficientRestriction (𝟭 C)
      (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)).obj RC :=
  ⟨𝟙 RC.obj⟩

/-- The identity coefficient map respects the normalized lax structure.
Source: DAG proof Steps 5 and 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. The generator equations identify the identity restriction multiplication
and unit with those of RC. Its identity additive map respects both. -/
@[instance] theorem laxIdentityCoefficient_isMonHom :
    IsMonHom (laxIdentityCoefficient RC) := by
  sorry

/-- Identity comparisons agree with the identity internal and sectionwise
compositors. Source: DAG proof Step 7
(blueprint: lem-sfb-section-ring-lax-pushforward-coherence).

Proof. Both identity direct images have the original action on every section.
Thus identity maps give the two unit compositors. Reconstruction of the identity
coefficient map is the identity by uniqueness. The comparison followed by the
sectionwise unitor and reconstruction of the internal unitor have identical
section maps, proving agreement. -/
theorem laxSectionPushforward_identity :
    laxSectionRingMap (𝟭 C) (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
      RC RC (laxIdentityCoefficient RC) = 𝟙 (sectionRings.{u, uC, vC} J RC) ∧
    ∃ i : laxInternalPushforward (𝟭 C)
        (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
        RC RC (laxIdentityCoefficient RC) ≅ 𝟭 _,
    ∃ s : laxSectionPushforward (𝟭 C)
        (fun M : Sheaf J AddCommGrpCat.{u} ↦ M.property)
        RC RC (laxIdentityCoefficient RC) ≅ 𝟭 _,
      (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) RC, (i.hom.app M).hom = 𝟙 M.X) ∧
      (∀ (M : SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (sectionRingSheaf.{u, uC, vC} J RC)))
          (U : Cᵒᵖ), ((s.hom.app M).val.app U).hom.toAddMonoidHom =
            AddMonoidHom.id _) ∧
      (∀ M : Mod (Sheaf J AddCommGrpCat.{u}) RC,
        (sectionModuleEquivalence.{u, uC, vC} J RC).functor.map (i.hom.app M) =
          (laxSectionComparison (𝟭 C) (fun N : Sheaf J AddCommGrpCat.{u} ↦ N.property)
              RC RC (laxIdentityCoefficient RC)).hom.app M ≫
            s.hom.app ((sectionModuleEquivalence.{u, uC, vC} J RC).functor.obj M)) := by
  sorry

end CategoryTheory.InternalAbelianSheafModule
