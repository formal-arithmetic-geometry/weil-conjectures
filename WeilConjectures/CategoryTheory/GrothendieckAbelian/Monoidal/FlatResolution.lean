/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!

# Functorial flat resolutions and flat separators

The K-flat left derivability structure computes the derived pullback on a K-flat
resolution, so it requires the sheaf categories to admit functorial flat resolutions
for the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

## The criterion

The file is organized around the criterion
`CategoryTheory.Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator`: a
Grothendieck abelian category with a braided closed monoidal structure
admits functorial flat resolutions if and only if it has a *flat separator*.

The backward implication is the useful one. Given a flat separator `G`, the copower
adjunction `CategoryTheory.Limits.sigmaConstAdj G : (∐_{-} G) ⊣ Hom(G, -)` already has
everything: its counit at `X` is the canonical map `∐_{g : G ⟶ X} G ⟶ X`, which is an
epimorphism exactly because `G` is a separator (`isSeparator_iff_epi`), and it is
functorial in `X` by construction, so the only thing left to check is that its source is
flat. That is `ObjectProperty.flat_coproduct` of
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`: tensoring on the left with `∐ f`
is, since `curriedTensor A` preserves the coproduct, the pointwise colimit of the
`tensorLeft (f i)`, and a colimit of shape `Discrete I` of left exact functors is left
exact because a Grothendieck abelian category satisfies `AB4`. The forward implication
reads off a flat separator from a functorial flat resolution of an arbitrary separator:
the flat cover of a separator is again a separator, since it maps onto it epimorphically.

Only left exactness has to be tracked in all of this: in a *closed* monoidal category
`tensorLeft X` is a left adjoint, hence automatically preserves colimits, and the
braiding carries everything from `tensorLeft` to `tensorRight`. This is
`ObjectProperty.flat_iff_preservesFiniteLimits`, in the same file.

On the coefficient side the criterion is immediately enough: the free module of rank one
is a flat separator of `ModuleCat.{u} Λ`, so `ModuleCat.hasFunctorialFlatResolution`
supplies the functorial flat resolutions that the étale six-functor files ask of their
coefficient category.

## The sheaf case

With the criterion in hand, the sheaf statement reduces to the transfer of flat
separators along the site, `exists_flat_separator_sheaf_of_essentiallySmall`. As in the
sibling files it is stated for an arbitrary site `C` with `Hom`-types in the universe `u` and
objects in `u + 1` which is essentially small in `u + 1`; the small étale site and the small
pro-étale site are such sites, so the étale and pro-étale instances are obtained from the
general one by `inferInstance`.

For an object `U` of `C` and a flat separator `G` of `A`, let `G_U` be the free presheaf
`V ↦ ∐_{V ⟶ U} G`, so that `Hom (G_U, F) ≅ Hom (G, F(U))`. Its sheafification `L G_U` is flat:
tensoring with it is `F ↦ L (G_U ⊗ F)`, and the objectwise tensor product with `G_U` is left
exact because each `G_U(V)` is a coproduct of copies of `G`
(`CategoryTheory.GrothendieckTopology.flat_presheafToSheaf_obj`). The sheaves `L G_U`, for `U`
ranging over a small model of the site, form a separating family, so their coproduct is a flat
separator of `Sheaf J A`. On the small étale site with `A = ModuleCat.{u + 1} Λ` this is the
construction by local free covers `⊕ j_{U!} Λ_U` of the Stacks Project, Tag 06YL.

## Main results

- `CategoryTheory.Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator`:
  functorial flat resolutions exist exactly when there is a flat separator.
- `ModuleCat.hasFunctorialFlatResolution`: `ModuleCat.{u} Λ` admits functorial flat
  resolutions, over a commutative ring `Λ : Type u`.
- `CategoryTheory.GrothendieckTopology.exists_flat_separator_sheaf_of_essentiallySmall`:
  a flat separator of the coefficient category induces one of the sheaf category, hence
  `CategoryTheory.GrothendieckTopology.hasFunctorialFlatResolution_sheaf_of_essentiallySmall`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.Abelian

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- A flat separator gives functorial flat resolutions: the counit of the copower
adjunction `sigmaConstAdj G` is the functorial map `∐_{g : G ⟶ X} G ⟶ X`, an epimorphism
because `G` is a separator and with flat source because `G` is flat. -/
theorem hasFunctorialFlatResolution_of_flat_separator {G : A} (hG : IsSeparator G)
    (hG' : ObjectProperty.flat G) : HasFunctorialFlatResolution A :=
  ⟨{ F := ObjectProperty.lift _ (coyoneda.obj (op G) ⋙ sigmaConst.obj G)
        (fun _ ↦ ObjectProperty.flat_coproduct _ (fun _ ↦ hG'))
     π := (sigmaConstAdj G).counit
     epi_π_app X := (isSeparator_iff_epi G).1 hG X }⟩

omit [BraidedCategory A] [MonoidalClosed A] in
/-- Functorial flat resolutions give a flat separator: resolve an arbitrary separator, and
use that anything mapping epimorphically onto a separator is a separator. -/
theorem exists_flat_separator_of_hasFunctorialFlatResolution
    [h : HasFunctorialFlatResolution A] :
    ∃ G : A, IsSeparator G ∧ ObjectProperty.flat G := by
  obtain ⟨Λ⟩ := h
  refine ⟨(Λ.F.obj (separator A)).obj, ?_, (Λ.F.obj (separator A)).property⟩
  rw [isSeparator_def]
  intro X Y f g hfg
  refine (isSeparator_separator A).def f g (fun k ↦ ?_)
  have := hfg (Λ.π.app (separator A) ≫ k)
  simpa using (cancel_epi (Λ.π.app (separator A))).1 (by simpa using this)

/-- A Grothendieck abelian category with a braided closed monoidal structure
admits functorial flat resolutions if and only if it has a flat separator; see the module
docstring. -/
theorem hasFunctorialFlatResolution_iff_exists_flat_separator :
    HasFunctorialFlatResolution A ↔ ∃ G : A, IsSeparator G ∧ ObjectProperty.flat G :=
  ⟨fun _ ↦ exists_flat_separator_of_hasFunctorialFlatResolution A,
    fun ⟨_, hG, hG'⟩ ↦ hasFunctorialFlatResolution_of_flat_separator A hG hG'⟩

end CategoryTheory.Abelian

namespace ModuleCat

instance hasFunctorialFlatResolution (Λ : Type u) [CommRing Λ] :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} Λ) :=
  (Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator _).mpr
    ⟨ModuleCat.of Λ (Shrink.{u} Λ), ModuleCat.isSeparator.{u, u} Λ,
      ObjectProperty.prop_of_iso _
        (Shrink.linearEquiv.{u, u, u} Λ Λ).toModuleIso.symm
        (ObjectProperty.prop_unit _)⟩

end ModuleCat

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/- The monoidal structure on the coefficient category, as in the sibling file
`TensorColimits`: preadditive, symmetric and closed. The symmetry and closedness are what
make `Sheaf J A` itself monoidal closed, which is one of the hypotheses of
`Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator` below. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

omit [MonoidalPreadditive A] in
/-- The sheafification of a presheaf with flat values is flat: tensoring with it is
`F ↦ L (P ⊗ F)`, the composite of the inclusion of sheaves into presheaves, the objectwise
tensor product with `P` and sheafification, each of which is left exact. -/
lemma flat_presheafToSheaf_obj (P : Cᵒᵖ ⥤ A) (hP : ∀ U, ObjectProperty.flat (P.obj U)) :
    ObjectProperty.flat ((presheafToSheaf J A).obj P) := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have (U : Cᵒᵖ) : PreservesFiniteLimits (tensorLeft (P.obj U)) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).1 (hP U)
  have : PreservesFiniteLimits (tensorLeft P) :=
    preservesFiniteLimits_of_evaluation _ fun U ↦
      inferInstanceAs (PreservesFiniteLimits ((evaluation Cᵒᵖ A).obj U ⋙ tensorLeft (P.obj U)))
  let e : tensorLeft ((presheafToSheaf J A).obj P) ≅
      sheafToPresheaf J A ⋙ tensorLeft P ⋙ presheafToSheaf J A :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (sheafToPresheaf J A) (Sheaf.presheafToSheafCompTensorLeftIso P)
  exact preservesFiniteLimits_of_natIso e.symm

variable {A} in
/-- The free presheaf `V ↦ ∐_{V ⟶ U} G` on an object `U` of the site with values in an object
`G` of `A`: morphisms out of it into a presheaf `F` are the morphisms `G ⟶ F(U)`. -/
noncomputable abbrev freePresheaf (U : C) (G : A) : Cᵒᵖ ⥤ A :=
  CategoryTheory.yoneda.obj U ⋙ uliftFunctor.{u + 1} ⋙ sigmaConst.obj G

variable {A} in
/-- The morphism `∐_{V ⟶ U} G ⟶ F(V)` out of the free presheaf induced by a morphism
`G ⟶ F(U)`. -/
noncomputable def freePresheafDesc {U : C} {G : A} {F : Cᵒᵖ ⥤ A} (h : G ⟶ F.obj (op U)) :
    freePresheaf U G ⟶ F where
  app V := Sigma.desc fun φ ↦ h ≫ F.map φ.down.op
  naturality V W ψ := Sigma.hom_ext _ _ fun φ ↦ by
    simp [sigmaConst, ← Functor.map_comp]
    rfl

omit [EssentiallySmall.{u + 1} C] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] in
variable {A} in
@[reassoc (attr := simp)]
lemma ι_freePresheafDesc_app {U : C} {G : A} {F : Cᵒᵖ ⥤ A} (h : G ⟶ F.obj (op U)) (V : Cᵒᵖ)
    (φ : ULift.{u + 1} (V.unop ⟶ U)) :
    Sigma.ι (fun _ ↦ G) φ ≫ (freePresheafDesc h).app V = h ≫ F.map φ.down.op :=
  Sigma.ι_desc (fun φ : ULift.{u + 1} (V.unop ⟶ U) ↦ h ≫ F.map φ.down.op) φ

omit [EssentiallySmall.{u + 1} C] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] in
variable {A} in
/-- Two morphisms out of `F` agree on a morphism `h : G ⟶ F(U)` as soon as they agree after
composition with the morphism out of the free presheaf induced by `h`. -/
lemma comp_app_eq_of_freePresheafDesc_comp_eq {U : C} {G : A} {F F' : Cᵒᵖ ⥤ A}
    (h : G ⟶ F.obj (op U)) {α β : F ⟶ F'}
    (H : freePresheafDesc h ≫ α = freePresheafDesc h ≫ β) :
    h ≫ α.app (op U) = h ≫ β.app (op U) := by
  let ι : G ⟶ (freePresheaf U G).obj (op U) :=
    Sigma.ι (fun _ : ULift.{u + 1} (U ⟶ U) ↦ G) (ULift.up (𝟙 U))
  have hι : ι ≫ (freePresheafDesc h).app (op U) = h :=
    (ι_freePresheafDesc_app h (op U) (ULift.up (𝟙 U))).trans (by simp)
  calc h ≫ α.app (op U) = ι ≫ (freePresheafDesc h).app (op U) ≫ α.app (op U) := by
        rw [← Category.assoc, hι]
    _ = ι ≫ (freePresheafDesc h).app (op U) ≫ β.app (op U) := by
        rw [← NatTrans.comp_app, H, NatTrans.comp_app]
    _ = h ≫ β.app (op U) := by rw [← Category.assoc, hι]

omit [MonoidalPreadditive A] in
/-- A flat separator of the coefficient category `A` induces a flat separator of the
category of `A`-valued sheaves on an essentially small site, obtained by applying
extension by zero to it and summing over the site; see the module docstring. -/
theorem exists_flat_separator_sheaf_of_essentiallySmall
    (hA : ∃ G : A, IsSeparator G ∧ ObjectProperty.flat G) :
    ∃ G : Sheaf J A, IsSeparator G ∧ ObjectProperty.flat G := by
  obtain ⟨G, hG, hG'⟩ := hA
  let e := equivSmallModel.{u + 1} C
  let S : SmallModel.{u + 1} C → Sheaf J A := fun U ↦
    (presheafToSheaf J A).obj (freePresheaf (e.inverse.obj U) G)
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{_, _, u + 1} (Sheaf J A)
    (SmallModel.{u + 1} C)
  refine ⟨∐ S, ?_, ObjectProperty.flat_coproduct _ fun U ↦
    flat_presheafToSheaf_obj A J _ fun V ↦ ObjectProperty.flat_coproduct _ fun _ ↦ hG'⟩
  rw [isSeparator_sigma]
  intro X Y f g hfg
  have key (U : SmallModel.{u + 1} C) :
      f.hom.app (op (e.inverse.obj U)) = g.hom.app (op (e.inverse.obj U)) := by
    refine hG.def _ _ fun k ↦ ?_
    have h := congrArg ((sheafificationAdjunction J A).homEquiv _ _)
      (hfg (S U) (ObjectProperty.ofObj_apply _ U)
        (((sheafificationAdjunction J A).homEquiv _ _).symm (freePresheafDesc k)))
    simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] at h
    exact comp_app_eq_of_freePresheafDesc_comp_eq k h
  ext ⟨W⟩ : 3
  let i : W ≅ e.inverse.obj (e.functor.obj W) := e.unitIso.app W
  rw [← cancel_epi (X.obj.map i.hom.op), f.hom.naturality, g.hom.naturality]
  exact congrArg (· ≫ _) (key (e.functor.obj W))

/-- Functorial flat resolutions of `A`-valued sheaves on an essentially small site: by
`Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator` this is the existence of a
flat separator of `Sheaf J A`, which `exists_flat_separator_sheaf_of_essentiallySmall`
produces from a flat separator of `A`. -/
instance hasFunctorialFlatResolution_sheaf_of_essentiallySmall
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf J A) :=
  (Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator _).2
    (exists_flat_separator_sheaf_of_essentiallySmall A J
      ((Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator A).1 ‹_›))

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- Functorial flat resolutions of `A`-valued étale sheaves: the instance above applied to
the essentially small small étale site. -/
instance Etale.hasFunctorialFlatResolution_sheaf [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

/-- Functorial flat resolutions of `A`-valued pro-étale sheaves: the instance above applied
to the essentially small small pro-étale site. -/
instance ProEtale.hasFunctorialFlatResolution_sheaf [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology Y) A) :=
  inferInstance

end AlgebraicGeometry
