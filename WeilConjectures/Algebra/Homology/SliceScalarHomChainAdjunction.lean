/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.StrictScalarHomChain
import all WeilConjectures.Algebra.Homology.StrictScalarHomChain
import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Slice-normalized scalar adjunction for product Hom complexes

Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03DH and 04IX;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction).

The interfaces below reuse the existing scalar extension, tensor and actual Hom
product projections. They specify the ordinary slice adjunctions and precisely
the nu/theta portion of the scalar-Hom comparison, without its evaluation square.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.StrictScalarHom

attribute [local irreducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection tensorSection evaluate homMap

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}]

/-- The normalized ordinary scalar adjunction, including its inverse on generators.
Source: Stacks 03CZ and 03CY
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure NormalizedOrdinaryAdjunction {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) where
  /-- Sheafified sectionwise scalar extension, with its prescribed maps. -/
  extension : Extension.{c, v, u} φ
  /-- The ordinary adjunction supplies mutually inverse, composition-natural bijections. -/
  adjunction : extension.functor ⊣
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  /-- The forward formula at every object. -/
  forward : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g : extension.functor.obj M ⟶ L) (V : Cᵒᵖ) (x : M.val.obj V),
    (adjunction.homEquiv M L g).val.app V x =
      g.val.app V ((eqToHom (extension.obj_eq M).symm).val.app V
        (scalarExtensionSection φ M V 1 x))
  /-- The inverse is the S-linear extension of s tensor x mapping to s h(x). -/
  inverse : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (h : M ⟶ (restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj L)
    (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V),
    ((adjunction.homEquiv M L).symm h).val.app V
        ((eqToHom (extension.obj_eq M).symm).val.app V
          (scalarExtensionSection φ M V s x)) = s • (@id (L.val.obj V) (h.val.app V x))
  /-- Additivity of the bijection, in addition to its inverse and naturality laws. -/
  additive : ∀ (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g h : extension.functor.obj M ⟶ L),
    adjunction.homEquiv M L (g + h) =
      adjunction.homEquiv M L g + adjunction.homEquiv M L h

/-- The two normalized chain isomorphisms, with both directions of theta specified.
Source: Stacks 03CY, 03CZ and 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure ScalarHomAdjunctionChains {R S : Sheaf J CommRingCat.{max c v u}}
    {φ : R ⟶ S} (E : Extension.{c, v, u} φ) where
  /-- Identity on the tensor generators, natural as a chain isomorphism. -/
  nu : tensor.{c, v, u} φ ≅ E.complex ⋙ restriction.{c, v, u} φ
  /-- The generator normalization of nu. -/
  nu_pure : ∀ (A : Complex.{c, v, u} R) (n : ℤ) (V : Cᵒᵖ)
    (s : S.obj.obj V) (x : (A.X n).val.obj V),
    (((nu.app A).hom.f n).val.app V) (tensorSection.{c, v, u} φ A n V s x) =
      E.section A n V s x
  /-- An R-linear chain isomorphism of the actual unbounded product Hom complexes. -/
  theta : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S),
    (restriction.{c, v, u} φ).obj (homComplex (R := S) (E.complex.obj P) N) ≅
      homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)
  /-- Forward theta, using the actual product projection and slice identity. -/
  theta_forward : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (g : ((homComplex (R := S) (E.complex.obj P) N).X n).val.obj V)
    (x : (P.X i).val.obj V),
    evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V
        ((((theta P N).hom.f n).val.app V) g) x =
      evaluate.{c, v, u} (E.complex.obj P) N n i k h V g (E.section P i V 1 x)
  /-- Inverse theta on every local tensor generator, for an arbitrary product family. -/
  theta_inverse : ∀ (P : Complex.{c, v, u} R) (N : Complex.{c, v, u} S)
    (n i k : ℤ) (h : i + n = k) (V : Cᵒᵖ)
    (f : ((homComplex (R := R) P ((restriction.{c, v, u} φ).obj N)).X n).val.obj V)
    (s : S.obj.obj V) (x : (P.X i).val.obj V),
    evaluate.{c, v, u} (E.complex.obj P) N n i k h V
        ((((theta P N).inv.f n).val.app V) f) (E.section P i V s x) =
      s • (@id ((N.X k).val.obj V)
        (evaluate.{c, v, u} P ((restriction.{c, v, u} φ).obj N) n i k h V f x))
  /-- Naturality contravariantly in P and covariantly in N, before localization. -/
  theta_natural : ∀ (P P' : Complex.{c, v, u} R) (N N' : Complex.{c, v, u} S)
    (a : P' ⟶ P) (b : N ⟶ N'),
    (restriction.{c, v, u} φ).map (homMap.{c, v, u} (E.complex.map a) b) ≫
        (theta P' N').hom =
      (theta P N).hom ≫ homMap.{c, v, u} a ((restriction.{c, v, u} φ).map b)

open scoped ChangeOfRings

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

attribute [local semireducible] changeOfRingsOfUniverses changeOfRingsHomOfUniverses
  scalarExtensionSection evaluate

attribute [local instance] ordinaryExtension_additive
attribute [local irreducible] scalarSheafHomEquiv ordinaryAdjunction

private def extensionIso {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : ordinaryExtension.{c, v, u} φ ≅ E.functor := by
  let e : ordinaryExtension.{c, v, u} φ ≅ E.functor :=
    NatIso.ofComponents (fun M ↦ eqToIso (E.obj_eq M).symm) (by
      intro M N f
      change changeOfRingsHomOfUniverses φ M f ≫ eqToHom (E.obj_eq N).symm =
        eqToHom (E.obj_eq M).symm ≫ E.functor.map f
      rw [E.map_eq]
      simp)
  exact e

private def normalizedAdjunction {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : E.functor ⊣ moduleRestriction.{c, v, u} φ :=
  (ordinaryAdjunction.{c, v, u} φ).ofNatIsoLeft (extensionIso E)

private theorem normalizedForward {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (L : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (g : E.functor.obj M ⟶ L) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((normalizedAdjunction E).homEquiv M L g).val.app V x =
      g.val.app V ((eqToHom (E.obj_eq M).symm).val.app V
        (scalarExtensionSection φ M V 1 x)) := by
  rw [normalizedAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [ordinaryAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change (scalarSheafHomEquiv.{c, v, u} φ M L ((extensionIso E).hom.app M ≫ g)).val.app V x = _
  rw [scalarSheafHomEquiv_apply.{c, v, u}]
  rfl

attribute [local irreducible] normalizedAdjunction extensionIso

private def normalizedFor {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (E : Extension.{c, v, u} φ) : NormalizedOrdinaryAdjunction.{c, v, u} φ where
  extension := E
  adjunction := normalizedAdjunction E
  forward := normalizedForward E
  inverse := by
    intro M L h V s x
    have he := congrArg (fun t ↦ t.val.app V x)
      (((normalizedAdjunction E).homEquiv M L).apply_symm_apply h)
    rw [normalizedForward] at he
    have hs := scalarExtensionSection_smul φ M V s 1 x
    rw [mul_one] at hs
    rw [← hs]
    erw [map_smul, map_smul]
    exact congrArg (fun z : L.val.obj V ↦ s • z) he
  additive := by
    intro M L g h
    ext V x
    rw [normalizedForward]
    change g.val.app V _ + h.val.app V _ = _
    rw [← normalizedForward E M L g V x, ← normalizedForward E M L h V x]
    rfl

attribute [local irreducible] normalizedFor ordinaryExtension canonicalExtension

private def chainsFromData {R S : Sheaf J CommRingCat.{max c v u}} {φ : R ⟶ S}
    (D : Data.{c, v, u} φ) : ScalarHomAdjunctionChains.{c, v, u} D.extension where
  nu := D.nu
  nu_pure := D.nu_pure
  theta := D.theta
  theta_forward := D.theta_evaluate
  theta_natural := D.theta_natural
  theta_inverse := by
    intro P N n i k h V f s x
    let g := (((D.theta P N).inv.f n).val.app V) f
    have he : ((((D.theta P N).hom.f n).val.app V) g) = f := by
      have hh := congrArg (fun t ↦ (t.f n).val.app V f) (D.theta P N).inv_hom_id
      exact hh
    have hx := D.theta_evaluate P N n i k h V g x
    rw [he] at hx
    have hs : D.extension.section P i V s x = s • D.extension.section P i V 1 x := by
      dsimp only [Extension.section]
      have hs := scalarExtensionSection_smul φ (P.X i) V s 1 x
      rw [mul_one] at hs
      rw [← hs]
      exact map_smul _ _ _
    rw [hs]
    change (((homComplexπ (R := S) (D.extension.complex.obj P) N n i k h).val.app V
      g).app (op (Over.mk (𝟙 V.unop)))).hom (s • _) = _
    rw [map_smul]
    exact congrArg (fun z : (N.X k).val.obj V ↦ s • z) hx.symm


universe a b d e r

section RestrictionComparison
variable {C₀ : Type a} [Category.{b} C₀] {D₀ : Type d} [Category.{e} D₀]
  {J₀ : GrothendieckTopology C₀} {K₀ : GrothendieckTopology D₀}
  (F : C₀ ⥤ D₀) [Functor.IsContinuous F J₀ K₀] [F.IsCocontinuous J₀ K₀]
  [J₀.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J₀ AddCommGrpCat.{r}]
  [K₀.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K₀ AddCommGrpCat.{r}]
  (A : Sheaf K₀ RingCat.{r})

private abbrev restrictedRing := (F.sheafPushforwardContinuous RingCat.{r} J₀ K₀).obj A

private def rawRestriction : PresheafOfModules.{r} A.obj ⥤
    PresheafOfModules.{r} (restrictedRing (J₀ := J₀) F A).obj :=
  PresheafOfModules.pushforward (F := F) (𝟙 _)

private def moduleRestrictionF : SheafOfModules.{r} A ⥤
    SheafOfModules.{r} (restrictedRing (J₀ := J₀) F A) :=
  pushforward (F := F) (𝟙 _)

private def restrictionSheafify (P : PresheafOfModules.{r} A.obj) :
    (PresheafOfModules.sheafification (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).obj
      ((rawRestriction F A).obj P) ⟶
    (moduleRestrictionF F A).obj
      ((PresheafOfModules.sheafification (R := A) (𝟙 _)).obj P) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).homEquiv _ _).symm
      ((rawRestriction F A).map
        ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).unit.app P))

omit [F.IsCocontinuous J₀ K₀] in
private theorem restrictionSheafify_unit (P : PresheafOfModules.{r} A.obj) :
    toSheafify J₀ ((rawRestriction F A).obj P).presheaf ≫
      (PresheafOfModules.toPresheaf _).map (restrictionSheafify (J₀ := J₀) F A P).val =
    Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf) := by
  have h := ((PresheafOfModules.sheafificationAdjunction
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)).homEquiv
      ((rawRestriction F A).obj P)
      ((moduleRestrictionF F A).obj
        ((PresheafOfModules.sheafification (R := A) (𝟙 _)).obj P))).apply_symm_apply
      ((rawRestriction F A).map
        ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (restrictedRing (J₀ := J₀) F A).obj).map) h

private theorem restrictionSheafify_isIso (P : PresheafOfModules.{r} A.obj) :
    IsIso (restrictionSheafify (J₀ := J₀) F A P) := by
  let η := toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf
  let t := (PresheafOfModules.toPresheaf (restrictedRing (J₀ := J₀) F A).obj).map
    (restrictionSheafify (J₀ := J₀) F A P).val
  have hi : Presheaf.IsLocallyInjective J₀
      (Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker J₀ K₀ F _
  have hs : Presheaf.IsLocallySurjective J₀
      (Functor.whiskerLeft F.op (toSheafify K₀ P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker J₀ K₀ F _
  have hi' : Presheaf.IsLocallyInjective J₀ t := by
    rw [← Presheaf.comp_isLocallyInjective_iff J₀ η t]
    change Presheaf.IsLocallyInjective J₀
      (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (restrictionSheafify (J₀ := J₀) F A P).val)
    rw [restrictionSheafify_unit (J₀ := J₀) F A P]
    exact hi
  have hs' : Presheaf.IsLocallySurjective J₀ t := by
    rw [← Presheaf.comp_isLocallySurjective_iff J₀ η t]
    change Presheaf.IsLocallySurjective J₀
      (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf ≫
        (PresheafOfModules.toPresheaf _).map
          (restrictionSheafify (J₀ := J₀) F A P).val)
    rw [restrictionSheafify_unit (J₀ := J₀) F A P]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (restrictedRing (J₀ := J₀) F A))]
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi', hs'⟩

attribute [local irreducible] restrictionSheafify

variable [K₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R₀ S₀ : Sheaf K₀ CommRingCat.{r}} (φ₀ : R₀ ⟶ S₀)

private abbrev pullRing := F.sheafPushforwardContinuous CommRingCat.{r} J₀ K₀

private def scalarRawIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsPresheafOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (rawRestriction (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsPresheafOfUniverses φ₀ M) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    exact (changeOfRingsMap_tmulOfUniverses
      ((pullRing (J₀ := J₀) F).map φ₀) _ f 1 x).trans
      (changeOfRingsMap_tmulOfUniverses φ₀ M (F.op.map f) 1 x).symm)

private theorem scalarRawIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (scalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
      (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x) =
      s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x := rfl

attribute [local irreducible] scalarRawIso

private def scalarBackHom
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ⟶
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsOfUniverses φ₀ M) :=
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let T := PresheafOfModules.sheafification
    (R := restrictedRing (J₀ := J₀) F A) (𝟙 _)
  T.map (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
    restrictionSheafify (J₀ := J₀) F A (changeOfRingsPresheafOfUniverses φ₀ M)

private theorem scalarBackHom_eq
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    scalarBackHom (J₀ := J₀) F φ₀ M =
      (PresheafOfModules.sheafification
        (R := restrictedRing (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
        (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
        restrictionSheafify (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
          (changeOfRingsPresheafOfUniverses φ₀ M) := rfl

attribute [local irreducible] scalarBackHom

private theorem scalarBackHom_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (scalarBackHom (J₀ := J₀) F φ₀ M).val.app X
        (scalarExtensionSection ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      scalarExtensionSection φ₀ M (F.op.obj X) s x := by
  let A := (sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀
  let P := changeOfRingsPresheafOfUniverses φ₀ M
  let Q := changeOfRingsPresheafOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
    ((moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M)
  let b := PresheafOfModules.sheafificationAdjunction (R := restrictedRing (J₀ := J₀) F A)
    (𝟙 _)
  have hn := b.unit.naturality (scalarRawIso (J₀ := J₀) F φ₀ M).hom
  have hu := restrictionSheafify_unit (J₀ := J₀) (K₀ := K₀) F A P
  have hn' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hn
  change (toSheafify J₀ ((rawRestriction (J₀ := J₀) F A).obj P).presheaf).app X
      ((scalarRawIso (J₀ := J₀) F φ₀ M).hom.app X
        (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) = _ at hn'
  rw [scalarRawIso_pure] at hn'
  have hu' := congrArg (fun t ↦ t.app X
    (s ⊗ₜ[R₀.obj.obj (F.op.obj X), (φ₀.hom.app (F.op.obj X)).hom] x)) hu
  have hn'' := congrArg (fun z ↦ (restrictionSheafify (J₀ := J₀) F A P).val.app X z) hn'
  change (scalarBackHom (J₀ := J₀) F φ₀ M).val.app X
      (scalarExtensionSection _ _ X s x) = _
  rw [scalarBackHom_eq]
  change (restrictionSheafify (J₀ := J₀) F A P).val.app X
    (((PresheafOfModules.sheafification (𝟙 _)).map (scalarRawIso (J₀ := J₀) F φ₀ M).hom).val.app X
      (scalarExtensionSection ((pullRing (J₀ := J₀) F).map φ₀) _ X s x)) = _
  exact hn''.symm.trans hu'

private theorem scalarBackHom_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHomOfUniverses ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (scalarBackHom (J₀ := J₀) F φ₀ N) =
      (scalarBackHom (J₀ := J₀) F φ₀ M) ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHomOfUniverses φ₀ M g) := by
  apply scalarExtension_hom_ext
  intro X s x
  change (scalarBackHom (J₀ := J₀) F φ₀ N).val.app X
      ((changeOfRingsHomOfUniverses _ _ _).val.app X
        (scalarExtensionSection _ _ X s x)) =
    (changeOfRingsHomOfUniverses φ₀ M g).val.app (F.op.obj X)
      ((scalarBackHom (J₀ := J₀) F φ₀ M).val.app X (scalarExtensionSection _ _ X s x))
  rw [scalarExtension_map_tmul, scalarBackHom_pure, scalarBackHom_pure,
    scalarExtension_map_tmul]
  rfl


private theorem scalarBackHom_isIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    IsIso (scalarBackHom (J₀ := J₀) F φ₀ M) := by
  let := restrictionSheafify_isIso (J₀ := J₀) F
    ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
      (changeOfRingsPresheafOfUniverses φ₀ M)
  change IsIso (scalarBackHom (J₀ := J₀) F φ₀ M)
  rw [scalarBackHom_eq]
  change IsIso
    ((PresheafOfModules.sheafification
      (R := restrictedRing (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)) (𝟙 _)).map
      (scalarRawIso (J₀ := J₀) F φ₀ M).hom ≫
      restrictionSheafify (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)
        (changeOfRingsPresheafOfUniverses φ₀ M))
  infer_instance

private def scalarBackIso
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)) :
    changeOfRingsOfUniverses ((pullRing (J₀ := J₀) F).map φ₀)
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) ≅
      (moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).obj
          (changeOfRingsOfUniverses φ₀ M) := by
  letI := scalarBackHom_isIso (J₀ := J₀) F φ₀ M
  exact asIso (scalarBackHom (J₀ := J₀) F φ₀ M)

private theorem scalarBackIso_pure
    (M : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀))
    (X : C₀ᵒᵖ) (s : S₀.obj.obj (F.op.obj X)) (x : M.val.obj (F.op.obj X)) :
    (scalarBackIso (J₀ := J₀) F φ₀ M).hom.val.app X
        (scalarExtensionSection ((pullRing (J₀ := J₀) F).map φ₀)
          ((moduleRestrictionF (J₀ := J₀) F
            ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).obj M) X s x) =
      scalarExtensionSection φ₀ M (F.op.obj X) s x := by
  exact scalarBackHom_pure (J₀ := J₀) F φ₀ M X s x

private theorem scalarBackIso_natural
    {M N : SheafOfModules.{r} ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)}
    (g : M ⟶ N) :
    changeOfRingsHomOfUniverses ((pullRing (J₀ := J₀) F).map φ₀) _
        ((moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀)).map g) ≫
        (scalarBackIso (J₀ := J₀) F φ₀ N).hom =
      (scalarBackIso (J₀ := J₀) F φ₀ M).hom ≫
        (moduleRestrictionF (J₀ := J₀) F
          ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀)).map
            (changeOfRingsHomOfUniverses φ₀ M g) := by
  exact scalarBackHom_natural (J₀ := J₀) F φ₀ g

attribute [local irreducible] scalarBackIso

private def scalarExtensionF {D₁ : Type*} [Category D₁] {K₁ : GrothendieckTopology D₁}
    [K₁.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [K₁.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify K₁ AddCommGrpCat.{r}]
    {R₁ S₁ : Sheaf K₁ CommRingCat.{r}} (ψ : R₁ ⟶ S₁) :
    SheafOfModules.{r} ((sheafCompose K₁ (forget₂ CommRingCat RingCat)).obj R₁) ⥤
      SheafOfModules.{r} ((sheafCompose K₁ (forget₂ CommRingCat RingCat)).obj S₁) where
  obj M := changeOfRingsOfUniverses ψ M
  map f := changeOfRingsHomOfUniverses ψ _ f
  map_id M := scalarExtension_map_id ψ M
  map_comp f g := scalarExtension_map_comp ψ f g

private def scalarRestrictionIso :
    moduleRestrictionF (J₀ := J₀) F
        ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj R₀) ⋙
      scalarExtensionF ((pullRing (J₀ := J₀) F).map φ₀) ≅
    scalarExtensionF φ₀ ⋙ moduleRestrictionF (J₀ := J₀) F
      ((sheafCompose K₀ (forget₂ CommRingCat RingCat)).obj S₀) :=
  NatIso.ofComponents (fun M ↦ scalarBackIso (J₀ := J₀) F φ₀ M)
    (fun g ↦ scalarBackIso_natural (J₀ := J₀) F φ₀ g)

end RestrictionComparison

variable [∀ W : C, (J.over W).HasSheafCompose
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]
  [∀ W : C, (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [∀ W : C, HasWeakSheafify (J.over W) AddCommGrpCat.{max c v u}]

/-- The normalized adjunction on every slice, with comparisons under further restriction.
Source: Stacks 03CZ, 03CY, 03DH and 04IX
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction). -/
structure SliceScalarHomAdjunction {R S : Sheaf J CommRingCat.{max c v u}}
    (φ : R ⟶ S) where
  /-- Ordinary scalar extension on the original site. -/
  ordinary : NormalizedOrdinaryAdjunction.{c, v, u} φ
  /-- Ordinary adjunction for arbitrary module sheaves on each slice. -/
  slices : ∀ W : C, NormalizedOrdinaryAdjunction.{max c v, v, u}
    ((J.overPullback CommRingCat.{max c v u} W).map φ)
  /-- The unit-normalized comparison between restricted and slice extension. -/
  overIso : ∀ W : C,
    ordinary.extension.functor ⋙
        overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) W ≅
      overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) W ⋙
        (slices W).extension.functor
  /-- The comparison sends the sheafification image of s tensor x to itself. -/
  over_pure : ∀ (W : C)
    (M : ringedSiteModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Over W) (s : S.obj.obj (op V.left)) (x : M.val.obj (op V.left)),
    ((overIso W).hom.app M).val.app (op V)
        ((eqToHom (ordinary.extension.obj_eq M).symm).val.app (op V.left)
          (scalarExtensionSection φ M (op V.left) s x)) =
      (eqToHom ((slices W).extension.obj_eq (M.over W)).symm).val.app (op V)
        (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} W).map φ)
          (M.over W) (op V) s x)
  /-- Further slice restriction also commutes naturally with scalar extension. -/
  furtherIso : ∀ {V W : C} (a : V ⟶ W),
    (slices W).extension.functor ⋙
        overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) a ≅
      overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a ⋙
        (slices V).extension.functor
  /-- Normalization for arbitrary module sheaves on the slice, not only global ones. -/
  further_pure : ∀ {V W : C} (a : V ⟶ W)
    (M : ringedSiteModules.{max c v u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over W))
    (Z : Over V) (s : S.obj.obj (op Z.left))
    (x : M.val.obj (op ((Over.map a).obj Z))),
    ((furtherIso a).hom.app M).val.app (op Z)
        ((eqToHom ((slices W).extension.obj_eq M).symm).val.app
          (op ((Over.map a).obj Z))
            (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} W).map φ)
              M (op ((Over.map a).obj Z)) s x)) =
      ((eqToHom ((slices V).extension.obj_eq
        ((overMap.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).obj M)).symm).val.app
          (op Z))
        (scalarExtensionSection ((J.overPullback CommRingCat.{max c v u} V).map φ)
          ((overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a).obj M)
          (op Z) s x)
  /-- The normalized natural chain isomorphisms for the global extension. -/
  chains : ScalarHomAdjunctionChains.{c, v, u} ordinary.extension

attribute [local semireducible] normalizedFor ordinaryExtension canonicalExtension


/-- Slice scalar adjunction and its natural unbounded product-Hom chain isomorphism.
Source: Stacks Project, sites-modules.tex, Tags 03CZ, 03CY, 03DH and 04IX;
sites-cohomology.tex, Tag 0A8X
(blueprint: lem-sfb-slice-scalar-hom-chain-adjunction).

Proof:
1. On each slice, the forgetful functor is continuous and cocontinuous: covering
   sieves are the same arrows with their maps to the base object. The module
   sheafification comparison of lem-weil-pbc-slice-module-sheafification therefore
   identifies scalar extension with restricted scalar extension, preserving its unit.
2. Apply lem-pur-sheaf-ring-coefficient-ordinary-adjunction on each slice. The inverse
   of g mapping to g(1 tensor x) sends s tensor x to s h(x): this is balanced,
   additive and S-linear, commutes with restrictions, and extends uniquely through
   module sheafification. Both composites are identities on generators and hence
   on sheaves, by the tensor and sheafification universal properties.
3. Evaluation on generators shows additivity, R-linearity and compatibility with
   precomposition, postcomposition and further slice restriction. The inverse has
   the same compatibilities by uniqueness. This uses def-pur-sheaf-hom and the
   sectionwise description of def-pur-localized-ringed-site.
4. T(A) and UEA have the same abelian sheafification of the tensor presheaf.
   Uniqueness of the extended R-action gives nu, identity on generators. The
   differential sends s tensor x to s tensor dx on both sides, giving a natural
   chain isomorphism, by def-pur-sheaf-tensor-product and module sheafification.
5. Apply the normalized slice bijection in each integer-indexed product coordinate
   of def-pur-hom-complex. The two displayed formulas are inverse R-linear maps
   of sheaves. No extension functor is applied to an infinite product.
6. On a degree-n family and coordinate i, theta(dg)(x) equals
   d_N(g(1 tensor x)) - (-1)^n g(1 tensor d_P(x)), which is d(theta(g))(x).
   Equality on every slice and coordinate proves the chain-map equation. The
   inverse is a chain map by cancellation, with the exact 0A8X sign convention.
7. For a:P' to P and b:N to N', both naturality composites evaluate to
   b(g(1 tensor a(x))). Product projections detect equality. These constructions
   allow arbitrary unbounded complexes, with no flatness or K-injectivity. -/
theorem exists_sliceScalarHomChainAdjunction
    {R S : Sheaf J CommRingCat.{max c v u}} (φ : R ⟶ S) :
    Nonempty (SliceScalarHomAdjunction.{c, v, u} φ) := by
  classical
  let E := canonicalExtension.{c, v, u} φ
  let O := normalizedFor.{c, v, u} E
  let L := fun W : C ↦ normalizedFor.{max c v, v, u}
    (canonicalExtension.{max c v, v, u} ((J.overPullback CommRingCat.{max c v u} W).map φ))
  let o (W : C) :
      E.functor ⋙
        overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) W ≅
      overFunctor.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) W ⋙
        (L W).extension.functor :=
    (scalarRestrictionIso (J₀ := J.over W) (Over.forget W) φ).symm
  let t {V W : C} (a : V ⟶ W) :
      (L W).extension.functor ⋙
          overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) a ≅
        overMap.{max c v u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) a ⋙
          (L V).extension.functor :=
    (scalarRestrictionIso (J₀ := J.over V) (Over.map a)
      ((J.overPullback CommRingCat.{max c v u} W).map φ)).symm
  refine ⟨{ ordinary := O
            slices := L
            overIso := o
            furtherIso := t
            chains := chainsFromData (canonicalData.{c, v, u} φ)
            over_pure := ?_
            further_pure := ?_ }⟩
  · intro W M V s x
    have hh := scalarBackIso_pure (J₀ := J.over W) (Over.forget W) φ M (op V) s x
    have hi := congrArg (fun z ↦ ((scalarBackIso (J₀ := J.over W)
      (Over.forget W) φ M).inv.val.app (op V)) z) hh
    have hc := congrArg (fun z ↦ z.val.app (op V)
      (scalarExtensionSection ((pullRing (J₀ := J.over W) (Over.forget W)).map φ)
        (M.over W) (op V) s x))
      (scalarBackIso (J₀ := J.over W) (Over.forget W) φ M).hom_inv_id
    change (scalarBackIso (J₀ := J.over W) (Over.forget W) φ M).inv.val.app (op V)
      (scalarExtensionSection φ M (op V.left) s x) = _
    exact hi.symm.trans hc
  · intro V W a M Z s x
    have hh := scalarBackIso_pure (J₀ := J.over V) (Over.map a)
      ((J.overPullback CommRingCat.{max c v u} W).map φ) M (op Z) s x
    have hi := congrArg (fun z ↦ ((scalarBackIso (J₀ := J.over V)
      (Over.map a) ((J.overPullback CommRingCat.{max c v u} W).map φ) M).inv.val.app
        (op Z)) z) hh
    have hc := congrArg (fun z ↦ z.val.app (op Z)
      (scalarExtensionSection
        ((pullRing (J₀ := J.over V) (Over.map a)).map
          ((J.overPullback CommRingCat.{max c v u} W).map φ))
        ((overMap _ a).obj M) (op Z) s x))
      (scalarBackIso (J₀ := J.over V) (Over.map a)
        ((J.overPullback CommRingCat.{max c v u} W).map φ) M).hom_inv_id
    exact hi.symm.trans hc

end SheafOfModules.StrictScalarHom
