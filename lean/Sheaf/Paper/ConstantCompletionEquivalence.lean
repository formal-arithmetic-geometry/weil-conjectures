/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Sheaf.Paper.FlatRingedIdealCompleteEquivalence
public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.ConstantModuleSectionProperties
import WeilConjectures.RingTheory.LimitFlatModules
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.RingTheory.NoetherianKoszulAugmentationProZero

import WeilConjectures.AlgebraicGeometry.KoszulComplex
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
/-!
# Constant coefficients and their sheafwise adic completion

Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).

Positive exponents are indexed by `n : ℕ`, meaning `n+1`. All localizations below use
Mathlib's standard derived category. The extra names only specify the canonical objects,
strict towers and representative normalizations in this node; they introduce no replacement
for sheaves, tensor products, derived internal Hom or local completeness.
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

/-- The constant ring sheaf. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev constant : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)

/-- The finite coefficient sheaf at exponent n+1. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev finite (n : ℕ) : Sheaf J CommRingCat.{u} :=
  constant J (A ⧸ I ^ (n + 1))

/-- The quotient map of constant ring sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotient (n : ℕ) : constant J A ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The finite quotient transition. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def transition (n : ℕ) : finite J A I (n + 1) ⟶ finite J A I n :=
  (constantSheaf J CommRingCat.{u}).map
    (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))))

/-- The actual inverse sequence of finite constant ring sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteSystem : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{u} :=
  Functor.ofOpSequence (transition J A I)

/-- The sheafwise completion, as the limit of the specified sequence. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completed : Sheaf J CommRingCat.{u} := limit (finiteSystem J A I)

/-- The canonical finite projection. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def projection (n : ℕ) : completed J A I ⟶ finite J A I n :=
  limit.π (finiteSystem J A I) (op n)

/-- Quotient maps form a cone. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: both composites are the image under constant sheafification of the quotient map
A → A/I^(n+1); use factorPow_comp_mk and functoriality. -/
theorem quotient_step (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (constant J A)).map (homOfLE (Nat.le_succ n)).op ≫
        quotient J A I n =
      quotient J A I (n + 1) ≫ (finiteSystem J A I).map (homOfLE (Nat.le_succ n)).op := by
  simp only [Functor.const_obj_map, finiteSystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  change _ = (constantSheaf J CommRingCat).map _ ≫ (constantSheaf J CommRingCat).map _
  rw [← Functor.map_comp]
  congr 1

/-- The quotient cone, using the actual quotient maps. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotientCone : Cone (finiteSystem J A I) where
  pt := constant J A
  π := NatTrans.ofOpSequence (quotient J A I) (quotient_step J A I)

/-- The canonical map from constant to completed coefficients. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def coefficientMap : constant J A ⟶ completed J A I :=
  limit.lift _ (quotientCone J A I)

variable {J A I}

/-- The existing category of module sheaves, with commutativity forgotten.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Mod (O : Sheaf J CommRingCat.{u}) := ringedSiteModules.{u} (siteModuleRings O)

/-- Cochain complexes of these module sheaves. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Cx (O : Sheaf J CommRingCat.{u}) := CochainComplex (Mod O) ℤ

/-- The standard derived localization, rather than an additional size hypothesis.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev D (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (Mod O) _ _ (HasDerivedCategory.standard _)

/-- The standard localization functor. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev Q (O : Sheaf J CommRingCat.{u}) : Cx O ⥤ D O :=
  @DerivedCategory.Q (Mod O) _ _ (HasDerivedCategory.standard _)

/-- Ordinary restriction of scalars, exactly Mathlib's functor. Source: Stacks 099I
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev res {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : Mod B ⥤ Mod R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Exact derived restriction of scalars. Source: Stacks 099I
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def dres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : D B ⥤ D R :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  siteDerivedRestrictScalars φ

/-- Constant global sections supplied by the sheafification unit. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def constantSection (a : A) : ((constant J A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a,
    fun f ↦ ConcreteCategory.congr_hom
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).naturality f) a |>.symm⟩

/-- Images of constant sections in a coefficient algebra. Source: Stacks 093M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def algebraSection {O : Sheaf J CommRingCat.{u}} (φ : constant J A ⟶ O) (a : A) :
    (O.obj ⋙ forget CommRingCat).sections :=
  ⟨fun U ↦ φ.hom.app U ((constantSection (J := J) a).val U),
    fun f ↦ (ConcreteCategory.congr_hom (φ.hom.naturality f) _).symm.trans
      (congrArg (φ.hom.app _) ((constantSection (J := J) a).property f))⟩

/-- The kernel of a ring-sheaf map is a genuine ideal subsheaf with these sections.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ring-map kernels are ideals; naturality preserves them. A section whose image
vanishes on a covering sieve has zero image by separatedness of the target sheaf.
The sections formula determines the ideal subsheaf uniquely, by proof irrelevance. -/
theorem kernelIdeal_existsUnique {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) :
    ∃! K : RingedSiteIdeal O,
      ∀ U : C, K.sections U = RingHom.ker (q.hom.app (op U)).hom := by
  let K : RingedSiteIdeal O :=
    { sections := fun U ↦ RingHom.ker (q.hom.app (op U)).hom
      restriction := by
        intro U V g a ha
        change q.hom.app (op V) (O.obj.map g.op a) = 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [h, ha, map_zero]
      local_mem := by
        intro U a T hT ha
        change q.hom.app (op U) a = 0
        have hS : Presieve.IsSheaf J (S.obj ⋙ forget CommRingCat) :=
          (isSheaf_iff_isSheaf_of_type J _).mp
            ((sheafCompose J (forget CommRingCat)).obj S).property
        apply (hS.isSeparated T hT).ext
        intro V g hg
        change S.obj.map g.op (q.hom.app (op U) a) = S.obj.map g.op 0
        have h := ConcreteCategory.congr_hom (q.hom.naturality g.op) a
        change q.hom.app (op V) (O.obj.map g.op a) =
          S.obj.map g.op (q.hom.app (op U) a) at h
        rw [← h, map_zero]
        exact ha V g hg }
  refine ⟨K, fun _ ↦ rfl, ?_⟩
  intro L hL
  have h : L.sections = K.sections := funext hL
  have hext (M N : RingedSiteIdeal O) (h : M.sections = N.sections) : M = N := by
    cases M
    cases N
    dsimp only at h
    cases h
    rfl
  exact hext L K h

/-- The specified kernel ideal subsheaf, selected by its unique sections formula.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def kernelIdeal {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) : RingedSiteIdeal O :=
  (kernelIdeal_existsUnique q).exists.choose

/-- The existing local internal-Hom completeness predicate, at the standard localization.
Source: Stacks 0999, 099I (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsComplete {O S : Sheaf J CommRingCat.{u}} (q : O ⟶ S) (M : D O) : Prop :=
  @IsLocallyDerivedRingedIdealComplete C _ J O
    (HasDerivedCategory.standard _)
    (fun _ ↦ HasDerivedCategory.standard _)
    (kernelIdeal q).module (kernelIdeal q).inclusion M

/-- Flatness and every canonical quotient identification for the sheafwise completion.
Source: Stacks 093M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the constant-module section theorem gives flat A/I^n sections and surjective
transitions. The flat inverse-limit theorem makes the limit flat over A on each object;
flat sheafification makes it flat over the constant ring sheaf. The tensor-limit theorem
with the finite module A/I^n identifies the projection quotient with the constant finite
sheaf, sectionwise. Its kernel is generated by the images of I^n and its projection is
surjective. These identifications are the original projections, so respect transitions. -/
theorem flat_and_quotients (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlat
      ((res (coefficientMap J A I)).obj (SheafOfModules.unit
        (siteModuleRings (completed J A I)))) ∧
    (∀ (n : ℕ) (U : C),
      Function.Surjective ((projection J A I n).hom.app (op U)) ∧
      RingHom.ker ((projection J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (algebraSection (coefficientMap J A I) a).val (op U)))) ∧
    (∀ (n : ℕ) (U : C),
      Function.Surjective ((quotient J A I n).hom.app (op U)) ∧
      RingHom.ker ((quotient J A I n).hom.app (op U)).hom =
        Ideal.span (Set.range (fun a : ↥(I ^ (n + 1)) ↦
          (constantSection (J := J) (a : A)).val (op U)))) := by
  sorry

/-- Restriction along the canonical completion map gives the asserted equivalence.
Source: Stacks 099I and the opening of 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: flat_and_quotients gives flatness and the quotient isomorphism modulo I. The
constant ideal is finite type since A is Noetherian. Apply the general flat ringed-ideal
complete equivalence. The kernel ideals in IsComplete are exactly I and I times the
completed ring by the preceding sections formulas. Its ambient functor is dres. -/
theorem equivalence (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : ObjectProperty.FullSubcategory (IsComplete (projection J A I 0)) ≌
        ObjectProperty.FullSubcategory (IsComplete (quotient J A I 0)),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IsComplete (quotient J A I 0)) ≅
        ObjectProperty.ι (IsComplete (projection J A I 0)) ⋙ dres (coefficientMap J A I)) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary scalar-extension map respects identities and composition.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: before sheafification these are the identity and composition laws of the
sectionwise extension-of-scalars functors. Sheafification preserves those equations. -/
theorem change_laws {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (∀ M : Mod R, SheafOfModules.changeOfRingsHom.{u, u, u} φ M (𝟙 M) = 𝟙 _) ∧
    (∀ (M N L : Mod R) (f : M ⟶ N) (g : N ⟶ L),
      SheafOfModules.changeOfRingsHom.{u, u, u} φ M (f ≫ g) =
        SheafOfModules.changeOfRingsHom.{u, u, u} φ M f ≫
          SheafOfModules.changeOfRingsHom.{u, u, u} φ N g) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨E, hobj, hmap, _, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
  have hm {M N : Mod R} (f : M ⟶ N) :
      SheafOfModules.changeOfRingsHom φ M f =
        eqToHom (hobj M).symm ≫ E.map f ≫ eqToHom (hobj N) := by
    rw [hmap]
    simp
  constructor
  · intro M
    rw [hm, E.map_id]
    simp
  · intro M N L f g
    simp only [hm, E.map_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- The additive ordinary scalar extension, with the recorded objects and maps.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def change {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : Mod R ⥤ Mod S where
  obj := SheafOfModules.changeOfRings.{u, u, u} φ
  map := SheafOfModules.changeOfRingsHom.{u, u, u} φ _
  map_id := (change_laws φ).1
  map_comp f g := (change_laws φ).2 _ _ _ f g

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary scalar extension is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: its objects and maps are those of the additive witness in the recorded
independent-coefficient derived change-of-rings theorem; transport its additive law. -/
theorem change_additive {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (change φ).Additive := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨E, hobj, hmap, hAdd, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients φ
  have hE : E = change φ := Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  exact hAdd

attribute [instance] change_additive

set_option genSizeOf false in
set_option genInjectivity false in
/-- The derived scalar-extension universal property and K-flat computation.
This packages an existing notion, with its universal comparison retained.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure DerivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶
    (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsAcyclicTensorKFlat → IsIso (comparison.app P)

/-- The recorded derived change-of-rings theorem supplies this universally specified pair.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: use derivedChangeOfRingsIndependentCoefficients with the standard localizations.
Identify its ordinary tensor witness with change on objects and maps. Compose its
homotopy counit with quotientCompQhIso and mapHomotopyCategoryFactors. The composite
localization universal property gives the complex-level universal property, and its
K-flat computation transports across those factorization isomorphisms. -/
theorem derivedExtension_exists {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Nonempty (DerivedExtension φ) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  obtain ⟨E, hobj, hmap, hpres, T, hpw, ε, huniv, htri, hcomp⟩ :=
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel φ).some
  have hE : E = change φ := Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  exact ⟨{ functor := T
           comparison := ε
           universal := huniv
           computation := fun P hP ↦ hcomp P
             ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) }⟩

/-- Select the universal derived pair, which is determined up to its unique normalized
natural isomorphism; no arbitrary tensor functor is chosen. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedExtension {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : DerivedExtension φ :=
  Classical.choice (derivedExtension_exists φ)

/-- The specified derived extension of scalars. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def extend {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) : D R ⥤ D S :=
  (derivedExtension φ).functor

/-- Its universal computation comparison on complexes. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def extendComparison {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    Q R ⋙ extend φ ⟶ (change φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S :=
  (derivedExtension φ).comparison


/-- The scalar-extension insertion on sections, including the sheafification unit.
The target is the sheafification defining the actual scalar-extension tensor functor.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tensorSection {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) : ((change φ).obj M).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ M)).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)

/-- The finite comparison before localization, uniquely fixed on sheafified pure tensors.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: both tensors are the cokernel of the same finite row of multiplication maps on M,
namely the monomials generating I^(n+1). Thus the formula sends s tensor m to itself
and is invertible, S_n-linear, natural in M and compatible with all quotient transitions.
Pure tensors generate after sheafification, proving uniqueness. -/
theorem finiteComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
        change (projection J A I n),
      ∀ (M : Mod (completed J A I)) (U : Cᵒᵖ)
        (s : (finite J A I n).obj.obj U) (m : M.val.obj U),
        (e.hom.app M).val.app U
          (tensorSection (quotient J A I n) ((res (coefficientMap J A I)).obj M) U s m) =
            tensorSection (projection J A I n) M U s m := by
  sorry

/-- The canonical finite comparison, with its pure-tensor normalization fixed uniquely.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    res (coefficientMap J A I) ⋙ change (quotient J A I n) ≅
      change (projection J A I n) :=
  (finiteComparison_existsUnique J A I n).exists.choose


/-- The standard computation square for exact restriction of scalars.
Source: Stacks 099I (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def resFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q R ≅ Q B ⋙ dres φ :=
  letI := HasDerivedCategory.standard (Mod R)
  letI := HasDerivedCategory.standard (Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (res φ).mapDerivedCategoryFactors.symm

/-- Finite scalar comparison in D(S_n), normalized on every flat-term K-flat complex.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: a flat-term K-flat B-complex remains K-flat over R because B is R-flat.
Use finiteComparison on that representative. Its pure-tensor formula is natural and
independent of replacements by the universal derived-change-of-rings counits, giving
this natural isomorphism and the displayed computation square. -/
theorem finiteDerivedComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    ∃ e : dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ≅
        extend (projection J A I n),
      ∀ (P : Cx (completed J A I)), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (extend (quotient J A I n)).map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (extendComparison (quotient J A I n)).app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (finite J A I n)).map
            ((NatIso.mapHomologicalComplex (finiteComparison J A I n)
              (ComplexShape.up ℤ)).hom.app P) =
        (e.hom.app ((Q (completed J A I)).obj P)) ≫
          (extendComparison (projection J A I n)).app P := by
  sorry

variable (J A I)

/-- The two coefficient sheaves, false for constant and true for completed coefficients.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev coefficients (b : Bool) : Sheaf J CommRingCat.{u} :=
  if b then completed J A I else constant J A

/-- Their structural constant coefficient maps. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def baseMap (b : Bool) : constant J A ⟶ coefficients J A I b :=
  match b with
  | false => 𝟙 _
  | true => coefficientMap J A I

/-- Their finite projections, the original quotient maps. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finiteMap (b : Bool) (n : ℕ) : coefficients J A I b ⟶ finite J A I n :=
  match b with
  | false => quotient J A I n
  | true => projection J A I n

/-- Finite reduction with the original coefficient action retained. Source: Stacks 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reduction (b : Bool) (n : ℕ) :
    Mod (coefficients J A I b) ⥤ Mod (coefficients J A I b) :=
  change (finiteMap J A I b n) ⋙ res (finiteMap J A I b n)

/-- The quotient transition is fixed uniquely by its sectionwise tensor formula.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite quotient transition preserves the balanced tensor relations because
it commutes with the coefficient projections. Sheafify its map s tensor m ↦ bar(s) tensor m.
The formula is linear, commutes with restrictions and module maps, and determines it uniquely. -/
theorem reductionStep_existsUnique (b : Bool) (n : ℕ) :
    ∃! t : reduction J A I b (n + 1) ⟶ reduction J A I b n,
      ∀ (M : Mod (coefficients J A I b)) (U : Cᵒᵖ)
        (s : (finite J A I (n + 1)).obj.obj U) (m : M.val.obj U),
        (t.app M).val.app U (tensorSection (finiteMap J A I b (n + 1)) M U s m) =
          tensorSection (finiteMap J A I b n) M U
            ((transition J A I n).hom.app U s) m := by
  sorry

/-- The actual finite quotient transition with its uniquely specified tensor formula.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionStep (b : Bool) (n : ℕ) :
    reduction J A I b (n + 1) ⟶ reduction J A I b n :=
  (reductionStep_existsUnique J A I b n).exists.choose

/-- The strict reduction tower, retaining all its transitions functorially.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTower (b : Bool) : Mod (coefficients J A I b) ⥤
    (ℕᵒᵖ ⥤ Mod (coefficients J A I b)) :=
  (Functor.ofOpSequence (reductionStep J A I b)).flip

/-- The tower is additive, since every evaluation is additive scalar extension/restriction.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate the additive-functor identity at each tower index. The chosen tensor functor
and restriction of scalars are additive. Evaluation is jointly faithful. -/
theorem reductionTower_additive (b : Bool) : (reductionTower J A I b).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (reduction J A I b n.unop).map (f + g) = _
  have : (reduction J A I b n.unop).Additive := by
    dsimp only [reduction, res]
    infer_instance
  exact Functor.map_add (reduction J A I b n.unop)

attribute [instance] reductionTower_additive

/-- The constant module tower functor. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev constantTower (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ (ℕᵒᵖ ⥤ Mod O) :=
  Functor.const ℕᵒᵖ

/-- The strict quotient unit is uniquely determined by m ↦ 1 tensor m at every level.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the scalar-extension units commute with quotient transitions since they preserve 1.
They are linear in the original coefficients and natural in M, so form a natural
transformation of strict towers. The section formula determines every component. -/
theorem reductionUnit_existsUnique (b : Bool) :
    ∃! η : constantTower J (coefficients J A I b) ⟶ reductionTower J A I b,
      ∀ (M : Mod (coefficients J A I b)) (n : ℕ) (U : Cᵒᵖ) (m : M.val.obj U),
        ((η.app M).app (op n)).val.app U m =
          tensorSection (finiteMap J A I b n) M U 1 m := by
  sorry

/-- The actual strict quotient-tower unit. Source: Stacks 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionUnit (b : Bool) :
    constantTower J (coefficients J A I b) ⟶ reductionTower J A I b :=
  (reductionUnit_existsUnique J A I b).exists.choose

variable {J A I}


/-- The standard derived category of strict module towers. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev TD (O : Sheaf J CommRingCat.{u}) :=
  @DerivedCategory (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- Localization of strict tower complexes. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev TQ (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ TD O :=
  @DerivedCategory.Q (ℕᵒᵖ ⥤ Mod O) _ _ (HasDerivedCategory.standard _)

/-- The ordinary termwise limit of strict tower complexes. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev ordinaryLimit (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ Cx O :=
  (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).mapHomologicalComplex (ComplexShape.up ℤ)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The total right derived strict-limit universal property and K-injective computation.
Source: Stacks 0940, 0941 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure StrictLimit (O : Sheaf J CommRingCat.{u}) where
  functor : TD O ⥤ D O
  comparison : ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ functor
  universal : functor.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Mod O) (ComplexShape.up ℤ))
  computation : ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ,
    P.IsKInjective → IsIso (comparison.app P)

/-- The strict-tower theorem supplies this existing total derived functor and comparison.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: specialize ringedStrictTowerHomotopyLimit to O with commutativity retained and to
the standard localizations. Project its universal right-derived pair and its computation
on K-injective tower complexes. These are precisely the fields displayed here. -/
theorem strictLimit_exists (O : Sheaf J CommRingCat.{u}) : Nonempty (StrictLimit O) := by
  let := HasDerivedCategory.standard (Mod O)
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod O)
  obtain ⟨RF, η, huniv, hcomp, _⟩ :=
    ringedStrictTowerHomotopyLimit J (siteModuleRings O) (fun U a b ↦ @mul_comm (O.obj.obj U) _ a b)
  exact ⟨{ functor := RF
           comparison := η
           universal := huniv
           computation := hcomp }⟩

/-- Select the total derived strict limit by its universal comparison.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def strictLimit (O : Sheaf J CommRingCat.{u}) : StrictLimit O :=
  Classical.choice (strictLimit_exists O)

/-- Total right derived strict inverse limit, not a noncanonical triangulated cone.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def rlim (O : Sheaf J CommRingCat.{u}) : TD O ⥤ D O := (strictLimit O).functor

/-- Its universal comparison from ordinary termwise inverse limit.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitComparison (O : Sheaf J CommRingCat.{u}) :
    ordinaryLimit O ⋙ Q O ⟶ TQ O ⋙ rlim O := (strictLimit O).comparison

variable (J A I)

/-- The ordinary strict reduction-tower complex, on one fixed representative.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev reductionComplex (b : Bool) (P : Cx (coefficients J A I b)) :=
  ((reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary limit unit is the unique chain map with the prescribed quotient components.
Source: Stacks 099M, 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at degree q use limit.lift on the strict quotient-unit cone. The differential
commutes with every projection by naturality of reductionUnit, hence with their limit.
Joint monicity of the projections proves uniqueness in every degree. -/
theorem ordinaryUnit_existsUnique (b : Bool) (P : Cx (coefficients J A I b)) :
    ∃! f : P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P),
      ∀ (q : ℤ) (n : ℕ), f.f q ≫
        limit.π ((reductionComplex J A I b P).X q) (op n) =
          ((reductionUnit J A I b).app (P.X q)).app (op n) := by
  let f : P ⟶
      (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P) :=
    { f := fun q ↦ limit.lift _
        { pt := P.X q
          π := (reductionUnit J A I b).app (P.X q) }
      comm' := by
        intro q q' h
        apply limit.hom_ext
        intro n
        rw [Category.assoc, Category.assoc]
        change limit.lift _ _ ≫ limMap ((reductionComplex J A I b P).d q q') ≫
          limit.π _ n = _
        rw [limMap_π, limit.lift_π_assoc]
        calc
          _ = P.d q q' ≫ ((reductionUnit J A I b).app (P.X q')).app n :=
            (congrArg (fun t ↦ t.app n)
              ((reductionUnit J A I b).naturality (P.d q q'))).symm
          _ = _ := congrArg (fun t ↦ P.d q q' ≫ t)
            (limit.lift_π (F := (reductionTower J A I b).obj (P.X q'))
              { pt := P.X q', π := (reductionUnit J A I b).app (P.X q') } n).symm }
  refine ⟨f, ?_, ?_⟩
  · intro q n
    exact limit.lift_π _ _
  · intro g hg
    apply HomologicalComplex.hom_ext
    intro q
    apply limit.hom_ext
    intro n
    change g.f q ≫ limit.π ((reductionTower J A I b).obj (P.X q)) n =
      limit.lift _ { pt := P.X q, π := (reductionUnit J A I b).app (P.X q) } ≫
        limit.π ((reductionTower J A I b).obj (P.X q)) n
    rw [limit.lift_π]
    exact hg q n.unop

/-- The actual ordinary strict-limit unit, fixed by its quotient projections.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryUnit (b : Bool) (P : Cx (coefficients J A I b)) :
    P ⟶ (ordinaryLimit (coefficients J A I b)).obj (reductionComplex J A I b P) :=
  (ordinaryUnit_existsUnique J A I b P).exists.choose

/-- The universal derived-tower laws and the actual quotient-unit computation.
Naming this predicate keeps the dependent record small; its normalization is unchanged.
Source: Stacks 099M, 06YY, 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def QuotientPresentationLaws (b : Bool)
    (tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b))
    (comparison : Q (coefficients J A I b) ⋙ tower ⟶
      (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        TQ (coefficients J A I b))
    (unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)) : Prop :=
  tower.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (Mod (coefficients J A I b)) (ComplexShape.up ℤ)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsAcyclicTensorKFlat →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)) ∧
    (∀ P : Cx (coefficients J A I b), P.IsAcyclicTensorKFlat →
      (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        unit.app ((Q (coefficients J A I b)).obj P) ≫
          (rlim (coefficients J A I b)).map (comparison.app P) =
        (Q (coefficients J A I b)).map (ordinaryUnit J A I b P) ≫
          (limitComparison (coefficients J A I b)).app (reductionComplex J A I b P))

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universal derived strict reduction tower with its prescribed completion unit.
The laws specify the actual quotient maps and total right derived strict inverse limit.
Source: Stacks 099M, 06YY, 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure QuotientPresentation (b : Bool) where
  tower : D (coefficients J A I b) ⥤ TD (coefficients J A I b)
  comparison : Q (coefficients J A I b) ⋙ tower ⟶
    (reductionTower J A I b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      TQ (coefficients J A I b)
  unit : 𝟭 (D (coefficients J A I b)) ⟶ tower ⋙ rlim (coefficients J A I b)
  laws : QuotientPresentationLaws J A I b tower comparison unit

/-- Strict diagram K-flat replacements and the universal derived limit supply this pair.
Source: Stacks 06YY, 0940, 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: use a single flat-term K-flat representative for the entire reduction tower.
Each scalar extension preserves quasi-isomorphisms between such representatives, so the
resolving-class localization theorem gives the displayed universal tower and computation.
Apply total right derived limit to its strict quotient units. Their naturality and
invariance under quasi-isomorphisms descend the unit to D(O). The comparison square is
its construction, and determines it because every object has such a representative. -/
theorem quotientPresentation_exists (b : Bool) : Nonempty (QuotientPresentation J A I b) := by
  sorry

/-- Choose the universally specified reduction tower and normalized unit.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def quotientPresentation (b : Bool) : QuotientPresentation J A I b :=
  Classical.choice (quotientPresentation_exists J A I b)

/-- Quotient-tower derived completion, using total right derived inverse limit.
Source: Stacks 099M (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completion (b : Bool) : D (coefficients J A I b) ⥤ D (coefficients J A I b) :=
  (quotientPresentation J A I b).tower ⋙ rlim (coefficients J A I b)

/-- Its prescribed quotient-tower completion unit. Source: Stacks 099M
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completionUnit (b : Bool) : 𝟭 (D (coefficients J A I b)) ⟶ completion J A I b :=
  (quotientPresentation J A I b).unit

/-- The existing strict Koszul presentation, for the images of the given generators.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev KoszulPresentation (b : Bool) (r : ℕ) (a : Fin r → A) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  RingedKoszulLimitPresentation (coefficients J A I b) r
    (fun i ↦ algebraSection (baseMap J A I b) (a i))

/-- Completion from the actual dual Koszul tensor tower with transitions (a_i,1).
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def koszulCompletion {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) : D (coefficients J A I b) ⥤
      D (coefficients J A I b) :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.completion

/-- The specified degree-zero Koszul unit in the standard localization.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def koszulUnit {b : Bool} {r : ℕ} {a : Fin r → A}
    (K : KoszulPresentation J A I b r a) (M : D (coefficients J A I b)) :
    M ⟶ (koszulCompletion J A I K).obj M :=
  letI := HasDerivedCategory.standard (Mod (coefficients J A I b))
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod (coefficients J A I b))
  K.unit M

/-- Koszul and finite-quotient completion are canonically identified, preserving the units;
their common functor is the reflector for the local internal-Hom completeness condition.
Source: Stacks 099L, 099M, 0A0E
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the ringed Koszul reflector to the global generators, including the empty
list. For constant coefficients the Noetherian Koszul augmentation has pro-zero cone.
Exact constant sheafification and tensor by a fixed K-flat model preserve this property.
The strict-tower derived-limit theorem inverts the augmentation and identifies its unit
with the quotient unit. For completed coefficients, restrict to constant coefficients:
the finite reductions, strict Koszul tensors and units agree, and restriction identifies
total derived limits by the flat exact adjunction on strict towers. Conservativity
of exact restriction detects the augmentation isomorphism over the completion as well.
Transport the reflector property and the unit-isomorphism criterion across this
unit-preserving natural isomorphism. -/
theorem koszul_quotient_reflector [IsNoetherianRing A] (b : Bool) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ K : KoszulPresentation J A I b r a,
      (∃ e : koszulCompletion J A I K ≅ completion J A I b,
        ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
          (completionUnit J A I b).app M) ∧
      (∀ M : D (coefficients J A I b),
        IsComplete (finiteMap J A I b 0) ((completion J A I b).obj M)) ∧
      (∀ (M L : D (coefficients J A I b)), IsComplete (finiteMap J A I b 0) L →
        Function.Bijective (fun f : (completion J A I b).obj M ⟶ L ↦
          (completionUnit J A I b).app M ≫ f)) ∧
      (∀ M : D (coefficients J A I b),
        IsIso ((completionUnit J A I b).app M) ↔ IsComplete (finiteMap J A I b 0) M) := by
  sorry

/-- Restriction identifies both completions and their specified units.
Source: Stacks 099L, 099M (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at the representative level finite reduction comparisons and dual Koszul tensor
comparisons preserve their strict transitions and degree-zero units. Restriction carries
K-injective strict tower resolutions to K-injective resolutions, since it is right
adjoint to flat exact extension of scalars. Apply limits and the universal comparisons.
This gives the natural isomorphism and the stated equality of the actual units. -/
theorem completion_restriction [IsNoetherianRing A] :
    ∃ e : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I),
      ∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          e.hom.app M =
        (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves the Koszul-to-quotient comparison itself and both units.
Source: Stacks 099M, 0A0E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite Koszul complexes are finite sums of the chosen representative with
identical differentials and transitions after restriction. Their augmentations to the
finite quotients are identical as well. Apply the strict derived-limit restriction
comparison to this square of towers. The resulting square is the displayed equation.
Every augmentation preserves the degree-zero element 1, giving both unit equations.
Alternatively the reflector universal property determines this same square uniquely. -/
theorem koszul_quotient_restriction [IsNoetherianRing A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I) :
    ∃ (KR : KoszulPresentation J A I false r a) (KB : KoszulPresentation J A I true r a)
      (θR : koszulCompletion J A I KR ≅ completion J A I false)
      (θB : koszulCompletion J A I KB ≅ completion J A I true)
      (κ : dres (coefficientMap J A I) ⋙ koszulCompletion J A I KR ≅
        koszulCompletion J A I KB ⋙ dres (coefficientMap J A I))
      (χ : dres (coefficientMap J A I) ⋙ completion J A I false ≅
        completion J A I true ⋙ dres (coefficientMap J A I)),
      (∀ N : D (constant J A), koszulUnit J A I KR N ≫ θR.hom.app N =
        (completionUnit J A I false).app N) ∧
      (∀ M : D (completed J A I), koszulUnit J A I KB M ≫ θB.hom.app M =
        (completionUnit J A I true).app M) ∧
      (∀ M : D (completed J A I),
        koszulUnit J A I KR ((dres (coefficientMap J A I)).obj M) ≫ κ.hom.app M =
          (dres (coefficientMap J A I)).map (koszulUnit J A I KB M)) ∧
      (∀ M : D (completed J A I),
        (completionUnit J A I false).app ((dres (coefficientMap J A I)).obj M) ≫
          χ.hom.app M =
          (dres (coefficientMap J A I)).map ((completionUnit J A I true).app M)) ∧
      (∀ M : D (completed J A I),
        θR.hom.app ((dres (coefficientMap J A I)).obj M) ≫ χ.hom.app M =
          κ.hom.app M ≫ (dres (coefficientMap J A I)).map (θB.hom.app M)) := by
  obtain ⟨KR, ⟨θR, hR⟩, _⟩ := koszul_quotient_reflector J A I false r a ha
  obtain ⟨KB, ⟨θB, hB⟩, _⟩ := koszul_quotient_reflector J A I true r a ha
  obtain ⟨χ, hχ⟩ := completion_restriction J A I
  let F := dres (coefficientMap J A I)
  let κ : F ⋙ koszulCompletion J A I KR ≅ koszulCompletion J A I KB ⋙ F :=
    Functor.isoWhiskerLeft F θR ≪≫ χ ≪≫ Functor.isoWhiskerRight θB.symm F
  refine ⟨KR, KB, θR, θB, κ, χ, hR, hB, ?_, hχ, ?_⟩
  · intro M
    change koszulUnit J A I KR (F.obj M) ≫
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) = _
    rw [← Category.assoc, hR, ← Category.assoc, hχ, ← hB M, F.map_comp]
    simp only [Category.assoc, ← F.map_comp, θB.hom_inv_id_app, Category.comp_id]
    rfl
  · intro M
    change θR.hom.app (F.obj M) ≫ χ.hom.app M =
      (θR.hom.app (F.obj M) ≫ χ.hom.app M ≫ F.map (θB.inv.app M)) ≫
        F.map (θB.hom.app M)
    simp only [Category.assoc, ← F.map_comp, θB.inv_hom_id_app, F.map_id]
    exact congrArg (fun t ↦ θR.hom.app (F.obj M) ≫ t)
      (Category.comp_id (χ.hom.app M)).symm

variable {J A I}

/-- Levelwise restriction on strict module towers. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (ℕᵒᵖ ⥤ Mod B) ⥤ (ℕᵒᵖ ⥤ Mod R) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)

/-- Levelwise restriction is additive and exact, since evaluation computes these laws.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Restriction is additive and exact on module sheaves
by siteRestrictScalars_exact, and finite limits and colimits of functors are pointwise. -/
theorem tres_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive ∧ PreservesFiniteLimits (tres φ) ∧
      PreservesFiniteColimits (tres φ) := by
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  change ((Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)).Additive ∧ _
  dsimp only [tres, res]
  refine ⟨inferInstance, ⟨fun K _ _ ↦ ?_⟩, ⟨fun K _ _ ↦ ?_⟩⟩ <;> infer_instance

/-- The additive structure of the specified levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_additive {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive := (tres_exact φ).1

/-- Finite limits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteLimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits (tres φ) := (tres_exact φ).2.1

/-- Finite colimits for levelwise restriction.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
instance tres_finiteColimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (tres φ) := (tres_exact φ).2.2

/-- Exact levelwise restriction induces restriction on the derived strict tower categories.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tdres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : TD B ⥤ TD R :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategory

/-- The exact levelwise restriction comparison on strict tower complexes.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def tresFactors {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ TQ R ≅ TQ B ⋙ tdres φ :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategoryFactors.symm

/-- The finite comparisons form a strict tower isomorphism, with all quotient transitions.
The normalization identifies each component with the S_n-linear comparison above.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: on s tensor m, transition then comparison and comparison then transition both give
bar(s) tensor m. Sheafification extends equality; naturality in M gives the functor
isomorphism of strict towers. The component formulas determine it uniquely. -/
theorem reductionTowerComparison_existsUnique (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! e : res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
        reductionTower J A I true ⋙ tres (coefficientMap J A I),
      ∀ (M : Mod (completed J A I)) (n : ℕ) (U : Cᵒᵖ)
        (x : ((change (quotient J A I n)).obj ((res (coefficientMap J A I)).obj M)).val.obj U),
        ((e.hom.app M).app (op n)).val.app U x =
          ((finiteComparison J A I n).hom.app M).val.app U x := by
  sorry

/-- The strict tower comparison with the prescribed S_n-linear finite components.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparison (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ reductionTower J A I false ≅
      reductionTower J A I true ⋙ tres (coefficientMap J A I) :=
  (reductionTowerComparison_existsUnique J A I).exists.choose

/-- Restricting before forming the strict quotient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: at every tower index the functor is scalar restriction followed by scalar
extension and restriction. All three maps preserve sums of module homomorphisms.
Equality after every evaluation is equality in the strict functor category. -/
theorem restrictionReduction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).Additive := by
  have : (res (coefficientMap J A I)).Additive := inferInstance
  constructor
  intro M N f g
  change (reductionTower J A I false).map
    ((res (coefficientMap J A I)).map (f + g)) = _
  rw [Functor.map_add]
  exact Functor.map_add (reductionTower J A I false)

attribute [instance] restrictionReduction_additive

/-- Reducing and then restricting a completed-coefficient tower is additive.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: evaluate at every tower index. Scalar extension and both restrictions preserve
addition of module maps, so their composite does as well. -/
theorem reductionRestriction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).Additive := by
  infer_instance

attribute [instance] reductionRestriction_additive

/-- The completed strict reduction followed by restriction preserves zero maps.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply the additive identity of reductionRestriction_additive to the zero map. -/
theorem reductionRestriction_preservesZero (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).PreservesZeroMorphisms := by
  infer_instance

attribute [instance] reductionRestriction_preservesZero

/-- Apply the prescribed strict tower comparison termwise to complexes.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def reductionTowerComparisonComplex (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (reductionTower J A I true ⋙ tres (coefficientMap J A I)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  letI := reductionRestriction_preservesZero J A I
  NatIso.mapHomologicalComplex (reductionTowerComparison J A I) (ComplexShape.up ℤ)

/-- The strict comparison descends through the universal derived-tower construction.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: restrict one flat-term K-flat B-representative, which remains K-flat by flatness
of the coefficient extension. Apply the strict tower comparison and both universal
computation counits. Their invariance under quasi-isomorphisms gives the derived natural
isomorphism, and the formula is exactly its normalized representative computation. -/
theorem derivedReductionTowerComparison (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : dres (coefficientMap J A I) ⋙ (quotientPresentation J A I false).tower ≅
        (quotientPresentation J A I true).tower ⋙ tdres (coefficientMap J A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (quotientPresentation J A I false).tower.map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (quotientPresentation J A I false).comparison.app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (TQ (constant J A)).map
            ((reductionTowerComparisonComplex J A I).hom.app P) ≫
          (tresFactors (coefficientMap J A I)).hom.app (reductionComplex J A I true P) =
        e.hom.app ((Q (completed J A I)).obj P) ≫
          (tdres (coefficientMap J A I)).map
            ((quotientPresentation J A I true).comparison.app P) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary inverse limits commute with scalar restriction by their coordinate maps.
Source: Stacks 0940 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: module restriction preserves limits, computed on underlying additive sheaves.
The limit comparison is invertible degreewise and commutes with differentials. Its
coordinate equations determine it uniquely, so this is a canonical chain isomorphism. -/
theorem limitRestriction_existsUnique {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ∃! e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R,
      ∀ (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ),
        (e.hom.app P).f q ≫
          limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
        (res φ).map (limit.π (P.X q) (op n)) := by
  have : PreservesLimitsOfSize.{u, u} (res φ) := siteRestrictScalars_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} (res φ) := preservesLimitsOfSize_shrink (res φ)
  let e : ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
    NatIso.mapHomologicalComplex (preservesLimitNatIso (res φ)) (ComplexShape.up ℤ)
  have he (P : CochainComplex (ℕᵒᵖ ⥤ Mod B) ℤ) (q : ℤ) (n : ℕ) :
      (e.hom.app P).f q ≫
        limit.π (((tres φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P |>.X q) (op n) =
      (res φ).map (limit.π (P.X q) (op n)) :=
    preservesLimitIso_hom_π (res φ) (P.X q) (op n)
  refine ⟨e, he, ?_⟩
  intro g hg
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro q
  apply limit.hom_ext
  intro n
  exact (hg P q n.unop).trans (he P q n.unop).symm

/-- The ordinary limit comparison fixed by its actual projections. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def limitRestriction {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    ordinaryLimit B ⋙ (res φ).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tres φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ordinaryLimit R :=
  (limitRestriction_existsUnique φ).exists.choose

/-- Restriction identifies total right derived limits of strict towers, canonically.
The comparison is normalized by the ordinary limit coordinate comparison and both
right-derived universal transformations. Source: Stacks 0940 and 0A07
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: extension of scalars is exact by flat_and_quotients, and restriction is its exact
right adjoint. This adjunction holds levelwise on strict towers, so the right-adjoint
K-injective theorem sends a K-injective tower resolution to one over the constant ring.
Ordinary limits agree by their coordinates. Apply the universal right-derived
comparisons to obtain the natural isomorphism and its displayed normalization. -/
theorem derivedLimitRestriction (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ e : rlim (completed J A I) ⋙ dres (coefficientMap J A I) ≅
        tdres (coefficientMap J A I) ⋙ rlim (constant J A),
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (completed J A I)) ℤ,
        (dres (coefficientMap J A I)).map ((limitComparison (completed J A I)).app P) ≫
          e.hom.app ((TQ (completed J A I)).obj P) =
        (resFactors (coefficientMap J A I)).inv.app
            ((ordinaryLimit (completed J A I)).obj P) ≫
          (Q (constant J A)).map ((limitRestriction (coefficientMap J A I)).hom.app P) ≫
          (limitComparison (constant J A)).app
            (((tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim (constant J A)).map ((tresFactors (coefficientMap J A I)).hom.app P) := by
  sorry

/-- Forget a module sheaf to its underlying sheaf of sets.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev underlying (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ Sheaf J (Type u) :=
  SheafOfModules.toSheaf (siteModuleRings O) ⋙ sheafCompose J (forget AddCommGrpCat)

/-- The scalar-extension insertion is the unique underlying-sheaf map m ↦ 1 tensor m.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the section formula commutes with restrictions by the pure-tensor formula for
changeOfRingsMap and naturality of the sheafification unit. Components determine the map. -/
theorem insertion_existsUnique {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    ∃! q : (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M),
      ∀ (U : Cᵒᵖ) (m : M.val.obj U), q.hom.app U m = tensorSection φ M U 1 m := by
  sorry

/-- The actual scalar-extension insertion, including sheafification.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def insertion {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M) :=
  (insertion_existsUnique φ M).exists.choose

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

set_option genSizeOf false in
set_option genInjectivity false in
/-- Algebraic lifts of a topos inverse image, coherently in all coefficient rings.
The existing AlgebraicInverseImage specifies every ring operation and module action on
all generalized sections. Naturality specifies its action on ring maps. The constant
comparison is natural in every commutative ring, fixing the canonical constant-object
identification, including its coefficient maps.
Source: Stacks 00YV, 03D2, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure InverseImageData (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)) where
  rings : Sheaf J CommRingCat.{u} ⥤ Sheaf J' CommRingCat.{u}
  algebra : ∀ O : Sheaf J CommRingCat.{u},
    SheafOfModules.AlgebraicInverseImage L O (rings.obj O)
  ring_naturality : ∀ {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S),
    L.map ((sheafCompose J (forget CommRingCat)).map φ) ≫ (algebra S).ringUnderlying.hom =
      (algebra R).ringUnderlying.hom ≫
        (sheafCompose J' (forget CommRingCat)).map (rings.map φ)
  constants : constantSheaf J CommRingCat.{u} ⋙ rings ≅ constantSheaf J' CommRingCat.{u}

/-- Every geometric inverse image has these algebraic lifts and canonical constant maps.
Source: Stacks 00YV, 03D2, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: transport algebraic operations through finite products preserved by L. The
existing generalized-section equations define the transported ring and module actions.
Transport morphisms through the same underlying-sheaf isomorphisms. Since L is a left
adjoint and preserves the terminal object, it preserves coproducts of the terminal object
and hence constant sheaves. This gives the comparison naturally in every coefficient
ring, and its maps are the canonical constant-sheaf maps. -/
theorem inverseImageData_exists (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] : Nonempty (InverseImageData L) := by
  sorry

variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image maps to finite coefficients form the canonical projection cone.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply F.rings to projection naturality and use naturality of F.constants for
A/I^(n+2) → A/I^(n+1). These are exactly the displayed cone equations. -/
theorem pulledProjection_naturality (A : Type u) [CommRing A] (I : Ideal A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map f ≫
        (F.rings.map (projection J A I n.unop) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom) =
      (F.rings.map (projection J A I m.unop) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (m.unop + 1)))).hom) ≫
          (finiteSystem J' A I).map f := by
  have hstep (k : ℕ) :
      ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map
          (homOfLE (Nat.le_succ k)).op ≫
        (F.rings.map (projection J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) =
      (F.rings.map (projection J A I (k + 1)) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
        (finiteSystem J' A I).map (homOfLE (Nat.le_succ k)).op := by
    simp only [Functor.const_obj_map, finiteSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    change F.rings.map (projection J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.rings.map (projection J A I (k + 1)) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
          transition J' A I k
    have hnat := F.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))))
    change F.rings.map (transition J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom ≫
        transition J' A I k at hnat
    have hproj : projection J A I (k + 1) ≫ transition J A I k =
        projection J A I k := by
      simpa only [projection, finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ k)).op
    calc
      _ = F.rings.map (projection J A I (k + 1) ≫ transition J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom := by rw [hproj]
      _ = _ := by rw [F.rings.map_comp, Category.assoc, hnat, Category.assoc]
  exact (NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I)))
    (G := finiteSystem J' A I)
    (fun k ↦ F.rings.map (projection J A I k) ≫
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) hstep).naturality f

/-- The canonical map from the inverse image of the completed coefficient sheaf to the
completion on the second site, formed from its finite projections.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def completedMap (A : Type u) [CommRing A] (I : Ideal A) :
    F.rings.obj (completed J A I) ⟶ completed J' A I :=
  limit.lift (finiteSystem J' A I)
    { pt := F.rings.obj (completed J A I)
      π :=
        { app := fun n ↦ F.rings.map (projection J A I n.unop) ≫
            (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom
          naturality := fun {m n} f ↦ pulledProjection_naturality F A I (m := m) (n := n) f } }

/-- Module inverse image followed by the existing sheafified scalar extension.
Source: Stacks 03D2, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Mod R ⥤ Mod S :=
  (F.algebra R).modules ⋙ change c

/-- This prescribed module pullback is additive.
Source: Stacks 03D2 (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the algebraic inverse-image lift preserves addition by its generalized-section
moduleAdd identity. The scalar-extension functor is additive, hence so is their composite. -/
theorem pull_additive {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : (pull F c).Additive := by
  sorry

attribute [instance] pull_additive

/-- Insertion after inverse image: u^(-1)M → u^(-1)M tensor S, with coefficient action
fixed by c. Source: Stacks 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullInsertion {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (M : Mod R) :
    L.obj ((underlying R).obj M) ⟶ (underlying S).obj ((pull F c).obj M) :=
  (F.algebra R).moduleUnderlying.inv.app M ≫ insertion c ((F.algebra R).modules.obj M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universally specified derived pullback with computation on flat-term K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
structure DerivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶ (pull F c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)

/-- The recorded K-flat derived-pullback theorem supplies this universal derived pair.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: apply ringedTopoiDerivedPullback to the supplied geometric adjunction and algebraic
lift; pull has exactly its specified scalar-extension objects and maps. Flat-term K-flat
resolutions supply its resolving class. Transport the universal homotopy counit through
the quotient factorization to obtain the complex-level universal pair and computation. -/
theorem derivedPull_exists (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Nonempty (DerivedPull F c) := by
  sorry

variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

/-- Choose the derived pullback with its universal comparison, not an arbitrary lift.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : DerivedPull F c :=
  Classical.choice (derivedPull_exists F V adj c)

/-- The canonical constant-coefficient structural isomorphism.
Source: Stacks 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def constantMap (A : Type u) [CommRing A] : F.rings.obj (constant J A) ⟶ constant J' A :=
  (F.constants.app (CommRingCat.of A)).hom

/-- The unreduced scalar comparison on ordinary modules is fixed by scalar insertion.
This is exactly u^(-1)M → u^(-1)M tensor the completed coefficient ring after inverse image.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the finite projections make the coefficient square commute. After identifying
inverse images of constant coefficients, define q by m ↦ 1 tensor m. It is linear over
the constant coefficient sheaf, and natural in M. Pure tensors generate after
sheafification, so the insertion equation determines q uniquely. -/
theorem ordinaryPullComparison_existsUnique (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! q : res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
        pull F (completedMap F A I) ⋙ res (coefficientMap J' A I),
      ∀ M : Mod (completed J A I),
        pullInsertion F (constantMap F A) ((res (coefficientMap J A I)).obj M) ≫
            (underlying (constant J' A)).map (q.app M) =
          pullInsertion F (completedMap F A I) M := by
  sorry

/-- The prescribed unreduced ordinary scalar comparison. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryPullComparison (A : Type u) [CommRing A] (I : Ideal A) :
    res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⟶
      pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) :=
  (ordinaryPullComparison_existsUnique F A I).exists.choose

/-- The canonical derived scalar comparison, characterized on every flat-term K-flat
representative. Uniqueness makes it independent of resolving choices and gives its
coherence for identity and composite inverse images with the same insertion formula.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: restrict a flat-term K-flat B-model, using flatness of B over the constant ring.
Apply ordinaryPullComparison termwise, then the two universal computation maps. This
is invariant under resolution maps by the resolving-class derived-functor theorem, and
hence descends naturally to every derived object. The square determines it on a resolving
class, hence uniquely. For composite inverse images, both formulas send m to
(1 tensor (1 tensor m)), identified with 1 tensor m by ordinary tensor reassociation;
therefore uniqueness gives composition and identity coherence. -/
theorem derivedPullComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! δ : dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
        (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I),
      ∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (derivedPull F V adj (constantMap F A)).functor.map
            ((resFactors (coefficientMap J A I)).inv.app P) ≫
          (derivedPull F V adj (constantMap F A)).comparison.app
            (((res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (constant J' A)).map
            ((NatTrans.mapHomologicalComplex (ordinaryPullComparison F A I)
              (ComplexShape.up ℤ)).app P) =
        δ.app ((Q (completed J A I)).obj P) ≫
          (dres (coefficientMap J' A I)).map
            ((derivedPull F V adj (completedMap F A I)).comparison.app P) ≫
          (resFactors (coefficientMap J' A I)).inv.app
            (((pull F (completedMap F A I)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        := by
  sorry

/-- The actual derived comparison with the specified K-flat scalar-insertion formula.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def derivedPullComparison (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    dres (coefficientMap J A I) ⋙ (derivedPull F V adj (constantMap F A)).functor ⟶
      (derivedPull F V adj (completedMap F A I)).functor ⋙ dres (coefficientMap J' A I) :=
  (derivedPullComparison_existsUnique F V adj A I).exists.choose

include V adj hL in
/-- Ordinary constant-coefficient pullback commutes with finite reduction, normalized
by the two insertions. This fixes the canonical tensor reassociation in the quotient
coefficient category. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: inverse image preserves balanced generators and relations because it preserves
finite products and colimits. Both sides are the same quotient of u^(-1)M. The maps
send a generalized element m to the same class. These generate the tensor sheaf, giving
uniqueness, naturality in M, and compatibility with quotient ring maps. -/
theorem ordinaryFinitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
        change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))),
      ∀ M : Mod (constant J A),
        pullInsertion F (constantMap F A) M ≫
            insertion (quotient J' A I n) ((pull F (constantMap F A)).obj M) ≫
            (underlying (finite J' A I n)).map (e.hom.app M) =
          L.map (insertion (quotient J A I n) M) ≫
            pullInsertion F (constantMap F (A ⧸ I ^ (n + 1)))
              ((change (quotient J A I n)).obj M) := by
  sorry

/-- The canonical ordinary finite pullback comparison, not an arbitrary isomorphism.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def ordinaryFinitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    pull F (constantMap F A) ⋙ change (quotient J' A I n) ≅
      change (quotient J A I n) ⋙ pull F (constantMap F (A ⧸ I ^ (n + 1))) :=
  (ordinaryFinitePull_existsUnique F V adj A I n).exists.choose

/-- Derived constant pullback and finite reduction commute by the prescribed ordinary
comparison on every flat-term K-flat representative. Source: Stacks 06YY, 099L
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ringed pullback and scalar extension preserve K-flat complexes with flat terms.
Consequently the two iterated derived functors are computed on the same representative.
Use ordinaryFinitePull there and descend through their universal computation counits.
The displayed square determines the resulting natural isomorphism uniquely. -/
theorem finitePull_existsUnique (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
        extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        (extend (quotient J' A I n)).map
            ((derivedPull F V adj (constantMap F A)).comparison.app P) ≫
          (extendComparison (quotient J' A I n)).app
            (((pull F (constantMap F A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Q (finite J' A I n)).map
            ((NatIso.mapHomologicalComplex (ordinaryFinitePull F V adj A I n)
              (ComplexShape.up ℤ)).hom.app P) =
        e.hom.app ((Q (constant J A)).obj P) ≫
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor.map
            ((extendComparison (quotient J A I n)).app P) ≫
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).comparison.app
            (((change (quotient J A I n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        := by
  sorry

/-- The specified derived finite constant pullback comparison.
Source: Stacks 06YY, 099L (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def finitePull (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    (derivedPull F V adj (constantMap F A)).functor ⋙ extend (quotient J' A I n) ≅
      extend (quotient J A I n) ⋙
        (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor :=
  (finitePull_existsUnique F V adj A I n).exists.choose

/-- Completed pullback has the asserted finite comparison in D(A/I^(n+1)) on the second
site. Its inverse is exactly the finite reduction of the unreduced scalar comparison,
after the canonical constant-pullback tensor reassociation. Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: choose one flat-term K-flat completed-coefficient model P. Both sides reduce to
the same quotient u^(-1)P/I^(n+1)u^(-1)P, by finiteComparison and inverse image exactness.
The scalar comparison sends p to 1 tensor p; finite reduction sends its image to the
same quotient class, inverse to the displayed comparison. Every construction commutes
with maps of models and with quotient transitions before localization, and therefore
after descent. The inverse equation fixes the natural isomorphism uniquely. -/
theorem completedFinitePull_existsUnique (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (completedMap F A I)).functor ⋙
          dres (coefficientMap J' A I) ⋙ extend (quotient J' A I n) ≅
        dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ M : D (completed J A I),
        (extend (quotient J' A I n)).map ((derivedPullComparison F V adj A I).app M) =
          (finitePull F V adj A I n).hom.app ((dres (coefficientMap J A I)).obj M) ≫
            e.inv.app M := by
  sorry

/-- Pointwise application of a module pullback to a strict tower.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def pullTowers (A : Type u) [CommRing A] :
    (ℕᵒᵖ ⥤ Mod (constant J A)) ⥤ (ℕᵒᵖ ⥤ Mod (constant J' A)) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod (constant J A)) (Mod (constant J' A))).obj
    (pull F (constantMap F A))

include V adj hL in
/-- All finite pullback comparisons respect quotient transitions and quotient units,
as one isomorphism of strict towers with the specified insertion formula.
This formula also fixes the comparison for every topos morphism, so identity and
composition compatibility follow from its uniqueness and associativity of insertion.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: on inverse-image sections both composites send p to its class in
u^(-1)P/I^(n+1)u^(-1)P. A quotient transition sends that class to the class with the
reduced scalar. The equality holds on all sheafified pure tensors, hence on the module
sheaves, naturally in P. Inserting 1 gives exactly the quotient units. Thus these
are maps of strict towers, not unrelated levelwise isomorphisms. Their components
are the finite pullback comparisons by the same insertion normalization. -/
theorem pullbackTowerComparison_existsUnique (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃! e : pull F (completedMap F A I) ⋙ reductionTower J' A I true ⋙
          tres (coefficientMap J' A I) ≅
        res (coefficientMap J A I) ⋙ reductionTower J A I false ⋙ pullTowers F A,
      ∀ (M : Mod (completed J A I)) (n : ℕ),
        pullInsertion F (completedMap F A I) M ≫
            insertion (projection J' A I n) ((pull F (completedMap F A I)).obj M) ≫
            (underlying (constant J' A)).map ((e.hom.app M).app (op n)) =
          L.map (insertion (quotient J A I n) ((res (coefficientMap J A I)).obj M)) ≫
            pullInsertion F (constantMap F A)
              ((reduction J A I false n).obj ((res (coefficientMap J A I)).obj M)) := by
  sorry

variable {C'' : Type u} [SmallCategory C''] {J'' : GrothendieckTopology C''}
variable {L₂ : Sheaf J' (Type u) ⥤ Sheaf J'' (Type u)}
variable (G : InverseImageData L₂) (H : InverseImageData (L ⋙ L₂))
variable (V₂ : Sheaf J'' (Type u) ⥤ Sheaf J' (Type u)) (adj₂ : L₂ ⊣ V₂)
variable [PreservesFiniteLimits L₂]

/-- Tensor insertion fixes the ordinary pullback composition comparison.
Source: Stacks 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsPullComposition {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d) : Prop :=
  ∀ M : Mod R, pullInsertion H e M ≫ (underlying T).map (a.hom.app M) =
    L₂.map (pullInsertion F c M) ≫ pullInsertion G d ((pull F c).obj M)

/-- The derived composition comparison is the ordinary tensor comparison on K-flat models.
Source: Stacks 06YY, 0G7E (blueprint: lem-weil-pbc-constant-completion-equivalence). -/
def IsDerivedPullComposition {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} {T : Sheaf J'' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (d : G.rings.obj S ⟶ T) (e : H.rings.obj R ⟶ T)
    (a : pull H e ≅ pull F c ⋙ pull G d)
    (α : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).functor ≅
      (derivedPull F V adj c).functor ⋙ (derivedPull G V₂ adj₂ d).functor) : Prop :=
  ∀ P : Cx R, P.IsAcyclicTensorKFlat → (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
    α.hom.app ((Q R).obj P) ≫
        (derivedPull G V₂ adj₂ d).functor.map
          ((derivedPull F V adj c).comparison.app P) ≫
        (derivedPull G V₂ adj₂ d).comparison.app
          (((pull F c).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) e).comparison.app P ≫
        (Q T).map ((NatIso.mapHomologicalComplex a (ComplexShape.up ℤ)).hom.app P)

/-- The unreduced comparison is coherent for composite topos inverse images.
The composition isomorphisms are normalized by actual tensor insertions and their
K-flat computations. Consequently this also gives composition coherence for the finite
comparison, which is uniquely determined by its inverse equation.
Source: Stacks 099L, 06YY (blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: ordinary tensor associativity sends the twice-inserted element to 1 tensor m.
The coefficient maps for the composite agree after every finite projection, hence agree
by the limit universal property. This gives the two normalized ordinary isomorphisms.
All pullbacks preserve the flat-term K-flat resolving class, so these isomorphisms
descend to the displayed derived composition isomorphisms. On that class both sides of
the final equation insert 1 twice. Associativity identifies them, and localization
extends the equality to all derived objects. Uniqueness gives the finite coherence. -/
theorem pullback_composition (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull H (constantMap H A) ≅
        pull F (constantMap F A) ⋙ pull G (constantMap G A))
      (aB : pull H (completedMap H A I) ≅
        pull F (completedMap F A I) ⋙ pull G (completedMap G A I))
      (αR : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (constantMap H A)).functor ≅
        (derivedPull F V adj (constantMap F A)).functor ⋙
          (derivedPull G V₂ adj₂ (constantMap G A)).functor)
      (αB : (derivedPull H (V₂ ⋙ V) (adj.comp adj₂) (completedMap H A I)).functor ≅
        (derivedPull F V adj (completedMap F A I)).functor ⋙
          (derivedPull G V₂ adj₂ (completedMap G A I)).functor),
      IsPullComposition F G H (constantMap F A) (constantMap G A) (constantMap H A) aR ∧
      IsPullComposition F G H (completedMap F A I) (completedMap G A I)
        (completedMap H A I) aB ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (constantMap F A) (constantMap G A) (constantMap H A) aR αR ∧
      IsDerivedPullComposition F V adj G H V₂ adj₂
        (completedMap F A I) (completedMap G A I) (completedMap H A I) aB αB ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison H (V₂ ⋙ V) (adj.comp adj₂) A I).app M ≫
            (dres (coefficientMap J'' A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M) ≫
            (derivedPull G V₂ adj₂ (constantMap G A)).functor.map
              ((derivedPullComparison F V adj A I).app M) ≫
            (derivedPullComparison G V₂ adj₂ A I).app
              ((derivedPull F V adj (completedMap F A I)).functor.obj M)) := by
  sorry

/-- The identity inverse image gives the identity scalar comparison under its normalized
ordinary and derived identity identifications. Source: Stacks 099L, 06YY
(blueprint: lem-weil-pbc-constant-completion-equivalence).
Proof: the ordinary identity comparison multiplies 1 tensor m to m, fixing the stated
insertion equation. Descend termwise through the K-flat universal comparison to obtain
the derived identity isomorphisms. The scalar comparison inserts 1 and each identity
isomorphism removes it, so the final equality holds on the resolving class and hence
throughout the derived category. The inverse equation then gives the finite identity law. -/
theorem pullback_identity (F₀ : InverseImageData (𝟭 (Sheaf J (Type u))))
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (aR : pull F₀ (constantMap F₀ A) ≅ 𝟭 (Mod (constant J A)))
      (aB : pull F₀ (completedMap F₀ A I) ≅ 𝟭 (Mod (completed J A I)))
      (αR : (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).functor ≅
        𝟭 (D (constant J A)))
      (αB : (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).functor ≅
        𝟭 (D (completed J A I))),
      (∀ M : Mod (constant J A), pullInsertion F₀ (constantMap F₀ A) M ≫
        (underlying (constant J A)).map (aR.hom.app M) = 𝟙 _) ∧
      (∀ M : Mod (completed J A I), pullInsertion F₀ (completedMap F₀ A I) M ≫
        (underlying (completed J A I)).map (aB.hom.app M) = 𝟙 _) ∧
      (∀ P : Cx (constant J A), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αR.hom.app ((Q (constant J A)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (constantMap F₀ A)).comparison.app P ≫
            (Q (constant J A)).map
              ((NatIso.mapHomologicalComplex aR (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ P : Cx (completed J A I), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        αB.hom.app ((Q (completed J A I)).obj P) =
          (derivedPull F₀ (𝟭 _) Adjunction.id (completedMap F₀ A I)).comparison.app P ≫
            (Q (completed J A I)).map
              ((NatIso.mapHomologicalComplex aB (ComplexShape.up ℤ)).hom.app P)) ∧
      (∀ M : D (completed J A I),
        (derivedPullComparison F₀ (𝟭 _) Adjunction.id A I).app M ≫
            (dres (coefficientMap J A I)).map (αB.hom.app M) =
          αR.hom.app ((dres (coefficientMap J A I)).obj M)) := by
  sorry

end CategoryTheory.ConstantCompletion
