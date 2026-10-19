/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.KrullTopology
public import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Sheaf.AlgebraicGeometry.FundamentalGroup.AlgebraicFieldLimit
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.CategoryTheory.Galois.AutProfinite
import Sheaf.CategoryTheory.Galois.GaloisTransitive
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Arithmetic lifts and semilinear paths of finite fibre functors

Source: Stacks Project, Tags 0BTX, 0BTV, 0BND and 0BNE (blueprint:
lem-wf-arithmetic-lift-fibre-path).

The statement records the arithmetic exact sequence, its normalized fibre-functor paths,
and the conjugation and change-of-lift formulas.  The proof is postponed: finite constant
covers, finite-field descent, the inverse-limit argument, and the finite locally constant
sheaf comparison are the proof dependencies of the blueprint node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The projection from the algebraic-closure base change to the original scheme.
Source: Stacks Project, Tags 0BTX and 0BTV (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable abbrev arithmeticBaseProjection {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) : fieldExtensionBase X₀ L ⟶ X₀.left :=
  Limits.pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The canonical semilinear self-map of the algebraic-closure base change.
Source: Stacks Project, Tags 0BTX and 0BTV (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticLiftMap {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) (σ : L ≃ₐ[K] L) :
    fieldExtensionBase X₀ L ⟶ fieldExtensionBase X₀ L :=
  fieldExtensionBaseMap X₀ σ

/-- The induced automorphism on the semilinearly moved finite fibre functor.
Source: Stacks Project, Tag 0BND (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticFibreAut {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) (σ : L ≃ₐ[K] L)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (a : Aut (fiber s)) : Aut (fiber (s ≫ arithmeticLiftMap X₀ σ)) :=
  fiberAutBaseChange (arithmeticLiftMap X₀ σ) s a

/-- A finite intermediate field as the existing finite étale constant algebra.
Source: Stacks Tags 0BTX and 0BNE (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticConstantAlgebra {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (E : IntermediateField K L) [FiniteDimensional K E] :
    FiniteEtaleAlgebra K :=
  ⟨CommAlgCat.of K E, inferInstance,
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K E
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }⟩

/-- Forgetting the intermediate field makes a finite model an arithmetic finite étale cover.
Source: Stacks Tag 0BTX, proof of lemma-ses-field
(blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticModelCover {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale) : X₀.left.FiniteEtale :=
  have : Etale (arithmeticBaseProjection (L := E) X₀) :=
    (constantCover X₀.hom (arithmeticConstantAlgebra E)).obj.prop
  have : IsFinite (arithmeticBaseProjection (L := E) X₀) :=
    (constantCover X₀.hom (arithmeticConstantAlgebra E)).property
  have : Etale Q.obj.hom := Q.obj.prop
  have : IsFinite Q.obj.hom := Q.property
  ⟨Etale.mk (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀),
    inferInstanceAs (IsFinite (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀))⟩

/-- The first projection of a finite-model fibre point lies over the arithmetic basepoint.
Source: Stacks Tags 0BTX and 0BTV, finite-model construction in proof step 5
(blueprint: lem-wf-arithmetic-lift-fibre-path).

Proof (postponed): apply the pullback condition to commute the first projection with
Q's structure map. The second projection composed with z is x by `fiber_left_comp`.
The constant-field base-change map preserves the first projection to X₀. Finish with hx.
This is the well-definedness clause of the forgetful injection in the node. -/
theorem arithmeticModelFiber_over {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s x : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (hx : x ≫ arithmeticBaseProjection X₀ = s ≫ arithmeticBaseProjection X₀)
    (z : (fiber x).obj ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)) :
    (z.left ≫ Limits.pullback.fst Q.obj.hom (fieldExtensionBaseMap X₀ E.val)) ≫
      (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀) =
        s ≫ arithmeticBaseProjection X₀ := by
  have hz : z.left ≫ Limits.pullback.snd Q.obj.hom
      (fieldExtensionBaseMap X₀ E.val) = x := fiber_left_comp x z
  calc
    _ = (z.left ≫ Limits.pullback.snd Q.obj.hom
        (fieldExtensionBaseMap X₀ E.val)) ≫
          (fieldExtensionBaseMap X₀ E.val ≫ arithmeticBaseProjection (L := E) X₀) := by
      simp only [Category.assoc, Limits.pullback.condition_assoc]
    _ = x ≫ arithmeticBaseProjection X₀ := by
      rw [hz]
      simp [arithmeticBaseProjection, fieldExtensionBaseMap]
    _ = _ := hx

/-- The forgetful injection on a finite-model fibre: postcompose with the first projection.
The equality `hx` only identifies the two specified arithmetic basepoints.
Source: Stacks Tags 0BTX and 0BTV (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticModelFiber {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s x : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (hx : x ≫ arithmeticBaseProjection X₀ = s ≫ arithmeticBaseProjection X₀)
    (z : (fiber x).obj ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)) :
    (fiber (s ≫ arithmeticBaseProjection X₀)).obj (arithmeticModelCover X₀ E Q) :=
  Over.homMk (z.left ≫ Limits.pullback.fst Q.obj.hom (fieldExtensionBaseMap X₀ E.val))
    (arithmeticModelFiber_over X₀ E Q s x hx z)

private theorem arithmeticModelFiber_injective {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s x : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (hx : x ≫ arithmeticBaseProjection X₀ = s ≫ arithmeticBaseProjection X₀) :
    Function.Injective (arithmeticModelFiber X₀ E Q s x hx) := by
  intro z w h
  apply fiber_ext x
  apply Limits.pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact (fiber_left_comp x z).trans (fiber_left_comp x w).symm

private theorem arithmeticModelFiber_range {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s x : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (hx : x ≫ arithmeticBaseProjection X₀ = s ≫ arithmeticBaseProjection X₀) :
    Set.range (arithmeticModelFiber X₀ E Q s x hx) =
      {z | z.left ≫ Q.obj.hom ≫ Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
        x ≫ fieldExtensionBaseMap X₀ E.val ≫ Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E)))} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change (w.left ≫ Limits.pullback.fst _ _) ≫ _ ≫ _ = _
    rw [Category.assoc, ← Category.assoc (Limits.pullback.fst _ _),
      Limits.pullback.condition]
    have hw := fiber_left_comp x w
    change w.left ≫ Limits.pullback.snd _ _ = x at hw
    simpa only [Category.assoc] using congrArg
      (fun a ↦ a ≫ fieldExtensionBaseMap X₀ E.val ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K E)))) hw
  · intro hz
    have hc : z.left ≫ Q.obj.hom = x ≫ fieldExtensionBaseMap X₀ E.val := by
      apply Limits.pullback.hom_ext
      · have hz₀ := fiber_left_comp (s ≫ arithmeticBaseProjection X₀) z
        change z.left ≫ (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀) =
          s ≫ arithmeticBaseProjection X₀ at hz₀
        simpa [arithmeticBaseProjection, fieldExtensionBaseMap, Category.assoc] using
          hz₀.trans hx.symm
      · exact hz
    refine ⟨fiberMk x ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)
      (Limits.pullback.lift z.left x hc) (Limits.pullback.lift_snd _ _ _), ?_⟩
    apply fiber_ext
    exact Limits.pullback.lift_fst _ _ _

private theorem arithmeticModelFiber_action {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L) (a : Aut (fiber s))
    (z : (fiber s).obj ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)) :
    arithmeticModelFiber X₀ E Q s s rfl (a.hom.app _ z) =
      (fiberAutBaseChange (arithmeticBaseProjection X₀) s a).hom.app _
        (arithmeticModelFiber X₀ E Q s s rfl z) := by
  let A := arithmeticModelCover X₀ E Q
  let f := fieldExtensionBaseMap X₀ E.val
  let p := arithmeticBaseProjection (L := L) X₀
  let φ : (pullback f).obj Q ⟶ (pullback p).obj A :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk
      (Limits.pullback.lift (Limits.pullback.fst Q.obj.hom f)
        (Limits.pullback.snd Q.obj.hom f) (by
          change Limits.pullback.fst Q.obj.hom f ≫
              (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀) =
            Limits.pullback.snd Q.obj.hom f ≫ p
          rw [← Category.assoc, Limits.pullback.condition, Category.assoc]
          congr 1
          simp [f, p, fieldExtensionBaseMap, arithmeticBaseProjection]))
      (Limits.pullback.lift_snd _ _ _))
  have hz : (fiber s).map φ z =
      (pullbackFiberIso p s).inv.app A (arithmeticModelFiber X₀ E Q s s rfl z) := by
    apply fiber_ext s
    change (z.left ≫ Limits.pullback.lift _ _ _) = Limits.pullback.lift _ _ _
    apply Limits.pullback.hom_ext
    · simp [arithmeticModelFiber, f]
    · simp only [Category.assoc, Limits.pullback.lift_snd]
      exact fiber_left_comp s z
  have hn := ConcreteCategory.congr_hom (a.hom.naturality φ) z
  simp only [ConcreteCategory.comp_apply] at hn
  have hproj (w : (fiber s).obj ((pullback f).obj Q)) :
      (pullbackFiberIso p s).hom.app A ((fiber s).map φ w) =
        arithmeticModelFiber X₀ E Q s s rfl w := by
    apply fiber_ext
    change (w.left ≫ Limits.pullback.lift _ _ _) ≫ Limits.pullback.fst _ _ = _
    simp [arithmeticModelFiber, f]
  rw [← hproj (a.hom.app _ z), ← hn, hz]
  rfl

private theorem arithmeticBaseChange_injective {K L : Type u} [Field K]
    [PerfectField K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    (X₀ : Over (Spec (.of K))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L) :
    Function.Injective (fiberAutBaseChange (arithmeticBaseProjection X₀) s) := by
  intro a b hab
  ext P z
  obtain ⟨E, hE, Q, ⟨e⟩⟩ := (finiteEtale_fieldLimit_descent X₀).1 P
  let := hE
  let w := (fiber s).map e.inv z
  have hm : a.hom.app _ w = b.hom.app _ w := by
    apply arithmeticModelFiber_injective X₀ E Q s s rfl
    exact (arithmeticModelFiber_action X₀ E Q s a w).trans
      ((congrArg (fun g ↦ g.hom.app _ (arithmeticModelFiber X₀ E Q s s rfl w)) hab).trans
        (arithmeticModelFiber_action X₀ E Q s b w).symm)
  have ha := ConcreteCategory.congr_hom (a.hom.naturality e.hom) w
  have hb := ConcreteCategory.congr_hom (b.hom.naturality e.hom) w
  simp only [ConcreteCategory.comp_apply] at ha hb
  have hw : (fiber s).map e.hom w = z := by
    exact ConcreteCategory.congr_hom ((fiber s).mapIso e).inv_hom_id z
  rw [hw] at ha hb
  exact ha.trans ((congrArg ((fiber s).map e.hom) hm).trans hb.symm)

/-- The semilinear constant-field map preserves the arithmetic basepoint.
Source: Stacks Tag 0BTX, finite-model construction in proof step 5
(blueprint: lem-wf-arithmetic-lift-fibre-path).

Proof (postponed): the first-projection equation for `fieldExtensionBaseMap X₀ σ`
says that its composite with the projection to X₀ is that projection. Precompose
with s and reassociate. This supplies the basepoint equality for the moved injection. -/
theorem arithmeticLiftMap_basepoint {K L : Type u} [Field K] [Field L] [Algebra K L]
    (X₀ : Over (Spec (.of K))) {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L) (σ : L ≃ₐ[K] L) :
    (s ≫ arithmeticLiftMap X₀ σ) ≫ arithmeticBaseProjection X₀ =
      s ≫ arithmeticBaseProjection X₀ := by
  simp [arithmeticLiftMap, arithmeticBaseProjection, fieldExtensionBaseMap]

/-- The same forgetful injection at the semilinearly moved point.
Source: Stacks Tag 0BTX and the normalization in the node
(blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticMovedModelFiber {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L) (σ : L ≃ₐ[K] L) :
    (fiber (s ≫ arithmeticLiftMap X₀ σ)).obj
        ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q) →
      (fiber (s ≫ arithmeticBaseProjection X₀)).obj (arithmeticModelCover X₀ E Q) :=
  arithmeticModelFiber X₀ E Q s (s ≫ arithmeticLiftMap X₀ σ)
    (arithmeticLiftMap_basepoint X₀ s σ)

private theorem arithmeticModelFiber_ranges {K L : Type u} [Field K] [PerfectField K]
    [Field L] [Algebra K L] (X₀ : Over (Spec (.of K)))
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] [Algebra K Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L) (i : L →ₐ[K] Ω)
    (hi : s ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom i.toRingHom)) (σ : L ≃ₐ[K] L) :
    Function.Injective (arithmeticModelFiber X₀ E Q s s rfl) ∧
    Function.Injective (arithmeticMovedModelFiber X₀ E Q s σ) ∧
    Set.range (arithmeticModelFiber X₀ E Q s s rfl) =
      {z | z.left ≫ Q.obj.hom ≫ Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
        Spec.map (CommRingCat.ofHom (i.toRingHom.comp E.val.toRingHom))} ∧
    Set.range (arithmeticMovedModelFiber X₀ E Q s σ) =
      {z | z.left ≫ Q.obj.hom ≫ Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
        Spec.map (CommRingCat.ofHom
          (i.toRingHom.comp (σ.toRingHom.comp E.val.toRingHom)))} := by
  refine ⟨arithmeticModelFiber_injective X₀ E Q s s rfl,
    arithmeticModelFiber_injective X₀ E Q s _ (arithmeticLiftMap_basepoint X₀ s σ),
    ?_, ?_⟩
  · have hscalar : s ≫ fieldExtensionBaseMap X₀ E.val ≫ Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
        Spec.map (CommRingCat.ofHom (i.toRingHom.comp E.val.toRingHom)) := by
      simp only [fieldExtensionBaseMap, Limits.pullback.map, Limits.pullback.lift_snd]
      rw [← Category.assoc, hi, ← Spec.map_comp]
      rfl
    rw [arithmeticModelFiber_range, hscalar]
  · have hscalar : (s ≫ arithmeticLiftMap X₀ σ) ≫ fieldExtensionBaseMap X₀ E.val ≫
        Limits.pullback.snd X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
        Spec.map (CommRingCat.ofHom
          (i.toRingHom.comp (σ.toRingHom.comp E.val.toRingHom))) := by
      simp only [arithmeticLiftMap, fieldExtensionBaseMap, Limits.pullback.map,
        Category.assoc, Limits.pullback.lift_snd_assoc, Limits.pullback.lift_snd]
      rw [← Category.assoc, hi, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    change Set.range (arithmeticModelFiber X₀ E Q s _ _) = _
    rw [arithmeticModelFiber_range, hscalar]

/-- The existing stalk functor restricted to the existing finite locally constant category.
Source: Stacks Tags 03Q1 and 03RV (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable abbrev arithmeticStalk {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) : Y.FLC ⥤ Type (u + 1) :=
  ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber (A := Type (u + 1))

/-- The existing forgetful and universe-lift functors for a finite fibre functor.
Source: Stacks Tag 03Q1 (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable abbrev arithmeticUnderlying {C : Type (u + 1)} [Category.{u} C]
    (F : C ⥤ FintypeCat.{u}) : C ⥤ Type (u + 1) :=
  F ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}

/-- Apply the existing forgetful and universe-lift functors to a finite natural path.
Source: Stacks Tag 03Q1 (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable abbrev arithmeticUnderlyingIso {C : Type (u + 1)} [Category.{u} C]
    {F G : C ⥤ FintypeCat.{u}} (a : F ≅ G) : arithmeticUnderlying F ≅ arithmeticUnderlying G :=
  Functor.isoWhiskerRight a (CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u})

/-- The canonical stalk comparison, obtained from the Yoneda identification and the
existing point/Yoneda comparison, with no choice of a fibre path.
Source: Stacks Tags 03Q1 and 03RV (blueprint: lem-wf-arithmetic-lift-fibre-path). -/
noncomputable def arithmeticStalkComparison {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) (e : Y.FiniteEtale ≌ Y.FLC)
    (α : e.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1}) :
    e.functor ⋙ arithmeticStalk s ≅ arithmeticUnderlying (fiber s) :=
  have e₀ : Y.smallEtaleTopology.uliftYoneda.{u + 1} ⋙
      (pointSmallEtale s).sheafFiber (A := Type (u + 1)) ≅
        (pointSmallEtale s).fiber ⋙ uliftFunctor.{u + 1, u} :=
    Functor.isoWhiskerLeft Y.smallEtaleTopology.uliftYoneda
        ((pointSmallEtale s).uliftSheafFiberIso (Type (u + 1))).symm ≪≫
      Functor.isoWhiskerRight uliftYonedaIsoShrinkYoneda
        (pointSmallEtale s).ulift.{u + 1}.presheafFiber ≪≫
      (pointSmallEtale s).ulift.{u + 1}.shrinkYonedaCompPresheafFiberIso
  Functor.isoWhiskerRight α (pointSmallEtale s).sheafFiber ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _) e₀

/-- Arithmetic lifts give the normalized semilinear paths of finite fibre functors.

Source: Stacks Project, Tags 0BTX (lemma-ses-field), 0BTV (lemma-limit), 0BND
(theorem-fundamental-group), and 0BNE (lemma-fundamental-group-Galois-group), together
with the pointed universal-cover convention of Weil II (1.1.12), p. 152.
(blueprint: lem-wf-arithmetic-lift-fibre-path)

Proof (postponed).
1. Every finite intermediate constant cover is finite étale, since K is perfect, and
   connected: Y maps surjectively onto it. Finite constant covers have their labelled
   embedding fibres by Tag 0BNE and `fiberConstantCoverEquiv`.
2. Naturality of an arithmetic automorphism on finite Galois constant covers makes its
   permutation left multiplication by a unique Galois element. Restriction between stages
   gives r. The finite evaluation maps are continuous, so r is continuous for the Krull
   topology. The canonical base-change restriction gives j and its continuity (Tag 0BND).
3. Connectedness of every finite constant cover gives transitivity on its embedding fibre.
   Thus the image of r surjects onto every finite Galois quotient. Compactness makes that
   image closed, hence r is surjective.
4. The stabilizer of the distinguished embedding at a finite stage is the image of its
   fundamental group. Tag 0BTV identifies Aut(F) with the inverse limit over these groups.
   Their intersection is ker r, proving injectivity of j and image j = ker r.
5. Descend a finite étale cover and its morphisms to a finite field E by
   `finiteEtale_fieldLimit_descent`. Composition with Y_E → Y₀ is finite étale. Forgetting
   the L-structure is postcomposition with the first projection; the fibre-product
   universal property proves injectivity and identifies the image by its scalar map.
6. On the finite model, t⁻¹ changes the label i sigma|E to i|E, since r(t) = sigma.
   The unique inverse of the latter injection defines lambda_t. This proves the displayed
   evaluation rule with t⁻¹, and its inverse is given by t between the two labelled fibres.
7. Refinement commutes with both forgetful injections and with t. Any two finite models
   have a common refinement, as do their comparison and inverse maps (Tag 0BTV). Thus the
   rule is independent of the model.
8. Descend every morphism at a common stage. Naturality of t there and commutation of the
   injections give naturality of lambda, for every morphism, so it is a natural isomorphism.
9. Restriction along the first-projection fibre comparison identifies the geometric action
   with j. Applying it on both sides of the evaluation rule gives t⁻¹ j(a) t and hence
   the conjugation identity; injectivity gives its unique geometric representative c.
10. Replacing t by j(a)t gives (j(a)t)⁻¹ = t⁻¹j(a)⁻¹. The same rule gives
    lambda_(j(a)t) = lambda_t composed with the inverse geometric action on the moved fibre.
11. To prove surjectivity onto all natural paths, choose any lift t and any path lambda.
    Then b = lambda composed with lambda_t⁻¹ is in Aut(F). Set s = t j(b)⁻¹. The
    evaluation rule gives lambda_s = lambda on every finite model, hence on every cover.
    For injectivity write s' = j(a)s using exactness. Equal paths force a to act trivially
    on every h_sigma-pullback fibre by step 10. Pullback by h_sigma is an equivalence,
    with inverse pullback by h_(sigma⁻¹), so a acts trivially on every cover and a = 1.
    The forward construction used no reference lift, so this bijection is canonical.
12. The equivalence of Tag 03RV with its Yoneda identification and the canonical point/
    Yoneda comparison identifies fibres with stalks. Whiskering along an equivalence is
    fully faithful and essentially surjective on natural isomorphisms. Transport lambda
    and the geometric automorphisms through these specified comparisons. This gives the
    stalk-path bijection, its comparison square, and both identities on all FLC sheaves.
    No coefficient module, descent datum, or Weil group is used.
-/
theorem arithmeticLiftFibrePath
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [Algebra.IsAlgebraic K L]
    {X₀ : Over (Spec (.of K))} [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [ConnectedSpace (fieldExtensionBase X₀ L)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (i : L →ₐ[K] Ω)
    (hi : s ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom i.toRingHom)) :
    ∃ (j : Aut (fiber s) →* Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)))
      (r : Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)) →*
        (L ≃ₐ[K] L)),
      Continuous j ∧ Continuous r ∧
      (∀ a : Aut (fiber s), j a =
        fiberAutBaseChange (arithmeticBaseProjection (L := L) X₀) s a) ∧
      (∀ (g : Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)))
        (E : IntermediateField K L) [FiniteDimensional K E] (τ : E →ₐ[K] L)
        (z : (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)).obj
          (constantCover X₀.hom (arithmeticConstantAlgebra E))),
        (fiberConstantCoverEquiv X₀.hom (s ≫ arithmeticBaseProjection X₀)
          (arithmeticConstantAlgebra E) z).1 = i.toRingHom.comp τ.toRingHom →
        (fiberConstantCoverEquiv X₀.hom (s ≫ arithmeticBaseProjection X₀)
          (arithmeticConstantAlgebra E) (g.hom.app _ z)).1 =
            i.toRingHom.comp ((r g).toRingHom.comp τ.toRingHom)) ∧
      Function.Injective j ∧ Function.Surjective r ∧
      Set.range j = {g | r g = 1} ∧
      (∀ (σ : L ≃ₐ[K] L),
        ∃ (Φ : (r ⁻¹' ({σ} : Set (L ≃ₐ[K] L))) ≃
            (fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s)),
          (∀ (E : IntermediateField K L) [FiniteDimensional K E]
            (Q : (fieldExtensionBase X₀ E).FiniteEtale),
            Function.Injective (arithmeticModelFiber X₀ E Q s s rfl) ∧
            Function.Injective (arithmeticMovedModelFiber X₀ E Q s σ) ∧
            Set.range (arithmeticModelFiber X₀ E Q s s rfl) =
              {z | z.left ≫ Q.obj.hom ≫ Limits.pullback.snd X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
                Spec.map (CommRingCat.ofHom (i.toRingHom.comp E.val.toRingHom))} ∧
            Set.range (arithmeticMovedModelFiber X₀ E Q s σ) =
              {z | z.left ≫ Q.obj.hom ≫ Limits.pullback.snd X₀.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap K E))) =
                Spec.map (CommRingCat.ofHom
                  (i.toRingHom.comp (σ.toRingHom.comp E.val.toRingHom)))} ∧
            ∀ (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)))
              (z : (fiber (s ≫ arithmeticLiftMap X₀ σ)).obj
                ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)),
              arithmeticModelFiber X₀ E Q s s rfl ((Φ t).hom.app _ z) =
                (t.1⁻¹).hom.app (arithmeticModelCover X₀ E Q)
                  (arithmeticMovedModelFiber X₀ E Q s σ z)) ∧
          (∀ (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L))) (a : Aut (fiber s)),
            ∃ c : Aut (fiber s),
              j c = t.1⁻¹ * j a * t.1 ∧
              ∀ (Q : (fieldExtensionBase X₀ L).FiniteEtale)
                (z : (fiber (s ≫ arithmeticLiftMap X₀ σ)).obj Q),
                (Φ t).hom.app Q ((arithmeticFibreAut X₀ σ s a).hom.app Q z) =
                  c.hom.app Q ((Φ t).hom.app Q z)) ∧
          (∀ (a : Aut (fiber s))
            (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)))
            (h : r (j a * t.1) = σ),
            Φ ⟨j a * t.1, h⟩ =
              arithmeticFibreAut X₀ σ s (a⁻¹) ≪≫ Φ t) ∧
          (∀ (e : (fieldExtensionBase X₀ L).FiniteEtale ≌ (fieldExtensionBase X₀ L).FLC)
            (α : e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
              (fieldExtensionBase X₀ L).smallEtaleTopology.uliftYoneda.{u + 1}),
            ∃ (Ψ : (r ⁻¹' ({σ} : Set (L ≃ₐ[K] L))) ≃
                (arithmeticStalk (s ≫ arithmeticLiftMap X₀ σ) ≅ arithmeticStalk s)),
              (∀ t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)),
                Functor.isoWhiskerLeft e.functor (Ψ t) =
                  arithmeticStalkComparison (s ≫ arithmeticLiftMap X₀ σ) e α ≪≫
                    arithmeticUnderlyingIso (Φ t) ≪≫
                    (arithmeticStalkComparison s e α).symm) ∧
              ∀ a : Aut (fiber s),
                ∃ (A : Aut (arithmeticStalk s))
                  (B : Aut (arithmeticStalk (s ≫ arithmeticLiftMap X₀ σ))),
                  Functor.isoWhiskerLeft e.functor A =
                    arithmeticStalkComparison s e α ≪≫ arithmeticUnderlyingIso a ≪≫
                      (arithmeticStalkComparison s e α).symm ∧
                  Functor.isoWhiskerLeft e.functor B =
                    arithmeticStalkComparison (s ≫ arithmeticLiftMap X₀ σ) e α ≪≫
                      arithmeticUnderlyingIso (arithmeticFibreAut X₀ σ s a) ≪≫
                      (arithmeticStalkComparison (s ≫ arithmeticLiftMap X₀ σ) e α).symm ∧
                  (∀ t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)),
                    ∃ (c : Aut (fiber s)) (C : Aut (arithmeticStalk s)),
                      j c = t.1⁻¹ * j a * t.1 ∧
                      Functor.isoWhiskerLeft e.functor C =
                        arithmeticStalkComparison s e α ≪≫ arithmeticUnderlyingIso c ≪≫
                          (arithmeticStalkComparison s e α).symm ∧
                      B ≪≫ Ψ t = Ψ t ≪≫ C) ∧
                  (∀ (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)))
                    (h : r (j a * t.1) = σ),
                    Ψ ⟨j a * t.1, h⟩ = B.symm ≪≫ Ψ t))) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
