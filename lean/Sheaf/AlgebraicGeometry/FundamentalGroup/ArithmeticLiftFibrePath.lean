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
import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
import Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticExactSequence

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

open scoped CategoryTheory.PreGaloisCategory

private theorem path_restriction_injective {C : Type*} [Category C] {X Y : C}
    {G : Type*} [Group G] (j : Aut Y →* G) (hj : Function.Injective j)
    (q : (X ≅ Y) → G) (hq : ∀ lam a, q (lam ≪≫ a) = j a * q lam) :
    Function.Injective q := by
  intro lam mu h
  have he : j (lam.symm ≪≫ mu) = 1 := by
    have hh := hq lam (lam.symm ≪≫ mu)
    simp only [Iso.self_symm_id_assoc] at hh
    rw [h] at hh
    exact mul_right_cancel (hh.symm.trans (one_mul _).symm)
  have ha : lam.symm ≪≫ mu = Iso.refl _ := hj (he.trans (map_one j).symm)
  calc
    lam = lam ≪≫ (lam.symm ≪≫ mu) := by rw [ha]; simp
    _ = mu := by simp

private noncomputable def restrictAut {C D E : Type*}
    [Category C] [Category D] [Category E] (H : C ⥤ D)
    {F : D ⥤ E} {G : C ⥤ E} (e : H ⋙ F ≅ G) : Aut F →* Aut G where
  toFun a := e.symm ≪≫ Functor.isoWhiskerLeft H a ≪≫ e
  map_one' := by
    change e.symm ≪≫ Functor.isoWhiskerLeft H (Iso.refl F) ≪≫ e = Iso.refl G
    simp
  map_mul' a b := by ext X; simp [Aut.Aut_mul_def]

private theorem restrictAut_continuous {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {F : D ⥤ FintypeCat.{u}} {G : C ⥤ FintypeCat.{u}}
    (e : H ⋙ F ≅ G) : Continuous (restrictAut H e) := by
  apply (CategoryTheory.PreGaloisCategory.autEmbedding_isClosedEmbedding G).isInducing
    |>.continuous_iff.mpr
  apply continuous_pi
  intro P
  change Continuous (fun a : Aut F ↦
    (Aut.autMulEquivOfIso (e.app P))
      (CategoryTheory.PreGaloisCategory.autEmbedding F a (H.obj P)))
  exact continuous_of_discreteTopology.comp ((continuous_apply _).comp continuous_induced_dom)

private theorem path_lift_equiv {C : Type*} [Category C] {X Y : C}
    {G H : Type*} [Group G] [Group H] (j : Aut Y →* G)
    (hj : Function.Injective j) (r : G →* H)
    (hex : Set.range j = {g | r g = 1}) (σ : H)
    (q : (X ≅ Y) → G) (hq : ∀ lam a, q (lam ≪≫ a) = j a * q lam)
    (hr : ∀ lam, r (q lam)⁻¹ = σ) (hn : Nonempty (X ≅ Y)) :
    ∃ Φ : (r ⁻¹' ({σ} : Set H)) ≃ (X ≅ Y), ∀ t, q (Φ t) = t.1⁻¹ := by
  classical
  let f : (X ≅ Y) → (r ⁻¹' ({σ} : Set H)) := fun lam ↦ ⟨(q lam)⁻¹, hr lam⟩
  have hfi : Function.Injective f := by
    intro lam mu h
    apply path_restriction_injective j hj q hq
    exact inv_injective (congrArg Subtype.val h)
  have hfs : Function.Surjective f := by
    intro t
    obtain ⟨lam⟩ := hn
    have ht : r t.val = σ := t.property
    have hk : t.val⁻¹ * (q lam)⁻¹ ∈ Set.range j := by
      rw [hex]
      change r (t.val⁻¹ * (q lam)⁻¹) = 1
      rw [map_mul, map_inv, ht, hr, inv_mul_cancel]
    obtain ⟨a, ha⟩ := hk
    refine ⟨lam ≪≫ a, Subtype.ext ?_⟩
    change (q (lam ≪≫ a))⁻¹ = t.val
    rw [hq, ha, mul_assoc, inv_mul_cancel, mul_one, inv_inv]
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e.symm, ?_⟩
  intro t
  have ht := congrArg Subtype.val (e.apply_symm_apply t)
  exact inv_injective (ht.trans (inv_inv t.val).symm)

section PathRestriction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (X₀ : Over (Spec (.of K))) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)

@[irreducible]
private noncomputable def arithmeticInclusion :
    Aut (fiber s) →* Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)) :=
  restrictAut (pullback (arithmeticBaseProjection (L := L) X₀))
    (pullbackFiberIso (arithmeticBaseProjection (L := L) X₀) s)

private theorem arithmeticInclusion_apply (a : Aut (fiber s)) :
    arithmeticInclusion X₀ s a = fiberAutBaseChange (arithmeticBaseProjection (L := L) X₀) s a := by
  unfold arithmeticInclusion
  rfl

private theorem arithmeticInclusion_continuous : Continuous (arithmeticInclusion X₀ s) := by
  unfold arithmeticInclusion
  exact restrictAut_continuous _ _

@[irreducible]
private noncomputable def arithmeticPathRestriction (σ : L ≃ₐ[K] L)
    (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s) :
    Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)) :=
  (eqToIso (congrArg fiber (arithmeticLiftMap_basepoint X₀ s σ))).symm ≪≫
    pullbackPathIso (arithmeticBaseProjection (L := L) X₀) lam

private theorem arithmeticPathRestriction_post (σ : L ≃ₐ[K] L)
    (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s) (a : Aut (fiber s)) :
    arithmeticPathRestriction X₀ s σ (lam ≪≫ a) =
      arithmeticInclusion X₀ s a * arithmeticPathRestriction X₀ s σ lam := by
  ext P z
  simp [arithmeticPathRestriction, pullbackPathIso, arithmeticInclusion_apply,
    fiberAutBaseChange, Aut.Aut_mul_def]

private theorem arithmeticPathRestriction_injective
    [PerfectField K] [Algebra.IsSeparable K L] [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] (σ : L ≃ₐ[K] L) :
    Function.Injective (arithmeticPathRestriction X₀ s σ) := by
  apply path_restriction_injective (arithmeticInclusion X₀ s)
  · intro a b hab
    apply arithmeticBaseChange_injective X₀ s
    simpa only [arithmeticInclusion_apply] using hab
  · exact arithmeticPathRestriction_post X₀ s σ

@[irreducible]
private noncomputable def arithmeticModelComparison [PerfectField K]
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale) :
    (pullback (fieldExtensionBaseMap X₀ E.val)).obj Q ⟶
      (pullback (arithmeticBaseProjection (L := L) X₀)).obj (arithmeticModelCover X₀ E Q) :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift
      (Limits.pullback.fst Q.obj.hom (fieldExtensionBaseMap X₀ E.val))
      (Limits.pullback.snd Q.obj.hom (fieldExtensionBaseMap X₀ E.val)) (by
        change Limits.pullback.fst Q.obj.hom (fieldExtensionBaseMap X₀ E.val) ≫
            (Q.obj.hom ≫ arithmeticBaseProjection (L := E) X₀) =
          Limits.pullback.snd Q.obj.hom (fieldExtensionBaseMap X₀ E.val) ≫
            arithmeticBaseProjection (L := L) X₀
        rw [← Category.assoc, Limits.pullback.condition, Category.assoc]
        congr 1
        simp [fieldExtensionBaseMap, arithmeticBaseProjection]))
    (Limits.pullback.lift_snd _ _ _))

private theorem arithmeticModelComparison_fst [PerfectField K]
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale) :
    (arithmeticModelComparison X₀ E Q).hom.left ≫
      Limits.pullback.fst (arithmeticModelCover X₀ E Q).obj.hom
        (arithmeticBaseProjection (L := L) X₀) =
      Limits.pullback.fst Q.obj.hom (fieldExtensionBaseMap X₀ E.val) := by
  unfold arithmeticModelComparison
  exact Limits.pullback.lift_fst _ _ _

private theorem arithmeticPathRestriction_model [PerfectField K] (σ : L ≃ₐ[K] L)
    (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s)
    (E : IntermediateField K L) [FiniteDimensional K E]
    (Q : (fieldExtensionBase X₀ E).FiniteEtale)
    (z : (fiber (s ≫ arithmeticLiftMap X₀ σ)).obj
      ((pullback (fieldExtensionBaseMap X₀ E.val)).obj Q)) :
    arithmeticModelFiber X₀ E Q s s rfl (lam.hom.app _ z) =
      (arithmeticPathRestriction X₀ s σ lam).hom.app (arithmeticModelCover X₀ E Q)
        (arithmeticMovedModelFiber X₀ E Q s σ z) := by
  let p := arithmeticBaseProjection (L := L) X₀
  let A := arithmeticModelCover X₀ E Q
  let φ := arithmeticModelComparison X₀ E Q
  let δ := eqToIso (congrArg fiber (arithmeticLiftMap_basepoint X₀ s σ))
  have hw : (pullbackFiberIso p (s ≫ arithmeticLiftMap X₀ σ)).inv.app A
      (δ.inv.app A (arithmeticMovedModelFiber X₀ E Q s σ z)) =
        (fiber (s ≫ arithmeticLiftMap X₀ σ)).map φ z := by
    apply fiber_ext
    apply Limits.pullback.hom_ext
    · change (Limits.pullback.lift _ _ _) ≫ Limits.pullback.fst _ _ = _
      rw [Limits.pullback.lift_fst]
      have hd := eqToIso_fiber_hom_app_left
        (arithmeticLiftMap_basepoint X₀ s σ).symm
        (congrArg fiber (arithmeticLiftMap_basepoint X₀ s σ)).symm A
        (arithmeticMovedModelFiber X₀ E Q s σ z)
      change _ = _ at hd
      calc
        _ = (arithmeticMovedModelFiber X₀ E Q s σ z).left := hd
        _ = _ := by
          rw [fiber_map_left, Category.assoc, arithmeticModelComparison_fst]
          rfl
    · rw [pullbackFiberIso_inv_app_left, Limits.pullback.lift_snd,
        fiber_map_left, Category.assoc]
      change s ≫ arithmeticLiftMap X₀ σ =
        z.left ≫ φ.hom.left ≫ ((pullback p).obj A).obj.hom
      rw [hom_left_comp]
      exact (fiber_left_comp _ z).symm
  unfold arithmeticPathRestriction
  change _ = (pullbackFiberIso p s).hom.app A
    (lam.hom.app _ ((pullbackFiberIso p (s ≫ arithmeticLiftMap X₀ σ)).inv.app A
      (δ.inv.app A (arithmeticMovedModelFiber X₀ E Q s σ z))))
  rw [hw, ← ConcreteCategory.comp_apply, lam.hom.naturality, ConcreteCategory.comp_apply]
  apply fiber_ext
  rw [pullbackFiberIso_hom_app_left, fiber_map_left, Category.assoc,
    arithmeticModelComparison_fst]
  rfl

@[irreducible]
private noncomputable def arithmeticConstantSection (A : FiniteEtaleAlgebra K)
    (τ : A.1 →ₐ[K] L) :
    fieldExtensionBase X₀ L ⟶ ((pullback (arithmeticBaseProjection (L := L) X₀)).obj
      (constantCover X₀.hom A)).obj.left := by
  let p := arithmeticBaseProjection (L := L) X₀
  let ℓ := Limits.pullback.snd X₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have hw : p ≫ X₀.hom =
      (ℓ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) ≫ A.specHom := by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hτ : τ.toRingHom.comp (algebraMap K A.1) = algebraMap K L := by
      ext a
      exact τ.commutes a
    rw [hτ]
    exact Limits.pullback.condition
  exact Limits.pullback.lift (Limits.pullback.lift p
    (ℓ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)) hw) (𝟙 _) (by simp [p])

private theorem arithmeticConstantSection_snd (A : FiniteEtaleAlgebra K)
    (τ : A.1 →ₐ[K] L) :
    arithmeticConstantSection X₀ A τ ≫
      ((pullback (arithmeticBaseProjection (L := L) X₀)).obj (constantCover X₀.hom A)).obj.hom =
        𝟙 _ := by
  unfold arithmeticConstantSection
  exact Limits.pullback.lift_snd _ _ _

private theorem arithmeticConstantSection_label (A : FiniteEtaleAlgebra K)
    (τ : A.1 →ₐ[K] L) :
    arithmeticConstantSection X₀ A τ ≫
      Limits.pullback.fst (constantCover X₀.hom A).obj.hom (arithmeticBaseProjection (L := L) X₀) ≫
        Limits.pullback.snd X₀.hom A.specHom =
      Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
          Spec.map (CommRingCat.ofHom τ.toRingHom) := by
  unfold arithmeticConstantSection
  simp only [Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd]

private theorem constantCover_scalar (A : FiniteEtaleAlgebra K)
    (z : (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)).obj (constantCover X₀.hom A))
    (ρ : A.1 →+* Ω) :
    (fiberConstantCoverEquiv X₀.hom _ A z).1 = ρ ↔
      z.left ≫ Limits.pullback.snd X₀.hom A.specHom =
        Spec.map (CommRingCat.ofHom ρ) := by
  rw [fiberConstantCoverEquiv_apply]
  constructor
  · intro h
    rw [← Spec.map_preimage (z.left ≫ Limits.pullback.snd X₀.hom A.specHom)]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h
  · intro h
    rw [h, Spec.preimage_map]
    rfl

private theorem arithmeticPathRestriction_constant [Algebra K Ω]
    (i : L →ₐ[K] Ω)
    (hi : s ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom i.toRingHom))
    (σ : L ≃ₐ[K] L) (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s)
    (A : FiniteEtaleAlgebra K) (τ : A.1 →ₐ[K] L) :
    ∃ z : (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)).obj (constantCover X₀.hom A),
      (fiberConstantCoverEquiv X₀.hom _ A z).1 = i.toRingHom.comp τ.toRingHom ∧
      (fiberConstantCoverEquiv X₀.hom _ A
        ((arithmeticPathRestriction X₀ s σ lam)⁻¹.hom.app _ z)).1 =
          i.toRingHom.comp (σ.toRingHom.comp τ.toRingHom) := by
  let p := arithmeticBaseProjection (L := L) X₀
  let P := (pullback p).obj (constantCover X₀.hom A)
  let sec := arithmeticConstantSection X₀ A τ
  let w := fiberMk s P (s ≫ sec) (by
    rw [Category.assoc, arithmeticConstantSection_snd, Category.comp_id])
  let z := (pullbackFiberIso p s).hom.app _ w
  refine ⟨z, ?_, ?_⟩
  · apply (constantCover_scalar X₀ s A z _).mpr
    change (s ≫ sec) ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ = _
    rw [Category.assoc, arithmeticConstantSection_label, ← Category.assoc, hi,
      ← Spec.map_comp]
    rfl
  · have hw : (lam.inv.app P w).left = (s ≫ arithmeticLiftMap X₀ σ) ≫ sec :=
      path_section lam.symm P sec (arithmeticConstantSection_snd X₀ A τ) w rfl
    apply (constantCover_scalar X₀ s A _ _).mpr
    unfold arithmeticPathRestriction
    change ((eqToIso (congrArg fiber (arithmeticLiftMap_basepoint X₀ s σ))).hom.app _
      ((pullbackFiberIso p (s ≫ arithmeticLiftMap X₀ σ)).hom.app _
        (lam.inv.app P ((pullbackFiberIso p s).inv.app _ z)))).left ≫ _ = _
    have hz : (pullbackFiberIso p s).inv.app _ z = w :=
      ConcreteCategory.congr_hom ((pullbackFiberIso p s).hom_inv_id_app _) w
    rw [hz, eqToIso_fiber_hom_app_left (arithmeticLiftMap_basepoint X₀ s σ),
      pullbackFiberIso_hom_app_left, hw]
    rw [Category.assoc, Category.assoc, arithmeticConstantSection_label]
    simp only [arithmeticLiftMap, fieldExtensionBaseMap, Limits.pullback.map,
      Category.assoc, Limits.pullback.lift_snd_assoc]
    rw [← Category.assoc, hi, ← Spec.map_comp, ← Spec.map_comp]
    rfl

private theorem arithmeticPathRestriction_image
    [PerfectField K] [Algebra.IsAlgebraic K L] [Algebra K Ω]
    (i : L →ₐ[K] Ω)
    (hi : s ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom i.toRingHom))
    (r : Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)) →* (L ≃ₐ[K] L))
    (hr : ∀ (g : Aut (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)))
      (E : IntermediateField K L) [FiniteDimensional K E] (τ : E →ₐ[K] L)
      (z : (fiber (s ≫ arithmeticBaseProjection (L := L) X₀)).obj
        (constantCover X₀.hom (arithmeticConstantAlgebra E))),
      (fiberConstantCoverEquiv X₀.hom _ (arithmeticConstantAlgebra E) z).1 =
          i.toRingHom.comp τ.toRingHom →
      (fiberConstantCoverEquiv X₀.hom _ (arithmeticConstantAlgebra E)
        (g.hom.app _ z)).1 = i.toRingHom.comp ((r g).toRingHom.comp τ.toRingHom))
    (σ : L ≃ₐ[K] L) (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s) :
    r (arithmeticPathRestriction X₀ s σ lam)⁻¹ = σ := by
  ext a
  let E := IntermediateField.adjoin K ({a} : Set L)
  have : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  obtain ⟨z, hz, hz'⟩ := arithmeticPathRestriction_constant X₀ s i hi σ lam
    (arithmeticConstantAlgebra E) E.val
  have he := (hr (arithmeticPathRestriction X₀ s σ lam)⁻¹ E E.val z hz).symm.trans hz'
  have ha := DFunLike.congr_fun he (⟨a, IntermediateField.subset_adjoin K _ rfl⟩ : E)
  exact i.injective ha

private theorem eqToIso_conjugacy {C : Type*} [Category C] {X Y Z : C}
    (p : X = Y) (q : X = Z) (r : Y = Z) (R : Aut Y) (J : Aut Z)
    (he : eqToIso p ≪≫ R ≪≫ (eqToIso p).symm =
      eqToIso q ≪≫ J ≪≫ (eqToIso q).symm) :
    (eqToIso r).symm ≪≫ R ≪≫ eqToIso r = J := by
  subst p
  subst q
  simpa using he

attribute [local irreducible] fiber

private theorem pullbackPathIso_pre_over {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : X ⟶ X) (hh : h ≫ f = f) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (a : Aut (fiber s))
    (hs : (s ≫ h) ≫ f = s ≫ f) :
    (eqToIso (congrArg fiber hs)).symm ≪≫
      pullbackPathIso f (pullbackPathIso h a) ≪≫ eqToIso (congrArg fiber hs) =
        pullbackPathIso f a := by
  exact eqToIso_conjugacy
    (congrArg fiber (Category.assoc s h f).symm)
    (congrArg fiber (congrArg (fun z ↦ s ≫ z) hh))
    (congrArg fiber hs) _ _ ((pullbackPathIso_comp h f a).symm.trans
      (pullbackPathIso_congr hh a))

private theorem arithmeticPathRestriction_pre (σ : L ≃ₐ[K] L)
    (lam : fiber (s ≫ arithmeticLiftMap X₀ σ) ≅ fiber s) (a : Aut (fiber s)) :
    arithmeticPathRestriction X₀ s σ (arithmeticFibreAut X₀ σ s a ≪≫ lam) =
      arithmeticPathRestriction X₀ s σ lam * arithmeticInclusion X₀ s a := by
  let f := arithmeticBaseProjection (L := L) X₀
  let h := arithmeticLiftMap X₀ σ
  have hh : h ≫ f = f := by
    simp [h, f, arithmeticLiftMap, arithmeticBaseProjection, fieldExtensionBaseMap]
  let δ : fiber ((s ≫ h) ≫ f) ≅ fiber (s ≫ f) :=
    eqToIso (congrArg fiber (arithmeticLiftMap_basepoint X₀ s σ))
  have hb : δ.symm ≪≫ pullbackPathIso f (pullbackPathIso h a) ≪≫ δ =
      pullbackPathIso f a :=
    pullbackPathIso_pre_over f h hh s a (arithmeticLiftMap_basepoint X₀ s σ)
  have hpre : arithmeticPathRestriction X₀ s σ
      (arithmeticFibreAut X₀ σ s a ≪≫ lam) =
      (δ.symm ≪≫ pullbackPathIso f (pullbackPathIso h a) ≪≫ δ) ≪≫
        arithmeticPathRestriction X₀ s σ lam := by
    unfold arithmeticPathRestriction
    change δ.symm ≪≫ pullbackPathIso f (pullbackPathIso h a ≪≫ lam) =
      (δ.symm ≪≫ pullbackPathIso f (pullbackPathIso h a) ≪≫ δ) ≪≫
        (δ.symm ≪≫ pullbackPathIso f lam)
    simp only [pullbackPathIso_trans, Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [hpre, hb, arithmeticInclusion_apply]
  rfl

private theorem arithmeticFibreAut_inv (σ : L ≃ₐ[K] L) (a : Aut (fiber s)) :
    arithmeticFibreAut X₀ σ s a⁻¹ = (arithmeticFibreAut X₀ σ s a)⁻¹ := by
  exact map_inv (restrictAut (pullback (arithmeticLiftMap X₀ σ))
    (pullbackFiberIso (arithmeticLiftMap X₀ σ) s)) a

end PathRestriction

private noncomputable def stalkIsoEquiv {Y : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x y : Spec (.of Ω) ⟶ Y)
    (e : Y.FiniteEtale ≌ Y.FLC)
    (α : e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Y.smallEtaleTopology.uliftYoneda.{u + 1}) :
    (fiber x ≅ fiber y) ≃ (arithmeticStalk x ≅ arithmeticStalk y) := by
  let U := CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  let V := (Functor.whiskeringRight Y.FiniteEtale FintypeCat.{u} (Type (u + 1))).obj U
  let W := (Functor.whiskeringLeft Y.FiniteEtale Y.FLC (Type (u + 1))).obj e.functor
  let v := (Functor.FullyFaithful.ofFullyFaithful V).isoEquiv
    (X := fiber x) (Y := fiber y)
  let w := (Functor.FullyFaithful.ofFullyFaithful W).isoEquiv
    (X := arithmeticStalk x) (Y := arithmeticStalk y)
  let c : (arithmeticUnderlying (fiber x) ≅ arithmeticUnderlying (fiber y)) ≃
      (e.functor ⋙ arithmeticStalk x ≅ e.functor ⋙ arithmeticStalk y) :=
    { toFun := fun f ↦ arithmeticStalkComparison x e α ≪≫ f ≪≫
        (arithmeticStalkComparison y e α).symm
      invFun := fun f ↦ (arithmeticStalkComparison x e α).symm ≪≫ f ≪≫
        arithmeticStalkComparison y e α
      left_inv := by intro f; simp
      right_inv := by intro f; simp }
  exact v.trans (c.trans w.symm)

private theorem stalkIsoEquiv_spec {Y : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x y : Spec (.of Ω) ⟶ Y)
    (e : Y.FiniteEtale ≌ Y.FLC)
    (α : e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Y.smallEtaleTopology.uliftYoneda.{u + 1}) (f : fiber x ≅ fiber y) :
    Functor.isoWhiskerLeft e.functor (stalkIsoEquiv x y e α f) =
      arithmeticStalkComparison x e α ≪≫ arithmeticUnderlyingIso f ≪≫
        (arithmeticStalkComparison y e α).symm := by
  apply Iso.ext
  exact ((Functor.whiskeringLeft Y.FiniteEtale Y.FLC (Type (u + 1))).obj e.functor).map_preimage _

private theorem stalkIsoEquiv_trans {Y : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x y z : Spec (.of Ω) ⟶ Y)
    (e : Y.FiniteEtale ≌ Y.FLC)
    (α : e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Y.smallEtaleTopology.uliftYoneda.{u + 1})
    (f : fiber x ≅ fiber y) (g : fiber y ≅ fiber z) :
    stalkIsoEquiv x z e α (f ≪≫ g) =
      stalkIsoEquiv x y e α f ≪≫ stalkIsoEquiv y z e α g := by
  apply ((Functor.whiskeringLeft Y.FiniteEtale Y.FLC (Type (u + 1))).obj e.functor).mapIso_injective
  change Functor.isoWhiskerLeft e.functor (stalkIsoEquiv x z e α (f ≪≫ g)) =
    Functor.isoWhiskerLeft e.functor
      (stalkIsoEquiv x y e α f ≪≫ stalkIsoEquiv y z e α g)
  rw [Functor.isoWhiskerLeft_trans, stalkIsoEquiv_spec, stalkIsoEquiv_spec,
    stalkIsoEquiv_spec]
  simp [arithmeticUnderlyingIso]

private theorem stalkIsoEquiv_symm {Y : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (x y : Spec (.of Ω) ⟶ Y)
    (e : Y.FiniteEtale ≌ Y.FLC)
    (α : e.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
      Y.smallEtaleTopology.uliftYoneda.{u + 1}) (f : fiber x ≅ fiber y) :
    stalkIsoEquiv y x e α f.symm = (stalkIsoEquiv x y e α f).symm := by
  apply ((Functor.whiskeringLeft Y.FiniteEtale Y.FLC (Type (u + 1))).obj e.functor).mapIso_injective
  change Functor.isoWhiskerLeft e.functor (stalkIsoEquiv y x e α f.symm) =
    Functor.isoWhiskerLeft e.functor (stalkIsoEquiv x y e α f).symm
  rw [← Functor.isoWhiskerLeft_symm, stalkIsoEquiv_spec, stalkIsoEquiv_spec]
  simp only [arithmeticUnderlyingIso, ← Functor.isoWhiskerRight_symm, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc]

/-- Arithmetic lifts give the normalized semilinear paths of finite fibre functors.

Source: Stacks Project, Tags 0BTX (lemma-ses-field), 0BTV (lemma-limit), 0BND
(theorem-fundamental-group), and 0BNE (lemma-fundamental-group-Galois-group), together
with the pointed universal-cover convention of Weil II (1.1.12), p. 152.
(blueprint: lem-wf-arithmetic-lift-fibre-path)

Proof: `arithmetic_exactSequence` supplies the arithmetic quotient, its constant-cover
characterization, and its kernel. Restriction through the first-projection fibre
comparison gives the continuous inclusion j. Finite-cover object descent and the
injective finite-model fibre maps prove that j is injective.

Restrict a path lambda from the moved point to the original point along Y → Y₀,
identifying its endpoints over Y₀, to obtain q(lambda). Naturality on the global
sections of pulled-back constant covers gives r(q(lambda)⁻¹) = sigma. Moreover,
q(lambda followed by a) = j(a) q(lambda), and q(B(a) followed by lambda) =
q(lambda) j(a), by coherence of pullback and its first-projection comparisons.
Any two fibre functors on the connected finite-etale Galois category are isomorphic.
Thus paths form a nonempty torsor. Injectivity of j and its kernel description show
that lambda ↦ q(lambda)⁻¹ is a bijection onto r⁻¹(sigma); define Phi by its inverse.

The comparison from a finite model to the pullback of its arithmetic cover and
naturality give the stated evaluation rule on every finite model, with no choices
of descended morphisms. Set c = lambda⁻¹ followed by B(a) followed by lambda.
The two composition formulas for q give j(c) = t⁻¹ j(a) t, and the defining equation
for c gives the pointwise conjugation identity. Applying injectivity of q to
(j(a)t)⁻¹ = t⁻¹ j(a)⁻¹ proves the lift-change identity.

Finally, whiskering with the given finite-etale/FLC equivalence and with the fully
faithful forgetful/ULift functor gives a bijection of natural paths. Conjugate by
the specified stalk comparisons. This bijection preserves composition and inverses,
so the finite-path identities give exactly the required stalk identities.
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
  classical
  let j := arithmeticInclusion X₀ s
  obtain ⟨r, hrc, hrs, hex₀, hr₀⟩ := arithmetic_exactSequence X₀ s i hi
  have hr : ∀ (g : Aut (fiber (s ≫ arithmeticBaseProjection X₀)))
      (E : IntermediateField K L) [FiniteDimensional K E] (τ : E →ₐ[K] L)
      (z : (fiber (s ≫ arithmeticBaseProjection X₀)).obj
        (constantCover X₀.hom (arithmeticConstantAlgebra E))),
      (fiberConstantCoverEquiv X₀.hom _ (arithmeticConstantAlgebra E) z).1 =
          i.toRingHom.comp τ.toRingHom →
      (fiberConstantCoverEquiv X₀.hom _ (arithmeticConstantAlgebra E)
        (g.hom.app _ z)).1 = i.toRingHom.comp ((r g).toRingHom.comp τ.toRingHom) :=
    fun g E _ τ z hz ↦ hr₀ g (arithmeticConstantAlgebra E) τ z hz
  have hj : Function.Injective j := by
    intro a b h
    apply arithmeticBaseChange_injective X₀ s
    simpa only [j, arithmeticInclusion_apply] using h
  have hex : Set.range j = {g | r g = 1} := by
    have hjfun : (fun a ↦ j a) =
        fiberAutBaseChange (arithmeticBaseProjection (L := L) X₀) s :=
      funext (arithmeticInclusion_apply X₀ s)
    exact (congrArg Set.range hjfun).trans hex₀
  refine ⟨j, r, arithmeticInclusion_continuous X₀ s, hrc,
    arithmeticInclusion_apply X₀ s, hr, hj, hrs, hex, ?_⟩
  intro σ
  let q := arithmeticPathRestriction X₀ s σ
  have hpost : ∀ lam a, q (lam ≪≫ a) = j a * q lam :=
    arithmeticPathRestriction_post X₀ s σ
  have hpre : ∀ lam a, q (arithmeticFibreAut X₀ σ s a ≪≫ lam) = q lam * j a :=
    arithmeticPathRestriction_pre X₀ s σ
  have hq : Function.Injective q := arithmeticPathRestriction_injective X₀ s σ
  obtain ⟨Φ, hΦ⟩ := path_lift_equiv j hj r hex σ q hpost
    (arithmeticPathRestriction_image X₀ s i hi r hr σ)
    (CategoryTheory.PreGaloisCategory.nonempty_iso_of_fiberFunctor _ _)
  have hconj (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L))) (a : Aut (fiber s)) :
      ∃ c : Aut (fiber s), j c = t.1⁻¹ * j a * t.1 ∧
        ∀ (Q : (fieldExtensionBase X₀ L).FiniteEtale)
          (z : (fiber (s ≫ arithmeticLiftMap X₀ σ)).obj Q),
          (Φ t).hom.app Q ((arithmeticFibreAut X₀ σ s a).hom.app Q z) =
            c.hom.app Q ((Φ t).hom.app Q z) := by
    let c : Aut (fiber s) := (Φ t).symm ≪≫ arithmeticFibreAut X₀ σ s a ≪≫ Φ t
    have hc : Φ t ≪≫ c = arithmeticFibreAut X₀ σ s a ≪≫ Φ t := by
      simp [c]
    refine ⟨c, ?_, ?_⟩
    · calc
        j c = (j c * q (Φ t)) * (q (Φ t))⁻¹ := by simp
        _ = (q (Φ t) * j a) * (q (Φ t))⁻¹ := by rw [← hpost, hc, hpre]
        _ = t.val⁻¹ * j a * t.val := by rw [hΦ, inv_inv]
    · intro Q z
      exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app Q) hc.symm) z
  have hchange (a : Aut (fiber s)) (t : r ⁻¹' ({σ} : Set (L ≃ₐ[K] L)))
      (h : r (j a * t.1) = σ) :
      Φ ⟨j a * t.1, h⟩ = arithmeticFibreAut X₀ σ s a⁻¹ ≪≫ Φ t := by
    apply hq
    rw [hΦ, hpre, hΦ, map_inv, mul_inv_rev]
  refine ⟨Φ, ?_, hconj, hchange, ?_⟩
  · intro E _ Q
    obtain ⟨h₁, h₂, h₃, h₄⟩ := arithmeticModelFiber_ranges X₀ E Q s i hi σ
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    intro t z
    have hn := arithmeticPathRestriction_model X₀ s σ (Φ t) E Q z
    rw [show arithmeticPathRestriction X₀ s σ (Φ t) = t.val⁻¹ from hΦ t] at hn
    exact hn
  · intro e α
    let T := stalkIsoEquiv (s ≫ arithmeticLiftMap X₀ σ) s e α
    refine ⟨Φ.trans T, ?_, ?_⟩
    · intro t
      exact stalkIsoEquiv_spec _ _ e α (Φ t)
    · intro a
      let A := stalkIsoEquiv s s e α a
      let B := stalkIsoEquiv (s ≫ arithmeticLiftMap X₀ σ)
        (s ≫ arithmeticLiftMap X₀ σ) e α (arithmeticFibreAut X₀ σ s a)
      refine ⟨A, B, stalkIsoEquiv_spec _ _ e α a,
        stalkIsoEquiv_spec _ _ e α (arithmeticFibreAut X₀ σ s a), ?_, ?_⟩
      · intro t
        obtain ⟨c, hc, he⟩ := hconj t a
        refine ⟨c, stalkIsoEquiv s s e α c, hc, stalkIsoEquiv_spec _ _ e α c, ?_⟩
        have hf : arithmeticFibreAut X₀ σ s a ≪≫ Φ t = Φ t ≪≫ c := by
          ext Q z
          exact he Q z
        change stalkIsoEquiv _ _ e α _ ≪≫ stalkIsoEquiv _ _ e α _ =
          stalkIsoEquiv _ _ e α _ ≪≫ stalkIsoEquiv _ _ e α _
        rw [← stalkIsoEquiv_trans, ← stalkIsoEquiv_trans, hf]
      · intro t h
        change stalkIsoEquiv _ _ e α (Φ ⟨j a * t.val, h⟩) =
          (stalkIsoEquiv _ _ e α (arithmeticFibreAut X₀ σ s a)).symm ≪≫
            stalkIsoEquiv _ _ e α (Φ t)
        rw [hchange, stalkIsoEquiv_trans, arithmeticFibreAut_inv]
        exact congrArg (fun z ↦ z ≪≫ stalkIsoEquiv _ _ e α (Φ t))
          (stalkIsoEquiv_symm _ _ e α (arithmeticFibreAut X₀ σ s a))

end AlgebraicGeometry.Scheme.FiniteEtale
