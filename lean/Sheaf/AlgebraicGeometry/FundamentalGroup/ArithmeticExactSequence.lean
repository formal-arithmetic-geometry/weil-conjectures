/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover

/-!
# The arithmetic fundamental group exact sequence

Source: Stacks Project, Tag 0BTX, with the embedding convention of Tag 0BNE.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

private noncomputable abbrev fieldConstantAlgebra (K E : Type u) [Field K]
    [PerfectField K] [Field E] [Algebra K E] [FiniteDimensional K E] :
    FiniteEtaleAlgebra K :=
  ⟨CommAlgCat.of K E, inferInstance,
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K E
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }⟩

@[irreducible]
private noncomputable def constantFiberAlgHomEquiv {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] :
    (fiber s).obj (constantCover p (fieldConstantAlgebra K E)) ≃ (E →ₐ[K] Ω) where
  toFun z :=
    { (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val with
      commutes' x := by
        have h := (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).property
        exact DFunLike.congr_fun (h.trans hb) x }
  invFun f := (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E)).symm
    ⟨f.toRingHom, by rw [hb]; exact f.comp_algebraMap⟩
  left_inv z := by
    apply (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E)).injective
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    apply AlgHom.ext
    intro x
    exact DFunLike.congr_fun (congrArg Subtype.val
      ((fiberConstantCoverEquiv p s (fieldConstantAlgebra K E)).apply_symm_apply
        ⟨f.toRingHom, by rw [hb]; exact f.comp_algebraMap⟩)) x

private theorem constantFiberAlgHomEquiv_label {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]
    (z : (fiber s).obj (constantCover p (fieldConstantAlgebra K E))) :
    (constantFiberAlgHomEquiv p s hb E z).toRingHom =
      (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val := by
  unfold constantFiberAlgHomEquiv
  rfl

@[irreducible]
private noncomputable def constantFiberGaloisEquiv {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] :
    (fiber s).obj (constantCover p (fieldConstantAlgebra K E)) ≃ (E ≃ₐ[K] E) :=
  (constantFiberAlgHomEquiv p s hb E).trans (Normal.algHomEquivAut K Ω E)

private theorem constantFiberGaloisEquiv_label {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω]
    (z : (fiber s).obj (constantCover p (fieldConstantAlgebra K E))) :
    (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val =
      (algebraMap E Ω).comp (constantFiberGaloisEquiv p s hb E z).toRingHom := by
  rw [← constantFiberAlgHomEquiv_label p s hb E z]
  unfold constantFiberGaloisEquiv
  exact congrArg AlgHom.toRingHom
    ((Normal.algHomEquivAut K Ω E).symm_apply_apply
      (constantFiberAlgHomEquiv p s hb E z)).symm

private theorem fibre_multiplier_formula {C : Type*} [Category C]
    (F : C ⥤ FintypeCat.{u}) (A : C) {H : Type*} [Group H]
    (e : F.obj A ≃ H) (τ : H → (A ⟶ A))
    (hτ : ∀ h z, e (F.map (τ h) z) = e z * h) (g : Aut F) (z : F.obj A) :
    e (g.hom.app A z) = e (g.hom.app A (e.symm 1)) * e z := by
  have hz : F.map (τ (e z)) (e.symm 1) = z := by
    apply e.injective
    rw [hτ, e.apply_symm_apply, one_mul]
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (τ (e z))) (e.symm 1)
  simp only [ConcreteCategory.comp_apply] at hn
  rw [hz] at hn
  rw [hn, hτ]

@[irreducible]
private noncomputable def fibreMultiplier {C : Type*} [Category C]
    (F : C ⥤ FintypeCat.{u}) (A : C) {H : Type*} [Group H]
    (e : F.obj A ≃ H) (τ : H → (A ⟶ A))
    (hτ : ∀ h z, e (F.map (τ h) z) = e z * h) : Aut F →* H where
  toFun g := e (g.hom.app A (e.symm 1))
  map_one' := e.apply_symm_apply 1
  map_mul' g h := fibre_multiplier_formula F A e τ hτ g (h.hom.app A (e.symm 1))

private theorem fibreMultiplier_formula {C : Type*} [Category C]
    (F : C ⥤ FintypeCat.{u}) (A : C) {H : Type*} [Group H]
    (e : F.obj A ≃ H) (τ : H → (A ⟶ A))
    (hτ : ∀ h z, e (F.map (τ h) z) = e z * h) (g : Aut F) (z : F.obj A) :
    e (g.hom.app A z) = fibreMultiplier F A e τ hτ g * e z := by
  unfold fibreMultiplier
  exact fibre_multiplier_formula F A e τ hτ g z

open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete

private theorem fibreMultiplier_continuous {C : Type*} [Category C]
    (F : C ⥤ FintypeCat.{u}) (A : C) {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H]
    (e : F.obj A ≃ H) (τ : H → (A ⟶ A))
    (hτ : ∀ h z, e (F.map (τ h) z) = e z * h) :
    Continuous (fibreMultiplier F A e τ hτ) := by
  unfold fibreMultiplier
  change Continuous (fun g : Aut F ↦
    e ((CategoryTheory.PreGaloisCategory.autEmbedding F g A).hom (e.symm 1)))
  exact (show Continuous (fun b : Aut (F.obj A) ↦ e (b.hom (e.symm 1))) from
    continuous_of_discreteTopology).comp ((continuous_apply A).comp continuous_induced_dom)

private theorem constantFiberGaloisEquiv_deck {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] (σ : E ≃ₐ[K] E)
    (z : (fiber s).obj (constantCover p (fieldConstantAlgebra K E))) :
    constantFiberGaloisEquiv p s hb E
      ((fiber s).map (constantCoverHom p σ.toAlgHom) z) =
      constantFiberGaloisEquiv p s hb E z * σ := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  calc
    _ = (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E)
        ((fiber s).map (constantCoverHom p σ.toAlgHom) z)).val x :=
      (DFunLike.congr_fun (constantFiberGaloisEquiv_label p s hb E _) x).symm
    _ = (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val (σ x) := by
      rw [fiberConstantCoverEquiv_fiber_map]
      rfl
    _ = _ := DFunLike.congr_fun (constantFiberGaloisEquiv_label p s hb E z) (σ x)

@[irreducible]
private noncomputable def normalConstantQuotient {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] : Aut (fiber s) →* (E ≃ₐ[K] E) :=
  fibreMultiplier (fiber s) (constantCover p (fieldConstantAlgebra K E))
    (constantFiberGaloisEquiv p s hb E) (fun σ ↦ constantCoverHom p σ.toAlgHom)
    (constantFiberGaloisEquiv_deck p s hb E)

private theorem normalConstantQuotient_formula {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] (g : Aut (fiber s))
    (z : (fiber s).obj (constantCover p (fieldConstantAlgebra K E))) :
    constantFiberGaloisEquiv p s hb E (g.hom.app _ z) =
      normalConstantQuotient p s hb E g * constantFiberGaloisEquiv p s hb E z := by
  unfold normalConstantQuotient
  exact fibreMultiplier_formula _ _ _ _ _ g z

private theorem normalConstantQuotient_continuous {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] :
    Continuous (normalConstantQuotient p s hb E) := by
  let : Fintype (E ≃ₐ[K] E) := AlgEquiv.fintype K E
  unfold normalConstantQuotient
  exact fibreMultiplier_continuous _ _ _ _ _

private theorem normalConstantQuotient_at_one {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Algebra E Ω] [IsScalarTower K E Ω] (g : Aut (fiber s))
    (z : (fiber s).obj (constantCover p (fieldConstantAlgebra K E)))
    (hz : (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val =
      algebraMap E Ω) :
    (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) (g.hom.app _ z)).val =
      (algebraMap E Ω).comp (normalConstantQuotient p s hb E g).toRingHom := by
  have he : constantFiberGaloisEquiv p s hb E z = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap E Ω).injective
    have h := DFunLike.congr_fun (constantFiberGaloisEquiv_label p s hb E z) x
    rw [hz] at h
    exact h.symm
  rw [constantFiberGaloisEquiv_label, normalConstantQuotient_formula, he, mul_one]

attribute [local irreducible] constantCoverHom

private theorem normalConstantQuotient_compatible {K Ω : Type u} [Field K]
    [PerfectField K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
    (hb : baseRingHom p s = algebraMap K Ω)
    (E E' : Type u) [Field E] [Algebra K E] [FiniteDimensional K E] [Normal K E]
    [Field E'] [Algebra K E'] [FiniteDimensional K E'] [Normal K E']
    [Algebra E Ω] [IsScalarTower K E Ω] [Algebra E' Ω] [IsScalarTower K E' Ω]
    (φ : E →ₐ[K] E')
    (hφ : (algebraMap E' Ω).comp φ.toRingHom = algebraMap E Ω)
    (g : Aut (fiber s)) :
    (algebraMap E Ω).comp (normalConstantQuotient p s hb E g).toRingHom =
      ((algebraMap E' Ω).comp (normalConstantQuotient p s hb E' g).toRingHom).comp
        φ.toRingHom := by
  let z' := (constantFiberGaloisEquiv p s hb E').symm 1
  have hz' : (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E') z').val =
      algebraMap E' Ω := by
    rw [constantFiberGaloisEquiv_label p s hb E' z', Equiv.apply_symm_apply]
    rfl
  let z := (fiber s).map (constantCoverHom p (A := fieldConstantAlgebra K E)
      (B := fieldConstantAlgebra K E') φ) z'
  have hz : (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) z).val =
      algebraMap E Ω :=
    (fiberConstantCoverEquiv_fiber_map p s
      (A := fieldConstantAlgebra K E) (B := fieldConstantAlgebra K E') φ z').trans
      ((congrArg (fun a : E' →+* Ω ↦ a.comp φ.toRingHom) hz').trans hφ)
  have hn := ConcreteCategory.congr_hom (g.hom.naturality
    (constantCoverHom p (A := fieldConstantAlgebra K E)
      (B := fieldConstantAlgebra K E') φ)) z'
  simp only [ConcreteCategory.comp_apply] at hn
  calc
    _ = (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) (g.hom.app _ z)).val :=
      (normalConstantQuotient_at_one p s hb E g z hz).symm
    _ = (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E)
        ((fiber s).map (constantCoverHom p (A := fieldConstantAlgebra K E)
          (B := fieldConstantAlgebra K E') φ) (g.hom.app _ z'))).val :=
      congrArg (fun w ↦ (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E) w).val) hn
    _ = (fiberConstantCoverEquiv p s (fieldConstantAlgebra K E')
        (g.hom.app _ z')).val.comp φ.toRingHom :=
      fiberConstantCoverEquiv_fiber_map p s
      (A := fieldConstantAlgebra K E) (B := fieldConstantAlgebra K E') φ (g.hom.app _ z')
    _ = _ := congrArg (fun a : E' →+* Ω ↦ a.comp φ.toRingHom)
      (normalConstantQuotient_at_one p s hb E' g z' hz')

section FiniteQuotients

variable {K L Ω : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
  [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (s : Spec (.of Ω) ⟶ X)
  (hb : baseRingHom p s = algebraMap K Ω)

private noncomputable def finiteConstantQuotient (N : FiniteGaloisIntermediateField K L) :
    Aut (fiber s) →* (N ≃ₐ[K] N) :=
  normalConstantQuotient p s hb N

private theorem finiteConstantQuotient_compatible
    (N M : FiniteGaloisIntermediateField K L) (h : N ≤ M) (g : Aut (fiber s)) :
    finGaloisGroupMap (CategoryTheory.homOfLE h).op (finiteConstantQuotient p s hb M g) =
      finiteConstantQuotient p s hb N g := by
  let : Algebra N M := RingHom.toAlgebra (Subsemiring.inclusion h)
  let : IsScalarTower K N M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have hc := normalConstantQuotient_compatible p s hb N M
    (IntermediateField.inclusion h) rfl g
  apply AlgEquiv.ext
  intro x
  apply (algebraMap N Ω).injective
  have hr := congrArg (algebraMap M Ω)
    ((normalConstantQuotient p s hb M g).restrictNormal_commutes N x)
  exact hr.trans (DFunLike.congr_fun hc x).symm

@[irreducible]
private noncomputable def constantQuotientLimit :
    Aut (fiber s) →* ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K L) where
  toFun g :=
    { val := fun N ↦ finiteConstantQuotient p s hb N.unop g
      property := fun {N M} f ↦
        finiteConstantQuotient_compatible p s hb M.unop N.unop (CategoryTheory.leOfHom f.unop) g }
  map_one' := by
    apply Subtype.ext
    funext N
    exact map_one (finiteConstantQuotient p s hb N.unop)
  map_mul' g h := by
    apply Subtype.ext
    funext N
    exact map_mul (finiteConstantQuotient p s hb N.unop) g h

private theorem constantQuotientLimit_continuous :
    Continuous (constantQuotientLimit (L := L) p s hb) := by
  unfold constantQuotientLimit
  apply Continuous.subtype_mk
  change @Continuous _ (∀ N : (FiniteGaloisIntermediateField K L)ᵒᵖ,
      N.unop ≃ₐ[K] N.unop) _ (@Pi.topologicalSpace _ _ (fun _ ↦ ⊥)) _
  apply continuous_pi (T := fun _ ↦ ⊥)
  intro N
  convert! normalConstantQuotient_continuous p s hb N.unop using 1
  exact (DiscreteTopology.eq_bot (α := N.unop ≃ₐ[K] N.unop)).symm

@[irreducible]
private noncomputable def constantQuotient [IsGalois K L] :
    Aut (fiber s) →* (L ≃ₐ[K] L) :=
  (InfiniteGalois.continuousMulEquivToLimit K L).symm.toMulEquiv.toMonoidHom.comp
    (constantQuotientLimit p s hb)

private theorem constantQuotient_continuous [IsGalois K L] :
    Continuous (constantQuotient (L := L) p s hb) := by
  unfold constantQuotient
  exact (InfiniteGalois.continuousMulEquivToLimit K L).symm.continuous.comp
    (constantQuotientLimit_continuous p s hb)

private theorem constantQuotient_restrict [IsGalois K L]
    (g : Aut (fiber s)) (N : FiniteGaloisIntermediateField K L) :
    (constantQuotient (L := L) p s hb g).restrictNormal N =
      finiteConstantQuotient p s hb N g := by
  have he := congrArg (fun a : ProfiniteGrp.limit
      (InfiniteGalois.asProfiniteGaloisGroupFunctor K L) ↦ a.val (Opposite.op N))
    ((InfiniteGalois.mulEquivToLimit K L).apply_symm_apply
      (constantQuotientLimit p s hb g))
  unfold constantQuotientLimit at he
  unfold constantQuotient constantQuotientLimit
  exact he

omit [PerfectField K] in
private theorem finiteEtaleAlgHom_factors [IsGalois K L]
    (A : FiniteEtaleAlgebra K) (τ : A.1 →ₐ[K] L) :
    ∃ (N : FiniteGaloisIntermediateField K L) (φ : A.1 →ₐ[K] N),
      N.toIntermediateField.val.comp φ = τ := by
  classical
  let b := Module.finBasis K A.1
  let N := FiniteGaloisIntermediateField.adjoin K (Set.range (fun j ↦ τ (b j)))
  have hτ : ∀ x : A.1, τ x ∈ N.toIntermediateField := by
    intro x
    have hx : τ x = ∑ j, (b.repr x j) • τ (b j) := by
      calc
        τ x = τ (∑ j, (b.repr x j) • b j) := congrArg τ (b.sum_repr x).symm
        _ = _ := by simp only [map_sum, map_smul]
    rw [hx]
    apply N.toIntermediateField.toSubmodule.sum_mem
    intro j _
    apply N.toIntermediateField.toSubmodule.smul_mem
    exact FiniteGaloisIntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  refine ⟨N, τ.codRestrict N.toIntermediateField.toSubalgebra hτ, ?_⟩
  rfl

end FiniteQuotients

/-- The constant-cover quotient of the arithmetic fundamental group is surjective,
and its kernel is the image of geometric base change.

Source: Stacks Project, Tags 0BTX (lemma-ses-field), 0BTV (lemma-limit), and
0BNE (lemma-fundamental-group-Galois-group).
(blueprint: lem-wf-arithmetic-exact-sequence)

Proof: Finite intermediate constant covers are connected since they are surjective
images of the connected algebraic-closure base change. On a finite Galois constant
cover, a natural automorphism commutes with the right deck action and therefore acts
by left multiplication. These multipliers commute with restriction; the Krull inverse
limit gives a unique Galois automorphism. Its action on every finite etale algebra is
postcomposition, by projecting to its finite separable field factors and extending
embeddings to finite Galois fields. Evaluation at finite covers proves continuity.
Transitivity on connected finite constant covers gives surjectivity at every finite
Galois quotient. Compactness of the arithmetic automorphism group then gives
surjectivity onto the inverse limit. At a finite intermediate field, the image of
base change is the stabilizer of its distinguished embedding. The fundamental-group
limit theorem identifies the intersection of these stabilizers with the image of the
algebraic-closure base change, proving the asserted kernel identity. -/
theorem arithmetic_exactSequence
    {K L : Type u} [Field K] [PerfectField K] [Field L] [Algebra K L]
    [IsAlgClosure K L] [Algebra.IsAlgebraic K L]
    (X₀ : Over (Spec (.of K))) [IsSeparated X₀.hom]
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [ConnectedSpace (fieldExtensionBase X₀ L)]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    (s : Spec (.of Ω) ⟶ fieldExtensionBase X₀ L)
    (i : L →ₐ[K] Ω)
    (hi : s ≫ Limits.pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom i.toRingHom)) :
    ∃ r : Aut (fiber (s ≫ Limits.pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))) →* (L ≃ₐ[K] L),
      Continuous r ∧ Function.Surjective r ∧
      Set.range (fiberAutBaseChange (Limits.pullback.fst X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) s) = {g | r g = 1} ∧
      ∀ (g : Aut (fiber (s ≫ Limits.pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K L))))))
        (A : FiniteEtaleAlgebra K) (τ : A.1 →ₐ[K] L)
        (z : (fiber (s ≫ Limits.pullback.fst X₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj (constantCover X₀.hom A)),
        (fiberConstantCoverEquiv X₀.hom _ A z).1 = i.toRingHom.comp τ.toRingHom →
        (fiberConstantCoverEquiv X₀.hom _ A (g.hom.app _ z)).1 =
          i.toRingHom.comp ((r g).toRingHom.comp τ.toRingHom) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
