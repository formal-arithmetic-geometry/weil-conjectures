/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.RepresentationTheory.ProfiniteStableLattice
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Exact.Basic
import Sheaf.Paper.LatticeNormalizationRationalExact

/-! # Exactness from functorial lattice normalization

Source: Bhatt--Scholze, Corollary 6.8.5.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem exists_invariant_lattice (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (V : SfContinuousRepresentations l E p) : Nonempty (SfInvariantLattice l E V) := by
  have : FiniteDimensional E V.obj.V := V.property.1
  obtain ⟨Λ, hfg, hspan, hfree, _, hstable, _, _⟩ :=
    Padic.exists_stable_lattice l E p.group V.obj.V
      (galoisRepLinearAction E V.obj) (by exact V.property.2)
  refine ⟨{
    submodule := Λ
    finite := Module.Finite.of_fg hfg
    free := hfree
    spans := ?_
    stable := ?_ }⟩
  · change Submodule.span E (Set.range (fun b : Λ ↦ (b.val : V.obj.V))) = ⊤
    rw [show Set.range (fun b : Λ ↦ (b.val : V.obj.V)) = (Λ : Set V.obj.V) from
      by ext x; simp]
    exact hspan
  · intro g b
    have hb := Set.mem_image_of_mem (galoisRepLinearAction E V.obj g) b.property
    rw [hstable] at hb
    exact hb

private theorem exists_nonzero_smul_mem
    {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup M] [Module R M] [Module K M]
    [IsScalarTower R K M] (P : Submodule R M)
    (hP : Submodule.span K (P : Set M) = ⊤) (x : M) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ P := by
  let := isLocalizedModule_id (nonZeroDivisors R) M K
  have hx : x ∈ P.localized' K (nonZeroDivisors R) (LinearMap.id : M →ₗ[R] M) := by
    rw [Submodule.localized'_eq_span]
    simpa using (hP ▸ (Submodule.mem_top : x ∈ (⊤ : Submodule K M)))
  obtain ⟨m, hm, s, h⟩ := hx
  refine ⟨s.val, nonZeroDivisors.ne_zero s.property, ?_⟩
  rw [← h]
  change s • IsLocalizedModule.mk' (LinearMap.id : M →ₗ[R] M) m s ∈ P
  simpa only [IsLocalizedModule.mk'_cancel', LinearMap.id_apply] using hm

private theorem comap_span_eq_top
    {R K M N : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup M] [Module R M] [Module K M]
    [IsScalarTower R K M] [AddCommGroup N] [Module R N] [Module K N]
    [IsScalarTower R K N] (P : Submodule R N)
    (hP : Submodule.span K (P : Set N) = ⊤) (f : M →ₗ[K] N) :
    Submodule.span K ((P.comap (f.restrictScalars R)) : Set M) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨r, hr, hx⟩ := exists_nonzero_smul_mem P hP (f x)
  have hx' : r • x ∈ P.comap (f.restrictScalars R) := by
    change f (r • x) ∈ P
    simpa only [LinearMap.map_smul_of_tower] using hx
  have hm := (Submodule.span K ((P.comap (f.restrictScalars R)) : Set M)).smul_mem
    ((algebraMap R K r)⁻¹) (Submodule.subset_span hx')
  have hr' : algebraMap R K r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr
  simpa only [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul] using hm

private theorem map_span_eq_top
    {R K M N : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower R K M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N]
    (P : Submodule R M) (hP : Submodule.span K (P : Set M) = ⊤)
    (f : M →ₗ[K] N) (hf : Function.Surjective f) :
    Submodule.span K ((P.map (f.restrictScalars R)) : Set N) = ⊤ := by
  have hset : (P.map (f.restrictScalars R) : Set N) = f '' (P : Set M) := rfl
  rw [hset, ← Submodule.map_span, hP, Submodule.map_top, LinearMap.range_eq_top.mpr hf]

private theorem invariant_lattice_comap (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    {V W : SfContinuousRepresentations l E p} (f : V ⟶ W)
    (hf : Function.Injective f.hom.hom) (B : SfInvariantLattice l E W) :
    ∃ C : SfInvariantLattice l E V,
      C.submodule = B.submodule.comap (f.hom.hom.restrictScalars
        (Padic.coefficientExtensionIntegers l E)) := by
  let O := Padic.coefficientExtensionIntegers l E
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsFractionRing O E := h.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := h.2.2.2.2.2.2.2.2.1
  have := B.finite
  let C := B.submodule.comap (f.hom.hom.restrictScalars O)
  let fC : C →ₗ[O] B.submodule :=
    { toFun x := ⟨f.hom.hom x.val, x.property⟩
      map_add' x y := by ext; exact map_add f.hom.hom x.val y.val
      map_smul' r x := by ext; exact f.hom.hom.map_smul_of_tower r x.val }
  have : Module.Finite O C := Module.Finite.of_injective fC (by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy)))
  have : Module.IsTorsionFree O V.obj.V := Module.IsTorsionFree.comap
    (algebraMap O E) (fun r hr ↦ IsRegular.of_ne_zero (by
      simpa only [map_zero] using (IsFractionRing.injective O E).ne
        (isRegular_iff_ne_zero.mp hr))) (fun _ _ ↦ rfl)
  have : Module.Free O C := inferInstance
  refine ⟨{
    submodule := C
    finite := by change Module.Finite O C; infer_instance
    free := by change Module.Free O C; infer_instance
    spans := ?_
    stable := ?_ }, rfl⟩
  · change Submodule.span E (Set.range (fun b : C ↦ (b.val : V.obj.V))) = ⊤
    rw [show Set.range (fun b : C ↦ (b.val : V.obj.V)) = (C : Set V.obj.V) from
      by ext x; simp]
    let P : Submodule O W.obj.V := by exact B.submodule
    have hB' : Submodule.span E (P : Set W.obj.V) = ⊤ := by
      rw [show (P : Set W.obj.V) =
        Set.range (fun b : B.submodule ↦ (b.val : W.obj.V)) from by ext x; simp [P]]
      exact B.spans
    exact comap_span_eq_top (R := O) (K := E) P hB' f.hom.hom.toLinearMap
  · intro g b
    change f.hom.hom (V.obj.ρ g b.val) ∈ B.submodule
    rw [f.hom.hom.isIntertwining]
    exact B.stable g ⟨f.hom.hom b.val, b.property⟩

private theorem invariant_lattice_map (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    {W Z : SfContinuousRepresentations l E p} (g : W ⟶ Z)
    (hg : Function.Surjective g.hom.hom) (B : SfInvariantLattice l E W) :
    ∃ D : SfInvariantLattice l E Z,
      D.submodule = B.submodule.map (g.hom.hom.restrictScalars
        (Padic.coefficientExtensionIntegers l E)) := by
  let O := Padic.coefficientExtensionIntegers l E
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsFractionRing O E := h.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := h.2.2.2.2.2.2.2.2.1
  have := B.finite
  let D := B.submodule.map (g.hom.hom.restrictScalars O)
  have : Module.Finite O D := Module.Finite.of_fg
    ((Module.Finite.iff_fg.mp B.finite).map (g.hom.hom.restrictScalars O))
  have : Module.IsTorsionFree O Z.obj.V := Module.IsTorsionFree.comap
    (algebraMap O E) (fun r hr ↦ IsRegular.of_ne_zero (by
      simpa only [map_zero] using (IsFractionRing.injective O E).ne
        (isRegular_iff_ne_zero.mp hr))) (fun _ _ ↦ rfl)
  have : Module.Free O D := inferInstance
  refine ⟨{
    submodule := D
    finite := by change Module.Finite O D; infer_instance
    free := by change Module.Free O D; infer_instance
    spans := ?_
    stable := ?_ }, rfl⟩
  · change Submodule.span E (Set.range (fun b : D ↦ (b.val : Z.obj.V))) = ⊤
    rw [show Set.range (fun b : D ↦ (b.val : Z.obj.V)) = (D : Set Z.obj.V) from
      by ext x; simp]
    let P : Submodule O W.obj.V := by exact B.submodule
    have hB' : Submodule.span E (P : Set W.obj.V) = ⊤ := by
      rw [show (P : Set W.obj.V) =
        Set.range (fun b : B.submodule ↦ (b.val : W.obj.V)) from by ext x; simp [P]]
      exact B.spans
    exact map_span_eq_top (R := O) (K := E) P hB' g.hom.hom.toLinearMap hg
  · intro a z
    obtain ⟨w, hw, heq⟩ := z.property
    change Z.obj.ρ a z.val ∈ D
    rw [← heq]
    refine ⟨W.obj.ρ a w, B.stable a ⟨w, hw⟩, ?_⟩
    exact LinearMap.congr_fun (g.hom.hom.isIntertwining' a) w

private theorem exists_compatible_invariant_lattices (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {T : Scheme.{u}} (p : SfMonodromyPoint T)
    {V W Z : SfContinuousRepresentations l E p} (f : V ⟶ W) (g : W ⟶ Z)
    (hf : Function.Injective f.hom.hom) (he : Function.Exact f.hom.hom g.hom.hom)
    (hg : Function.Surjective g.hom.hom) :
    ∃ (C : SfInvariantLattice l E V) (B : SfInvariantLattice l E W)
      (D : SfInvariantLattice l E Z),
      (∀ a : C.submodule, f.hom.hom a.val ∈ B.submodule) ∧
      (∀ b : B.submodule, g.hom.hom b.val ∈ D.submodule) ∧
      (∀ b : B.submodule, g.hom.hom b.val = 0 ↔
        ∃ a : C.submodule, f.hom.hom a.val = b.val) ∧
      (∀ d : D.submodule, ∃ b : B.submodule, g.hom.hom b.val = d.val) := by
  obtain ⟨B⟩ := exists_invariant_lattice l E p W
  obtain ⟨C, hC⟩ := invariant_lattice_comap l E p f hf B
  obtain ⟨D, hD⟩ := invariant_lattice_map l E p g hg B
  refine ⟨C, B, D, ?_, ?_, ?_, ?_⟩
  · intro a
    have ha := a.property
    have ha' := Eq.mp (congrArg (fun P ↦ a.val ∈ P) hC) ha
    exact ha'
  · intro b
    rw [hD]
    exact ⟨b.val, b.property, rfl⟩
  · intro b
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (he b.val).mp hb
      have hCa : a ∈ C.submodule := by
        rw [hC]
        change f.hom.hom a ∈ B.submodule
        rw [ha]
        exact b.property
      exact ⟨⟨a, hCa⟩, ha⟩
    · rintro ⟨a, ha⟩
      exact (he b.val).mpr ⟨a.val, ha⟩
  · intro d
    have hd := d.property
    have hd' := Eq.mp (congrArg (fun P ↦ d.val ∈ P) hD) hd
    obtain ⟨b, hb, heq⟩ := hd'
    exact ⟨⟨b, hb⟩, heq⟩


private theorem quotient_split_exact {R : Type u} [CommRing R]
    {A B C : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (I : Ideal R) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (r : B →ₗ[R] A) (s : C →ₗ[R] B)
    (hr : ∀ a, r (f a) = a) (hs : ∀ c, g (s c) = c)
    (hid : ∀ b, f (r b) + s (g b) = b)
    (hfg : ∀ a, g (f a) = 0) :
    ∃ (f' : (A ⧸ (I • ⊤ : Submodule R A)) →ₗ[R]
        (B ⧸ (I • ⊤ : Submodule R B)))
      (g' : (B ⧸ (I • ⊤ : Submodule R B)) →ₗ[R]
        (C ⧸ (I • ⊤ : Submodule R C))),
      (∀ a, f' (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a)) ∧
      (∀ b, g' (Submodule.Quotient.mk b) = Submodule.Quotient.mk (g b)) ∧
      Function.Injective f' ∧ Function.Exact f' g' ∧ Function.Surjective g' := by
  let f' := Submodule.mapQ (I • ⊤) (I • ⊤) f
    (Submodule.smul_top_le_comap_smul_top I f)
  let g' := Submodule.mapQ (I • ⊤) (I • ⊤) g
    (Submodule.smul_top_le_comap_smul_top I g)
  let r' := Submodule.mapQ (I • ⊤) (I • ⊤) r
    (Submodule.smul_top_le_comap_smul_top I r)
  let s' := Submodule.mapQ (I • ⊤) (I • ⊤) s
    (Submodule.smul_top_le_comap_smul_top I s)
  have hr' : Function.LeftInverse r' f' := by
    intro a
    induction a using Submodule.Quotient.induction_on with
    | _ a => change Submodule.Quotient.mk (r (f a)) = _; rw [hr]
  have hs' : Function.RightInverse s' g' := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | _ c => change Submodule.Quotient.mk (g (s c)) = _; rw [hs]
  have hid' : ∀ b, f' (r' b) + s' (g' b) = b := by
    intro b
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      change Submodule.Quotient.mk (f (r b)) + Submodule.Quotient.mk (s (g b)) = _
      rw [← Submodule.Quotient.mk_add, hid]
  have hfg' : ∀ a, g' (f' a) = 0 := by
    intro a
    induction a using Submodule.Quotient.induction_on with
    | _ a => change Submodule.Quotient.mk (g (f a)) = 0; rw [hfg]; rfl
  refine ⟨f', g', (fun _ ↦ rfl), (fun _ ↦ rfl), hr'.injective, ?_, hs'.surjective⟩
  intro b
  constructor
  · intro hb
    refine ⟨r' b, ?_⟩
    simpa only [hb, map_zero, add_zero] using hid' b
  · rintro ⟨a, rfl⟩
    exact hfg' a

/-- Any additive realization with functorial inverse-limit lattice normalization is
exact in the ambient rational module-sheaf category.
Source: Bhatt--Scholze, proof of Corollary 6.8.5, pp. 59--60.
(blueprint: lem-sfb-normalized-monodromy-exact)

Proof: in a short exact sequence of rational representations choose a stable lattice B in
the middle. Its intersection with the kernel and its image in the quotient are stable,
finite torsion-free modules over the coefficient DVR, hence free; they span the kernel and
quotient by clearing denominators. Their subspace topologies give continuous actions.
The resulting exact sequence of lattices splits as integral modules by lifting a basis of
the quotient, so reduction modulo every positive uniformizer power is exact. Finite
monodromy and the exact comparison inverse image give compatible exact sequences of
pro-etale finite-coefficient sheaves, with epic transitions on the kernels. Products are
exact. The Milnor 1-shift map on the product of the kernel tower is epic. Locally lift a
compatible quotient section to the product of the middle terms; its compatibility defect
lies in the product of kernels. Locally solve that defect by the Milnor epimorphism and
subtract the solution. Thus the inverse-limit quotient map is epic; sectionwise kernels
give left exactness. Localization by l is an exact filtered colimit. The normalizations
and their naturality identify this exact sequence with the image of the original rational
sequence. Additivity and functoriality identify its zero composite. -/
theorem sf_normalized_monodromy_exact (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (J : SfContinuousRepresentations l E p ⥤ SfRationalModules l E T)
    (hJ : J.Additive)
    (N : ∀ (V : SfContinuousRepresentations l E p) (B : SfInvariantLattice l E V),
      SfLatticeNormalization l E p c J V B)
    (hN : ∀ (V W : SfContinuousRepresentations l E p) (f : V ⟶ W)
      (B : SfInvariantLattice l E V) (C : SfInvariantLattice l E W)
      (h : ∀ b : B.submodule, f.hom.hom b.val ∈ C.submodule),
      Nonempty (SfNormalizationMap l E f B C h (N V B) (N W C)))
    (V W Z : SfContinuousRepresentations l E p) (f : V ⟶ W) (g : W ⟶ Z) :
    Function.Injective f.hom.hom → Function.Exact f.hom.hom g.hom.hom →
      Function.Surjective g.hom.hom →
        ∃ w : J.map f ≫ J.map g = 0,
          (ShortComplex.mk (J.map f) (J.map g) w).ShortExact := by
  intro hf he hg
  obtain ⟨C, B, D, hCB, hBD, hker, hsurj⟩ :=
    exists_compatible_invariant_lattices l E p f g hf he hg
  obtain ⟨F⟩ := hN V W f C B hCB
  obtain ⟨G⟩ := hN W Z g B D hBD
  let O := Padic.coefficientExtensionIntegers l E
  let f₀ : C.submodule →ₗ[O] B.submodule :=
    ((f.hom.hom.restrictScalars O).domRestrict C.submodule).codRestrict B.submodule hCB
  let g₀ : B.submodule →ₗ[O] D.submodule :=
    ((g.hom.hom.restrictScalars O).domRestrict B.submodule).codRestrict D.submodule hBD
  have hf₀ : Function.Injective f₀ := by
    intro a a' h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  have he₀ : Function.Exact f₀ g₀ := by
    intro b
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (hker b).mp (congrArg Subtype.val hb)
      exact ⟨a, Subtype.ext ha⟩
    · rintro ⟨a, ha⟩
      apply Subtype.ext
      exact (hker b).mpr ⟨a, congrArg Subtype.val ha⟩
  have hg₀ : Function.Surjective g₀ := by
    intro d
    obtain ⟨b, hb⟩ := hsurj d
    exact ⟨b, Subtype.ext hb⟩
  have w₀ : g₀.comp f₀ = 0 := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact (hker (f₀ a)).mpr ⟨a, rfl⟩
  let S₀ := ShortComplex.moduleCatMk f₀ g₀ w₀
  have heS : S₀.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S₀).mpr he₀
  have : Module.Free O D.submodule := D.free
  obtain ⟨s₀, hs₀⟩ :=
    g₀.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg₀)
  have hfS : Mono S₀.f := (ModuleCat.mono_iff_injective _).mpr hf₀
  let split := ShortComplex.Splitting.ofExactOfSection S₀ heS (ModuleCat.ofHom s₀)
    (ModuleCat.hom_ext hs₀) hfS
  let r₀ : B.submodule →ₗ[O] C.submodule := split.r.hom
  let s₁ : D.submodule →ₗ[O] B.submodule := split.s.hom
  have hr : ∀ a : C.submodule, r₀ (f₀ a) = a :=
    fun a ↦ congrArg (fun k ↦ k a) split.f_r
  have hs : ∀ d : D.submodule, g₀ (s₁ d) = d :=
    fun d ↦ congrArg (fun k ↦ k d) split.s_g
  have hid : ∀ b : B.submodule, f₀ (r₀ b) + s₁ (g₀ b) = b :=
    fun b ↦ congrArg (fun k ↦ k b) split.id
  have hfg₀ : ∀ a : C.submodule, g₀ (f₀ a) = 0 :=
    fun a ↦ congrArg (fun k : C.submodule →ₗ[O] D.submodule ↦ k a) w₀
  have Hq := fun n : ℕ ↦ quotient_split_exact
    (Padic.coefficientExtensionIdeal l E (n + 1)) f₀ g₀
      r₀ s₁ hr hs hid hfg₀
  choose qf qg hqf hqg hiq heq hsq using Hq
  obtain ⟨w, hw⟩ := sf_lattice_normalization_rational_exact l E p c J
    f g C B D hCB hBD (N V C) (N W B) (N Z D) F G
      qf qg hqf hqg (fun n ↦ ⟨hiq n, heq n, hsq n⟩)
  let a := SheafOfModules.changeOfRingsHom
    (ProEtale.lisseIntegerToFieldSized l E T) (N V C).integral F.integral
  let b := SheafOfModules.changeOfRingsHom
    (ProEtale.lisseIntegerToFieldSized l E T) (N W B).integral G.integral
  have : J.Additive := hJ
  have hfg : f ≫ g = 0 := by
    ext x
    exact (he (f.hom.hom x)).mpr ⟨x, rfl⟩
  have hj : J.map f ≫ J.map g = 0 := by
    rw [← J.map_comp, hfg, J.map_zero]
  let e : ShortComplex.mk (J.map f) (J.map g) hj ≅ ShortComplex.mk a b w :=
    ShortComplex.isoMk (N V C).rational (N W B).rational (N Z D).rational
      F.rational_comm.symm G.rational_comm.symm
  exact ⟨hj, (ShortComplex.shortExact_iff_of_iso e).mpr hw⟩

end AlgebraicGeometry.Scheme
