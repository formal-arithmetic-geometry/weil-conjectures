/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import WeilConjectures.CategoryTheory.FiniteFilteredGradedExactness
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero

/-!
# The preservation subgroups of the filtered Hom complex

Source: Varshavsky §5.1.5, the filtration on the Hom complex before localization
(blueprint: lem-trf-filtered-hom-preservation-subcomplex).
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.FiniteFiltered

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The degree-n cochains carrying every filtration step into its r-shifted step.
The subgroup is defined by the factorization property itself, without choosing lifts.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
def preservationCochains (K I : FilteredObject (CochainComplex A ℤ)) (r n : ℤ) :
    AddSubgroup (HomComplex.Cochain K.obj I.obj n) where
  carrier x := ∀ (a p q : ℤ) (hpq : p + n = q),
    ∃ lift : (K.filtration.F a : CochainComplex A ℤ).X p ⟶
      (I.filtration.F (a + r) : CochainComplex A ℤ).X q,
      lift ≫ (I.filtration.F (a + r)).arrow.f q =
        (K.filtration.F a).arrow.f p ≫ x.v p q hpq
  zero_mem' := by
    intro a p q hpq
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy a p q hpq
    obtain ⟨f, hf⟩ := hx a p q hpq
    obtain ⟨g, hg⟩ := hy a p q hpq
    exact ⟨f + g, by simp only [Preadditive.add_comp, hf, hg,
      HomComplex.Cochain.add_v, Preadditive.comp_add]⟩
  neg_mem' := by
    intro x hx a p q hpq
    obtain ⟨f, hf⟩ := hx a p q hpq
    exact ⟨-f, by simp only [Preadditive.neg_comp, hf,
      HomComplex.Cochain.neg_v, Preadditive.comp_neg]⟩

/-- The Hom differential preserves the shift of the filtration.
Source: Varshavsky §5.1.5.
Proof: expand d(x) as x d plus the signed d x term. Lift the first term using
preservation by x followed by the differential of the target filtration step;
lift the second using the differential of the source step followed by preservation
by x. The chain-map equations for the two step inclusions prove that their signed
sum is a lift of d(x). Nonadjacent differentials are zero.
(blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
theorem differential_mem_preservationCochains
    (K I : FilteredObject (CochainComplex A ℤ)) (r n m : ℤ)
    (x : HomComplex.Cochain K.obj I.obj n) (hx : x ∈ preservationCochains K I r n) :
    HomComplex.δ n m x ∈ preservationCochains K I r m := by
  by_cases hnm : n + 1 = m
  · intro a p q hpq
    obtain ⟨f, hf⟩ := hx a p (q - 1) (by omega)
    obtain ⟨g, hg⟩ := hx a (p + 1) q (by omega)
    refine ⟨f ≫ (I.filtration.F (a + r) : CochainComplex A ℤ).d (q - 1) q +
      m.negOnePow • (K.filtration.F a : CochainComplex A ℤ).d p (p + 1) ≫ g, ?_⟩
    rw [HomComplex.δ_v n m hnm x p q hpq (q - 1) (p + 1) rfl rfl]
    simp only [Preadditive.add_comp, Preadditive.comp_add,
      Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    rw [← (I.filtration.F (a + r)).arrow.comm (q - 1) q,
      ← Category.assoc, hf, Category.assoc, hg]
    congr 1
    rw [← Category.assoc, ← (K.filtration.F a).arrow.comm p (p + 1)]
    simp only [Category.assoc]
  · rw [HomComplex.δ_shape n m hnm]
    exact (preservationCochains K I r m).zero_mem

/-- The preservation subgroups form an actual cochain complex.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
def preservationComplex (K I : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    CochainComplex AddCommGrpCat.{v} ℤ where
  X n := AddCommGrpCat.of (preservationCochains K I r n)
  d n m := AddCommGrpCat.ofHom
    { toFun x := ⟨HomComplex.δ n m x.1,
        differential_mem_preservationCochains K I r n m x.1 x.2⟩
      map_zero' := by
        apply Subtype.ext
        exact (HomComplex.δ_hom ℤ K.obj I.obj n m).map_zero
      map_add' x y := by
        apply Subtype.ext
        exact (HomComplex.δ_hom ℤ K.obj I.obj n m).map_add x.1 y.1 }
  shape n m hnm := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    exact HomComplex.δ_shape n m hnm x.1
  d_comp_d' n m k _ _ := by
    apply AddCommGrpCat.ext
    intro x
    apply Subtype.ext
    exact HomComplex.δ_δ n m k x.1

/-- The inclusion of the preservation subcomplex into the ordinary Hom complex.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
def preservationComplexι (K I : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    preservationComplex K I r ⟶ HomComplex K.obj I.obj where
  f n := AddCommGrpCat.ofHom (preservationCochains K I r n).subtype
  comm' _ _ _ := rfl

instance preservationComplexι_mono (K I : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    Mono (preservationComplexι K I r) :=
  HomologicalComplex.mono_of_mono_f _ (fun _n ↦
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective)

/-- Increasing the preservation shift makes the subgroup smaller.
Source: Varshavsky §5.1.5. Proof: compose each lift with the inclusion of the
successive target filtration steps; its defining factorization gives the claim.
(blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
theorem preservationCochains_succ_le (K I : FilteredObject (CochainComplex A ℤ))
    (r n : ℤ) : preservationCochains K I (r + 1) n ≤ preservationCochains K I r n := by
  intro x hx a p q hpq
  obtain ⟨f, hf⟩ := hx a p q hpq
  have hle : I.filtration.F (a + (r + 1)) ≤ I.filtration.F (a + r) :=
    I.filtration.antitone (by omega)
  refine ⟨f ≫ (Subobject.ofLE _ _ hle).f q, ?_⟩
  rw [Category.assoc, ← HomologicalComplex.comp_f,
    Subobject.ofLE_arrow hle, hf]

/-- The inclusion between successive preservation subcomplexes.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
def preservationComplexStep (K I : FilteredObject (CochainComplex A ℤ)) (r : ℤ) :
    preservationComplex K I (r + 1) ⟶ preservationComplex K I r where
  f n := AddCommGrpCat.ofHom
    { toFun x := ⟨x.1, preservationCochains_succ_le K I r n x.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  comm' _ _ _ := rfl

/-- The decreasing preservation filtration, constructed from concrete subcomplexes.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
noncomputable def preservationFiltration
    (K I : FilteredObject (CochainComplex A ℤ)) :
    DecreasingFiltration (HomComplex K.obj I.obj) where
  F r := Subobject.mk (preservationComplexι K I r)
  F_succ_le r := by
    apply Subobject.mk_le_mk_of_comm (preservationComplexStep K I r)
    ext n
    rfl

/-- Explicit lower support bound of the preservation filtration.
Source: Varshavsky §5.1.5. Proof: if a source step is already zero there is nothing
to lift. Otherwise its index is below the upper source filtration bound, so after
the displayed shift the target step is the whole complex and its inclusion is
invertible. This gives a lift for every cochain, in every degree.
(blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
theorem preservationCochains_eq_top
    (K I : FilteredObject (CochainComplex A ℤ)) (b c n : ℤ)
    (hb : K.filtration.F b = ⊥) (hc : I.filtration.F c = ⊤) :
    preservationCochains K I (c - b) n = ⊤ := by
  apply top_unique
  intro x _ a p q hpq
  by_cases ha : b ≤ a
  · have hz : K.filtration.F a = ⊥ := by
      apply le_antisymm _ bot_le
      rw [← hb]
      exact K.filtration.antitone ha
    refine ⟨0, ?_⟩
    rw [hz, Subobject.bot_arrow]
    simp
  · have ht : I.filtration.F (a + (c - b)) = ⊤ := by
      apply top_unique
      rw [← hc]
      exact I.filtration.antitone (by omega)
    have : IsIso (I.filtration.F (a + (c - b))).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2 ht
    refine ⟨(K.filtration.F a).arrow.f p ≫ x.v p q hpq ≫
      inv ((I.filtration.F (a + (c - b))).arrow.f q), ?_⟩
    simp

/-- Explicit upper support bound of the preservation filtration.
Source: Varshavsky §5.1.5. Proof: test preservation at a source step equal to the
whole complex. The shifted target step is zero. Thus every component of the
cochain vanishes after the invertible source inclusion and hence vanishes.
(blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
theorem preservationCochains_eq_bot
    (K I : FilteredObject (CochainComplex A ℤ)) (a e n : ℤ)
    (ha : K.filtration.F a = ⊤) (he : I.filtration.F e = ⊥) :
    preservationCochains K I (e - a) n = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply HomComplex.Cochain.ext
  intro p q hpq
  obtain ⟨f, hf⟩ := hx a p q hpq
  have hz : I.filtration.F (a + (e - a)) = ⊥ := by
    simpa only [add_sub_cancel] using he
  have hzero : (I.filtration.F (a + (e - a))).arrow = 0 := by
    apply Subobject.mk_eq_bot_iff_zero.mp
    simpa only [Subobject.mk_arrow] using hz
  simp only [hzero, HomologicalComplex.zero_f, comp_zero] at hf
  have : IsIso (K.filtration.F a).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 ha
  apply (cancel_epi ((K.filtration.F a).arrow.f p)).1
  simpa using hf.symm

/-- Finite input filtrations give a uniformly finite preservation filtration.
Source: Varshavsky §5.1.5. Proof: use the explicit whole and zero subgroup bounds.
The whole-bound subtype inclusion is degreewise bijective, hence an isomorphism
of complexes. At the zero bound the subtype inclusion is the zero chain map.
The corresponding subobjects are top and bottom.
(blueprint: lem-trf-filtered-hom-preservation-subcomplex). -/
theorem preservationFiltration_finite (K I : FilteredObject (CochainComplex A ℤ))
    (hK : K.filtration.IsFinite) (hI : I.filtration.IsFinite) :
    (preservationFiltration K I).IsFinite := by
  obtain ⟨a, b, ha, hb⟩ := hK
  obtain ⟨c, e, hc, he⟩ := hI
  refine ⟨c - b, e - a, ?_, ?_⟩
  · have hcomp (n : ℤ) : IsIso ((preservationComplexι K I (c - b)).f n) := by
      have : Epi ((preservationComplexι K I (c - b)).f n) := by
        apply (AddCommGrpCat.epi_iff_surjective _).2
        intro x
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [preservationCochains_eq_top K I b c n hb hc]
        trivial
      exact isIso_of_mono_of_epi _
    have : IsIso (preservationComplexι K I (c - b)) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact Subobject.mk_eq_top_of_isIso _
  · apply Subobject.mk_eq_bot_iff_zero.2
    ext n x
    exact (preservationCochains_eq_bot K I a e n ha he).le x.2

end CochainComplex.FiniteFiltered
