-- Q80 stage-2 revalidation of the landed C3 repair.
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Algebra.Homology.FilteredDerivedHomCalculusUniverse
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exact-adjunction comparison for filtered derived global Hom

Source: Varshavsky, §§5.1.1–5.1.2 and §5.1.5
(blueprint: lem-trf-filtered-global-hom-exact-adjunction).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CochainComplex.FiniteFiltered

variable {A : Type u₁} {B : Type u₂}
variable [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]
variable (L : A ⥤ B) [L.Additive]
variable [hLlim : PreservesFiniteLimits L] [hLcolim : PreservesFiniteColimits L]

set_option linter.unusedSectionVars false in
/-- Images of the termwise images of filtration steps decrease.
Source: Varshavsky, §5.1.1, exact functors on filtered objects.
Proof: map the inclusion of two successive steps and its factorization, then use
monotonicity of image subobjects.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_antitone (K : FilteredObject (CochainComplex A ℤ)) :
    Antitone (fun p : ℤ ↦ imageSubobject
      ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)) := by
  intro p q hpq
  let F := L.mapHomologicalComplex (.up ℤ)
  have h := K.filtration.antitone hpq
  have hw := F.congr_map (Subobject.ofLE_arrow h)
  rw [F.map_comp] at hw
  change imageSubobject (F.map (K.filtration.F q).arrow) ≤
    imageSubobject (F.map (K.filtration.F p).arrow)
  rw [← hw]
  exact imageSubobject_comp_le _ _

/-- Termwise L with the filtration by the images of L of the step inclusions.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredObject (K : FilteredObject (CochainComplex A ℤ)) :
    FilteredObject (CochainComplex B ℤ) where
  obj := (L.mapHomologicalComplex (.up ℤ)).obj K.obj
  filtration :=
    { F := fun p ↦ imageSubobject
        ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow)
      F_succ_le := fun p ↦ exactFiltered_antitone L K (by omega) }

/-- Termwise exact application preserves finite filtration and cochain bounds.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: L sends the whole step to the whole image and the zero step to zero.
Additivity preserves zero terms, hence the same cochain degree bounds.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_bounds (bounded : Bool) (K : Complex A bounded) :
    (exactFilteredObject L K.obj).filtration.IsFinite ∧
      DegreeBound B bounded (exactFilteredObject L K.obj).obj := by
  constructor
  · obtain ⟨a, b, ha, hb⟩ := K.property.1
    refine ⟨a, b, ?_, ?_⟩
    · change imageSubobject
        ((L.mapHomologicalComplex (.up ℤ)).map (K.obj.filtration.step a).arrow) = ⊤
      have : IsIso (K.obj.filtration.step a).arrow :=
        (Subobject.isIso_arrow_iff_eq_top _).2 ha
      rw [imageSubobject_mono]
      exact Subobject.mk_eq_top_of_isIso _
    · change imageSubobject
        ((L.mapHomologicalComplex (.up ℤ)).map (K.obj.filtration.step b).arrow) = ⊥
      have hz : (K.obj.filtration.step b).arrow = 0 := by
        change (K.obj.filtration.F b).arrow = 0
        rw [hb, Subobject.bot_arrow]
      rw [hz, Functor.map_zero, imageSubobject_zero]
  · obtain ⟨⟨a, ha⟩, hb⟩ := K.property.2
    refine ⟨⟨a, fun n hn ↦ L.map_isZero (ha n hn)⟩, ?_⟩
    rcases hb with hb | ⟨b, hb⟩
    · exact Or.inl hb
    · exact Or.inr ⟨b, fun n hn ↦ L.map_isZero (hb n hn)⟩

/-- Applying L to a filtered map preserves the image filtration.
Source: Varshavsky, §5.1.1.
Proof: map the restriction square of the original filtered map and descend through
its image factorizations. The resulting factorization is unique by monicity.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_preserves (bounded : Bool) {K M : Complex A bounded} (f : K ⟶ M) :
    ∀ p : ℤ, ∃ l : ((exactFilteredObject L K.obj).filtration.step p : CochainComplex B ℤ) ⟶
      ((exactFilteredObject L M.obj).filtration.step p : CochainComplex B ℤ),
      l ≫ ((exactFilteredObject L M.obj).filtration.step p).arrow =
        ((exactFilteredObject L K.obj).filtration.step p).arrow ≫
          (L.mapHomologicalComplex (.up ℤ)).map f.hom.hom := by
  intro p
  obtain ⟨l, hl⟩ := f.hom.preserves p
  let F := L.mapHomologicalComplex (.up ℤ)
  let sq : Arrow.mk (F.map (K.obj.filtration.step p).arrow) ⟶
      Arrow.mk (F.map (M.obj.filtration.step p).arrow) :=
    Arrow.homMk (F.map l) (F.map f.hom.hom) (by
      exact (F.map_comp _ _).symm.trans ((F.congr_map hl).trans (F.map_comp _ _)))
  exact ⟨imageSubobjectMap sq, imageSubobjectMap_arrow sq⟩

/-- The actual termwise functor on uniformly finite filtered complexes.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredComplex (bounded : Bool) :
    Complex A bounded ⥤ Complex B bounded where
  obj K := ⟨exactFilteredObject L K.obj, exactFiltered_bounds L bounded K⟩
  map f := ⟨⟨(L.mapHomologicalComplex (.up ℤ)).map f.hom.hom,
    exactFiltered_preserves L bounded f⟩⟩
  map_id K := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ =
      FilteredObject.Hom.mk _ _
    congr 1
    exact (L.mapHomologicalComplex (.up ℤ)).map_id K.obj.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change FilteredObject.Hom.mk _ _ =
      FilteredObject.Hom.mk _ _
    congr 1
    exact (L.mapHomologicalComplex (.up ℤ)).map_comp f.hom.hom g.hom.hom

include hLlim hLcolim in
/-- Exactness gives the canonical graded quotient comparison, uniquely characterized
by the quotient projection square.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: L preserves the monic inclusions and their cokernels. Identify their sources
with their image subobjects and descend the mapped quotient projection. The descended
map is invertible by preservation of cokernels; the epimorphic projection gives uniqueness.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_graded_iso (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    ∃! e : (exactFilteredObject L K).filtration.gradedPiece p ≅
        (L.mapHomologicalComplex (.up ℤ)).obj (K.filtration.gradedPiece p),
      (L.mapHomologicalComplex (.up ℤ)).map
          (K.filtration.complexQuotientπ p (p + 1) (by omega)) ≫ e.inv =
        factorThruImageSubobject
            ((L.mapHomologicalComplex (.up ℤ)).map (K.filtration.step p).arrow) ≫
          (exactFilteredObject L K).filtration.complexQuotientπ p (p + 1) (by omega) := by
  let F := L.mapHomologicalComplex (.up ℤ)
  let t (q : ℤ) := factorThruImageSubobject (F.map (K.filtration.step q).arrow)
  have ht (q : ℤ) : IsIso (t q) := by
    have : Mono (t q) := mono_of_mono_fac
      (imageSubobject_arrow_comp (F.map (K.filtration.step q).arrow))
    exact isIso_of_mono_of_epi _
  let i := Subobject.ofLE (K.filtration.step (p + 1)) (K.filtration.step p)
    (K.filtration.antitone_step (by omega))
  let j := Subobject.ofLE ((exactFilteredObject L K).filtration.step (p + 1))
    ((exactFilteredObject L K).filtration.step p)
    ((exactFilteredObject L K).filtration.antitone_step (by omega))
  have hw : F.map i ≫ t p = t (p + 1) ≫ j := by
    apply (cancel_mono ((exactFilteredObject L K).filtration.step p).arrow).1
    simp only [Category.assoc]
    change F.map i ≫ (t p ≫ (imageSubobject (F.map (K.filtration.step p).arrow)).arrow) = _
    rw [imageSubobject_arrow_comp, ← F.map_comp, Subobject.ofLE_arrow]
    dsimp only [j]
    rw [Subobject.ofLE_arrow]
    exact (imageSubobject_arrow_comp (F.map (K.filtration.step (p + 1)).arrow)).symm
  let e : (exactFilteredObject L K).filtration.gradedPiece p ≅
      F.obj (K.filtration.gradedPiece p) :=
    ((PreservesCokernel.iso F i) ≪≫
      (cokernel.mapIso (F.map i) j (asIso (t (p + 1))) (asIso (t p)) hw)).symm
  have he : F.map (K.filtration.complexQuotientπ p (p + 1) (by omega)) ≫ e.inv =
      t p ≫ (exactFilteredObject L K).filtration.complexQuotientπ p (p + 1)
        (by omega) := by
    change F.map (cokernel.π i) ≫
      ((PreservesCokernel.iso F i).hom ≫ (cokernel.mapIso (F.map i) j _ _ hw).hom) =
      t p ≫ cokernel.π j
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    simp only [cokernel.mapIso_hom, cokernel.π_desc]
    rfl
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  exact (cancel_epi (F.map (cokernel.π i))).1 (he'.trans he.symm)

/-- The quotient comparison selected from its unique universal-property characterization.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredGrIso (K : FilteredObject (CochainComplex A ℤ)) (p : ℤ) :
    (exactFilteredObject L K).filtration.gradedPiece p ≅
      (L.mapHomologicalComplex (.up ℤ)).obj (K.filtration.gradedPiece p) :=
  (exactFiltered_graded_iso L K p).exists.choose

include hLlim hLcolim in
private theorem exactFiltered_graded_naturality (bounded : Bool)
    {K M : Complex A bounded} (f : K ⟶ M) (p : ℤ) :
    (L.mapHomologicalComplex (.up ℤ)).map (FilteredObject.gradedMapSteps f.hom p) ≫
        (exactFilteredGrIso L M.obj p).inv =
      (exactFilteredGrIso L K.obj p).inv ≫
        FilteredObject.gradedMapSteps ((exactFilteredComplex L bounded).map f).hom p := by
  let F := L.mapHomologicalComplex (.up ℤ)
  let f' := ((exactFilteredComplex L bounded).map f).hom
  let tK := factorThruImageSubobject (F.map (K.obj.filtration.step p).arrow)
  let tM := factorThruImageSubobject (F.map (M.obj.filtration.step p).arrow)
  let πK := K.obj.filtration.complexQuotientπ p (p + 1) (by omega)
  let πM := M.obj.filtration.complexQuotientπ p (p + 1) (by omega)
  let πK' := (exactFilteredObject L K.obj).filtration.complexQuotientπ p (p + 1)
    (by omega)
  let πM' := (exactFilteredObject L M.obj).filtration.complexQuotientπ p (p + 1)
    (by omega)
  have hK : F.map πK ≫ (exactFilteredGrIso L K.obj p).inv = tK ≫ πK' :=
    (exactFiltered_graded_iso L K.obj p).exists.choose_spec
  have hM : F.map πM ≫ (exactFilteredGrIso L M.obj p).inv = tM ≫ πM' :=
    (exactFiltered_graded_iso L M.obj p).exists.choose_spec
  have hA : πK ≫ FilteredObject.gradedMapSteps f.hom p =
      FilteredObject.restrictionSteps f.hom p ≫ πM :=
    Classical.choose_spec (FilteredObject.exists_gradedMap_steps K.obj M.obj f.hom p)
  have hB : πK' ≫ FilteredObject.gradedMapSteps f' p =
      FilteredObject.restrictionSteps f' p ≫ πM' :=
    Classical.choose_spec (FilteredObject.exists_gradedMap_steps _ _ f' p)
  have hr : F.map (FilteredObject.restrictionSteps f.hom p) ≫ tM =
      tK ≫ FilteredObject.restrictionSteps f' p := by
    apply (cancel_mono ((exactFilteredObject L M.obj).filtration.step p).arrow).1
    have h₁ : FilteredObject.restrictionSteps f.hom p ≫
        (M.obj.filtration.step p).arrow = (K.obj.filtration.step p).arrow ≫ f.hom.hom :=
      Classical.choose_spec (f.hom.preserves p)
    have h₂ : FilteredObject.restrictionSteps f' p ≫
        ((exactFilteredObject L M.obj).filtration.step p).arrow =
        ((exactFilteredObject L K.obj).filtration.step p).arrow ≫ F.map f.hom.hom :=
      Classical.choose_spec (f'.preserves p)
    rw [Category.assoc]
    change F.map (FilteredObject.restrictionSteps f.hom p) ≫
        (tM ≫ (imageSubobject (F.map (M.obj.filtration.step p).arrow)).arrow) =
      (tK ≫ FilteredObject.restrictionSteps f' p) ≫
        ((exactFilteredObject L M.obj).filtration.step p).arrow
    rw [imageSubobject_arrow_comp, ← F.map_comp, h₁, F.map_comp,
      Category.assoc, h₂]
    change _ = tK ≫ (imageSubobject (F.map (K.obj.filtration.step p).arrow)).arrow ≫
      F.map f.hom.hom
    rw [← Category.assoc, imageSubobject_arrow_comp]
  have : Epi πK := by
    dsimp only [πK, DecreasingFiltration.complexQuotientπ]
    infer_instance
  apply (cancel_epi (F.map πK)).1
  change F.map πK ≫ (F.map (FilteredObject.gradedMapSteps f.hom p) ≫
      (exactFilteredGrIso L M.obj p).inv) =
    F.map πK ≫ ((exactFilteredGrIso L K.obj p).inv ≫
      FilteredObject.gradedMapSteps f' p)
  rw [← Category.assoc]
  rw [← F.map_comp, hA, F.map_comp, Category.assoc, hM,
    ← Category.assoc, hr, Category.assoc, ← hB]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ FilteredObject.gradedMapSteps f' p) hK.symm

include hLlim hLcolim in
/-- Exact termwise application preserves graded quasi-isomorphisms and therefore
inverts them after the target localization.
Source: Varshavsky, §§5.1.1–5.1.2.
Proof: exactness identifies each cokernel of consecutive mapped steps with L of
the original graded complex. Exact L preserves quasi-isomorphisms; target Q inverts
these maps by its localization property.
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
theorem exactFiltered_inverts (bounded : Bool) :
    (∀ (K M : Complex A bounded) (f : K ⟶ M), quasiIso bounded f →
      quasiIso bounded ((exactFilteredComplex L bounded).map f)) ∧
    (quasiIso (A := A) bounded).IsInvertedBy
      (exactFilteredComplex L bounded ⋙ Q bounded) := by
  have h (K M : Complex A bounded) (f : K ⟶ M) (hf : quasiIso bounded f) :
      quasiIso bounded ((exactFilteredComplex L bounded).map f) := by
    intro p
    let F := L.mapHomologicalComplex (.up ℤ)
    have : QuasiIso (FilteredObject.gradedMapSteps f.hom p) := hf p
    have : QuasiIso (F.map (FilteredObject.gradedMapSteps f.hom p)) := by
      dsimp only [F]
      infer_instance
    exact quasiIso_of_arrow_mk_iso (F.map (FilteredObject.gradedMapSteps f.hom p))
      (FilteredObject.gradedMapSteps ((exactFilteredComplex L bounded).map f).hom p)
      (Arrow.isoMk (exactFilteredGrIso L K.obj p).symm
        (exactFilteredGrIso L M.obj p).symm
        (exactFiltered_graded_naturality L bounded f p).symm)
  exact ⟨h, fun K M f hf ↦ (quasiIso (A := B) bounded).Q_inverts _ (h K M f hf)⟩

/-- L^F is the localization lift of the actual termwise filtered functor.
Source: Varshavsky, §§5.1.1–5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredDerived (bounded : Bool) :
    Derived (A := A) bounded ⥤ Derived (A := B) bounded :=
  Localization.lift (exactFilteredComplex L bounded ⋙ Q bounded)
    (exactFiltered_inverts L bounded).2 (Q bounded)

/-- The localization comparison fixes L^F on all filtered representatives.
Source: Varshavsky, §5.1.2
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
noncomputable def exactFilteredDerivedQ (bounded : Bool) :
    Q bounded ⋙ exactFilteredDerived L bounded ≅ exactFilteredComplex L bounded ⋙ Q bounded :=
  Localization.fac (exactFilteredComplex L bounded ⋙ Q bounded)
    (exactFiltered_inverts L bounded).2 (Q bounded)

variable [HasDerivedCategory.{max u₁ v₁} A] [HasDerivedCategory.{max u₂ v₂} B]
variable [HasDerivedCategory.{(max (max u₁ v₁) (max u₂ v₂)) + 1}
  AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)}]
variable [TriangulatedLocalization A true] [TriangulatedLocalization B true]
variable [TriangulatedLocalization AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} false]
variable (TA : TruncationCalculus A true) (TB : TruncationCalculus B true)
variable (C : TruncationCalculus AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} false)
variable
  (GA : GlobalHomCalculusIn.{max (max u₁ v₁) (max u₂ v₂), v₁, u₁} A TA C)
  (GB : GlobalHomCalculusIn.{max (max u₁ v₁) (max u₂ v₂), v₂, u₂} B TB C)

/-- Comparison data for the constructed L^F, with representative-normalized omega/gr
comparisons and ordinary and graded maps pinned on all cohomology groups to L.mapDerivedCategory.
Source: Varshavsky, §§5.1.2 and 5.1.5
(blueprint: lem-trf-filtered-global-hom-exact-adjunction). -/
structure FilteredGlobalHomExactAdjunctionData where
  omega : exactFilteredDerived L true ⋙ TB.omega ≅ TA.omega ⋙ L.mapDerivedCategory
  omega_normalization : ∀ K : Complex A true,
    omega.hom.app ((Q true).obj K) =
      TB.omega.map ((exactFilteredDerivedQ L true).hom.app K) ≫
        TB.omegaComparison.hom.app ((exactFilteredComplex L true).obj K) ≫
          L.mapDerivedCategoryFactors.inv.app K.obj.obj ≫
            L.mapDerivedCategory.map (TA.omegaComparison.inv.app K)
  gr : ∀ p : ℤ, exactFilteredDerived L true ⋙ TB.gr p ≅ TA.gr p ⋙ L.mapDerivedCategory
  gr_normalization : ∀ (p : ℤ) (K : Complex A true),
    (gr p).hom.app ((Q true).obj K) =
      (TB.gr p).map ((exactFilteredDerivedQ L true).hom.app K) ≫
        (TB.grComparison p).hom.app ((exactFilteredComplex L true).obj K) ≫
          DerivedCategory.Q.map (exactFilteredGrIso L K.obj p).hom ≫
            L.mapDerivedCategoryFactors.inv.app (K.obj.filtration.gradedPiece p) ≫
              L.mapDerivedCategory.map ((TA.grComparison p).inv.app K)
  c : ∀ P Q : Derived (A := A) true,
    (GA.filteredHom.obj (op P)).obj Q ≅
      (GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj ((exactFilteredDerived L
        true).obj Q)
  natural_source : ∀ (P P' Q : Derived (A := A) true) (f : P' ⟶ P),
    (GA.filteredHom.map f.op).app Q ≫ (c P' Q).hom =
      (c P Q).hom ≫ (GB.filteredHom.map ((exactFilteredDerived L true).map f).op).app
        ((exactFilteredDerived L true).obj Q)
  natural_target : ∀ (P Q Q' : Derived (A := A) true) (g : Q ⟶ Q'),
    (GA.filteredHom.obj (op P)).map g ≫ (c P Q').hom =
      (c P Q).hom ≫ (GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).map
        ((exactFilteredDerived L true).map g)
  ordinary : ∀ (P Q : Derived (A := A) true),
    (GA.ordinaryHom.obj (op (GA.omegaBounded.obj P))).obj (GA.omegaBounded.obj Q) ⟶
      (GB.ordinaryHom.obj (op (GB.omegaBounded.obj ((exactFilteredDerived L true).obj P)))).obj
        (GB.omegaBounded.obj ((exactFilteredDerived L true).obj Q))
  ordinary_cohomology : ∀ (P Q : Derived (A := A) true) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor
      AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).obj
        ((GA.ordinaryHom.obj (op (GA.omegaBounded.obj P))).obj (GA.omegaBounded.obj Q))),
    GB.cohomology (GB.omegaBounded.obj ((exactFilteredDerived L true).obj P))
      (GB.omegaBounded.obj ((exactFilteredDerived L true).obj Q)) n
      ((DerivedCategory.homologyFunctor
        AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).map (ordinary P Q) x) =
      (GB.omegaBoundedComparison.hom.app ((exactFilteredDerived L true).obj P) ≫
        omega.hom.app P ≫ L.mapDerivedCategory.map (GA.omegaBoundedComparison.inv.app P)) ≫
      L.mapDerivedCategory.map (GA.cohomology (GA.omegaBounded.obj P)
        (GA.omegaBounded.obj Q) n x) ≫
      (L.mapDerivedCategory.commShiftIso n).hom.app (GA.omegaBounded.obj Q).obj ≫
      (L.mapDerivedCategory.map (GA.omegaBoundedComparison.hom.app Q) ≫
        omega.inv.app Q ≫
        GB.omegaBoundedComparison.inv.app ((exactFilteredDerived L true).obj Q))⟦n⟧'
  underlying : ∀ (P Q : Derived (A := A) true),
    C.omega.map ((c P Q).hom) ≫
        (GB.underlyingComparison ((exactFilteredDerived L true).obj P)).hom.app
          ((exactFilteredDerived L true).obj Q) =
      (GA.underlyingComparison P).hom.app Q ≫ ordinary P Q
  gradedTerm : ∀ (r a : ℤ) (P Q : Derived (A := A) true),
    (GA.ordinaryHom.obj (op ((GA.grBounded a).obj P))).obj
          ((GA.grBounded (a + r)).obj Q) ⟶
      (GB.ordinaryHom.obj (op ((GB.grBounded a).obj ((exactFilteredDerived L true).obj P)))).obj
          ((GB.grBounded (a + r)).obj ((exactFilteredDerived L true).obj Q))
  gradedTerm_cohomology : ∀ (r a : ℤ) (P Q : Derived (A := A) true) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor
      AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).obj
        ((GA.ordinaryHom.obj (op ((GA.grBounded a).obj P))).obj
          ((GA.grBounded (a + r)).obj Q))),
    GB.cohomology ((GB.grBounded a).obj ((exactFilteredDerived L true).obj P))
      ((GB.grBounded (a + r)).obj ((exactFilteredDerived L true).obj Q)) n
      ((DerivedCategory.homologyFunctor
        AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} n).map (gradedTerm r a P Q) x) =
      ((GB.grBoundedComparison a).hom.app ((exactFilteredDerived L true).obj P) ≫
        (gr a).hom.app P ≫
        L.mapDerivedCategory.map ((GA.grBoundedComparison a).inv.app P)) ≫
      L.mapDerivedCategory.map (GA.cohomology ((GA.grBounded a).obj P)
        ((GA.grBounded (a + r)).obj Q) n x) ≫
      (L.mapDerivedCategory.commShiftIso n).hom.app ((GA.grBounded (a + r)).obj Q).obj ≫
      (L.mapDerivedCategory.map ((GA.grBoundedComparison (a + r)).hom.app Q) ≫
        (gr (a + r)).inv.app Q ≫
        (GB.grBoundedComparison (a + r)).inv.app ((exactFilteredDerived L true).obj Q))⟦n⟧'
  gradedSum : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    ∃ m : (GA.gradedSum r P Q).pt ⟶
        (GB.gradedSum r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L true).obj
          Q)).pt,
      ∀ a : ℤ, m ≫ (GB.gradedSum r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L
        true).obj Q)).π a =
        (GA.gradedSum r P Q).π a ≫ gradedTerm r a P Q
  graded : ∀ (r : ℤ) (P Q : Derived (A := A) true),
    (C.gr r).map ((c P Q).hom) ≫
          (GB.gradedComparison r ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L
            true).obj Q)).hom =
      (GA.gradedComparison r P Q).hom ≫ Classical.choose (gradedSum r P Q)
  morphism : ∀ (P Q : Derived (A := A) true) (f : P ⟶ Q),
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max (max u₁ v₁) (max u₂ v₂)} 0).map
        (C.omega.map ((C.high 0).map ((c P Q).hom))) (GA.homEquiv P Q f) =
      GB.homEquiv ((exactFilteredDerived L true).obj P) ((exactFilteredDerived L true).obj Q)
        ((exactFilteredDerived L true).map f)
  forgetful_and_grade_zero : ∀ (P Q : Derived (A := A) true),
    C.omega.map ((C.high 0).map ((c P Q).hom)) ≫
        (C.gradeProjection.app
          ((GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj
            ((exactFilteredDerived L true).obj Q))) =
      (C.gradeProjection.app ((GA.filteredHom.obj (op P)).obj Q)) ≫
        (C.gr 0).map ((c P Q).hom) ∧
    C.omega.map ((C.high 0).map ((c P Q).hom)) ≫
        C.omega.map ((C.inclusion 0).app
          ((GB.filteredHom.obj (op ((exactFilteredDerived L true).obj P))).obj
            ((exactFilteredDerived L true).obj Q))) =
      C.omega.map ((C.inclusion 0).app ((GA.filteredHom.obj (op P)).obj Q)) ≫
        C.omega.map ((c P Q).hom)

/-- An exact adjunction with invertible bounded-below derived unit gives the
canonical filtered global-Hom comparison for the constructed termwise functor.
Source: Varshavsky, §5.1.5 (exact-adjunction calculation), §§5.1.1–5.1.2
(filtered localizations) (blueprint: lem-trf-filtered-global-hom-exact-adjunction).

Proof: Resolve L^F Q by a bounded-below termwise filtered-injective J. Exactness of L
and adjunction imply that R preserves injectives. Split the finite flags of J to
identify gr(RJ) with R(gr J). The unit followed by R of the resolution Q to RJ is a
graded quasi-isomorphism, since it represents the assumed derived unit on each grade.
Termwise adjunction identifies the shift-filtered Hom complexes Hom(P,RJ) and
Hom(LP,J), in both directions preserving their filtrations. Descend along the
filtered-injective model and Hom-complex invariance. Forgetting gives the ordinary
comparison, whose H^n map is L on derived morphisms. Grading gives the finite sum of
these comparisons. The counit triangle identity identifies the H^0 filtered-morphism
map with L^F.map. Respect for F^0 and F^1 gives the inclusion and quotient squares. -/
-- STATEMENT-DISPUTED: the arbitrary calculus parameters allow an independent sign change
-- of gradedComparison at grade one, but the conclusion fixes that sign through gradedTerm
-- cohomology and the filtered-morphism comparison. See the delivery report's pure-grade test.
theorem filteredGlobalHomExactAdjunction
    [EnoughInjectives A] [EnoughInjectives B]
    {R : B ⥤ A} [R.Additive] (adj : L ⊣ R)
    [IsIso adj.derivedPlus.unit] :
    Nonempty (FilteredGlobalHomExactAdjunctionData L TA TB C GA GB) := by
  sorry

end CochainComplex.FiniteFiltered
