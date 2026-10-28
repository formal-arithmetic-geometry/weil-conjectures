/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.SixFunctors.SystemTotalEnrichedTranspose

/-! # The specified integral adjunction equals the descended system adjunction

Source: prop-coef-integral-exceptional-adjoint, mapping-complex proof paragraph 2,
and the accepted six-step DAG comparison proof
(blueprint: lem-coef-integral-exceptional-descended-counit).

All maps are defined in ordinary derived categories before finite evaluation.
The normalized system domain has finite-Tor constructible levels separately;
no bound common to every level or every object is imposed on that domain.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SZ : CoefficientDerivedSystemCalculus l E c.Z)
  (SY : CoefficientDerivedSystemCalculus l E Y)
  (r : Realization l E D hl f c SX SZ SY)
  (h : Domains l E D hl f c SX SZ SY r)

variable {l E D hl f c SX SZ SY}

/-- The counit-induced kappa, applying L_Y F_f to the actual reconstruction counit.
Source: the displayed kappa in the node
(blueprint: lem-coef-integral-exceptional-descended-counit). -/
def kappa (M : sfIntegralConstructibleCategory l E Y) :=
  (coefficientSequenceLimit l E Y).map
    ((r.F.map (ObjectProperty.homMk
      (X := (reductionX r h).obj ((right r h).obj M))
      (Y := r.G.obj ((reductionY r h).obj M))
      (SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj))).hom)

/-- The descended counit, in categorical composition order.
Source: the displayed counit identity in the node
(blueprint: lem-coef-integral-exceptional-descended-counit). -/
def descendedCounit (M : sfIntegralConstructibleCategory l E Y) :=
  letI := h.unitY M
  kappa r h M ≫
    (coefficientSequenceLimit l E Y).map
      ((r.adjunction.counit.app ((reductionY r h).obj M)).hom) ≫
    inv (SY.adjunction.unit.app M.obj)

/-- The descended unit uses u_X, the actual system unit, and the inverse of e_Y.
Source: the node's final equivalence with reconstruction descent
(blueprint: lem-coef-integral-exceptional-descended-counit). -/
def descendedUnit (K : sfIntegralConstructibleCategory l E X) :=
  letI := h.counitY (r.F.obj ((reductionX r h).obj K))
  SX.adjunction.unit.app K.obj ≫
    (coefficientSequenceLimit l E X).map
      ((r.adjunction.unit.app ((reductionX r h).obj K)).hom) ≫
    (coefficientSequenceLimit l E X).map
      ((r.G.map (ObjectProperty.homMk
        (X := r.F.obj ((reductionX r h).obj K))
        (Y := (reductionY r h).obj ((left r h).obj K))
        (inv (SY.adjunction.counit.app (r.F.obj ((reductionX r h).obj K)).obj)))).hom)

/-- The descended Hom bijection, composed from actual adjunction bijections and
actual reconstruction isomorphisms. Full inclusions leave the arrows unchanged.
Source: the final paragraph of the node and reconstruction adjunction calculus
(blueprint: lem-coef-integral-exceptional-descended-counit). -/
def descendedHom (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) :
    ((left r h).obj K ⟶ M) ≃ (K ⟶ (right r h).obj M) :=
  letI := h.unitY M
  letI := h.counitY (r.F.obj ((reductionX r h).obj K))
  ((sfIntegralConstructible l E Y).fullyFaithfulι.homEquiv
      (X := (left r h).obj K) (Y := M)).trans
    ((Iso.homCongr (Iso.refl _) (asIso (SY.adjunction.unit.app M.obj))).trans
      (((SY.adjunction.homEquiv (left r h |>.obj K |>.obj) (SY.reduction.obj M.obj)).symm).trans
        ((Iso.homCongr
          (asIso (SY.adjunction.counit.app (r.F.obj ((reductionX r h).obj K)).obj))
          (Iso.refl _)).trans
          (((domain l E Y).fullyFaithfulι.homEquiv
            (X := r.F.obj ((reductionX r h).obj K))
            (Y := (reductionY r h).obj M)).symm.trans
            ((r.adjunction.homEquiv ((reductionX r h).obj K) ((reductionY r h).obj M)).trans
              (((domain l E X).fullyFaithfulι.homEquiv
                (X := (reductionX r h).obj K)
                (Y := r.G.obj ((reductionY r h).obj M))).trans
                ((SX.adjunction.homEquiv K.obj
                  (r.G.obj ((reductionY r h).obj M)).obj).trans
                  ((sfIntegralConstructible l E X).fullyFaithfulι.homEquiv
                    (X := K) (Y := (right r h).obj M)).symm)))))))

private theorem left_map_hom
    {K K' : sfIntegralConstructibleCategory l E X} (v : K ⟶ K') :
    ((left r h).map v).hom = (coefficientSequenceLimit l E Y).map
      ((r.F.map ((reductionX r h).map v)).hom) := rfl

private theorem right_map_hom
    {M M' : sfIntegralConstructibleCategory l E Y} (w : M ⟶ M') :
    ((right r h).map w).hom = (coefficientSequenceLimit l E X).map
      ((r.G.map ((reductionY r h).map w)).hom) := rfl

private theorem descendedHom_symm_apply
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) (w : K ⟶ (right r h).obj M) :
    ((descendedHom r h K M).symm w).hom =
      (coefficientSequenceLimit l E Y).map
        (((r.adjunction.homEquiv ((reductionX r h).obj K)
          ((reductionY r h).obj M)).symm
          (ObjectProperty.homMk (SX.reduction.map w.hom ≫
            SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj))).hom) ≫
        @inv _ _ _ _ (SY.adjunction.unit.app M.obj) (h.unitY M) := by
  let := h.unitY M
  let := h.counitY (r.F.obj ((reductionX r h).obj K))
  let b := ((r.adjunction.homEquiv ((reductionX r h).obj K)
    ((reductionY r h).obj M)).symm
      (ObjectProperty.homMk (SX.reduction.map w.hom ≫
        SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj))).hom
  dsimp only [descendedHom, left, right, reductionX, reductionY,
    reducedConstructible, ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj,
    Equiv.trans, Equiv.symm, Iso.homCongr, Functor.FullyFaithful.homEquiv,
    ObjectProperty.fullyFaithfulι, Adjunction.homEquiv, Equiv.coe_fn_mk,
    Function.comp_apply]
  simp only [Iso.refl_hom, Iso.refl_inv, asIso_hom, asIso_inv,
    ObjectProperty.ι_map, ObjectProperty.homMk_hom, Category.id_comp, Category.comp_id]
  change (SY.adjunction.unit.app
      ((coefficientSequenceLimit l E Y).obj (r.F.obj ((reductionX r h).obj K)).obj) ≫
      (coefficientSequenceLimit l E Y).map
        (SY.adjunction.counit.app (r.F.obj ((reductionX r h).obj K)).obj ≫ b)) ≫
        inv (SY.adjunction.unit.app M.obj) =
      (coefficientSequenceLimit l E Y).map b ≫ inv (SY.adjunction.unit.app M.obj)
  rw [Functor.map_comp, ← Category.assoc, SY.adjunction.right_triangle_components]
  exact congrArg (fun z ↦ z ≫ inv (SY.adjunction.unit.app M.obj))
    (Category.id_comp ((coefficientSequenceLimit l E Y).map b))

/-- Naturality of the actual descended Hom bijections, allowing their canonical
assembly into an adjunction. Source: reconstruction adjunction calculus and step 6
of the comparison proof (blueprint: lem-coef-integral-exceptional-descended-counit).
Proof: each factor in descendedHom is natural: full inclusions, postcomposition
by the actual unit, the two reduction/limit adjunctions, precomposition by the
actual counit inverse, and the system adjunction. Compose their naturality squares. -/
theorem descendedHom_naturality :
    (∀ {K' K : sfIntegralConstructibleCategory l E X}
      {M : sfIntegralConstructibleCategory l E Y} (v : K' ⟶ K)
      (w : K ⟶ (right r h).obj M),
      (descendedHom r h K' M).symm (v ≫ w) =
        (left r h).map v ≫ (descendedHom r h K M).symm w) ∧
    (∀ {K : sfIntegralConstructibleCategory l E X}
      {M M' : sfIntegralConstructibleCategory l E Y}
      (v : (left r h).obj K ⟶ M) (w : M ⟶ M'),
      descendedHom r h K M' (v ≫ w) =
        descendedHom r h K M v ≫ (right r h).map w) := by
  have hn {K : sfIntegralConstructibleCategory l E X}
      {M M' : sfIntegralConstructibleCategory l E Y}
      (v : K ⟶ (right r h).obj M) (w : M ⟶ M') :
      (descendedHom r h K M').symm (v ≫ (right r h).map w) =
        (descendedHom r h K M).symm v ≫ w := by
    let := h.unitY M
    let := h.unitY M'
    have he := SX.adjunction.counit.naturality
      ((r.G.map ((reductionY r h).map w)).hom)
    dsimp only [Functor.comp_map, Functor.id_map] at he
    have ht : SX.reduction.map ((v ≫ (right r h).map w).hom) ≫
        SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M')).obj =
        (SX.reduction.map v.hom ≫
          SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj) ≫
          (r.G.map ((reductionY r h).map w)).hom := by
      simpa only [ObjectProperty.FullSubcategory.comp_hom, right_map_hom,
        Functor.map_comp, Category.assoc] using congrArg (fun z ↦ SX.reduction.map v.hom ≫ z) he
    have hu : (coefficientSequenceLimit l E Y).map (SY.reduction.map w.hom) ≫
        inv (SY.adjunction.unit.app M'.obj) =
        inv (SY.adjunction.unit.app M.obj) ≫ w.hom := by
      have hh := congrArg (fun z ↦ inv (SY.adjunction.unit.app M.obj) ≫ z ≫
        inv (SY.adjunction.unit.app M'.obj)) (SY.adjunction.unit.naturality w.hom)
      simpa only [Functor.id_map, Functor.comp_map, Category.assoc,
        IsIso.inv_hom_id_assoc, IsIso.hom_inv_id, Category.comp_id] using hh.symm
    apply (sfIntegralConstructible l E Y).fullyFaithfulι.map_injective
    change ((descendedHom r h K M').symm _).hom =
      ((descendedHom r h K M).symm v).hom ≫ w.hom
    simp only [descendedHom_symm_apply r h K M', descendedHom_symm_apply r h K M]
    let t : (reductionX r h).obj K ⟶ r.G.obj ((reductionY r h).obj M) :=
      ObjectProperty.homMk (SX.reduction.map v.hom ≫
        SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj)
    have heq : ObjectProperty.homMk
        (SX.reduction.map ((v ≫ (right r h).map w).hom) ≫
          SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M')).obj) =
        t ≫ r.G.map ((reductionY r h).map w) := InducedCategory.hom_ext ht
    have htrans := r.adjunction.homEquiv_naturality_right_symm t ((reductionY r h).map w)
    have htotal := congrArg
      (fun z : (reductionX r h).obj K ⟶ r.G.obj ((reductionY r h).obj M') ↦
        (r.adjunction.homEquiv _ _).symm z) heq
    have hmap := congrArg
      (fun z : r.F.obj ((reductionX r h).obj K) ⟶ (reductionY r h).obj M' ↦
        (coefficientSequenceLimit l E Y).map z.hom) (htotal.trans htrans)
    exact (congrArg (fun z ↦ z ≫ inv (SY.adjunction.unit.app M'.obj)) hmap).trans
      (by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
        change (coefficientSequenceLimit l E Y).map
            ((r.adjunction.homEquiv _ _).symm t).hom ≫
            (coefficientSequenceLimit l E Y).map (SY.reduction.map w.hom) ≫
            inv (SY.adjunction.unit.app M'.obj) = _
        rw [hu])
  constructor
  · intro K' K M v w
    have ht : ObjectProperty.homMk
        (SX.reduction.map ((v ≫ w).hom) ≫
          SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj) =
        (reductionX r h).map v ≫ ObjectProperty.homMk
          (SX.reduction.map w.hom ≫
            SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj) := by
      ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        Functor.map_comp, Category.assoc]
      rfl
    apply (sfIntegralConstructible l E Y).fullyFaithfulι.map_injective
    change ((descendedHom r h K' M).symm _).hom =
      ((left r h).map v).hom ≫ ((descendedHom r h K M).symm w).hom
    simp only [descendedHom_symm_apply r h K' M, descendedHom_symm_apply r h K M]
    rw [ht, r.adjunction.homEquiv_naturality_left_symm]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc,
      left_map_hom]
  · intro K M M' v w
    apply (descendedHom r h K M').symm.injective
    rw [Equiv.symm_apply_apply, hn, Equiv.symm_apply_apply]

/-- The actual descended adjunction, assembled from the composite Hom bijections.
Source: reconstruction adjunction calculus and step 6 of the comparison proof
(blueprint: lem-coef-integral-exceptional-descended-counit). -/
def descendedAdjunction : left r h ⊣ right r h :=
  Adjunction.mkOfHomEquiv
    { homEquiv := descendedHom r h
      homEquiv_naturality_left_symm := (descendedHom_naturality r h).1
      homEquiv_naturality_right := (descendedHom_naturality r h).2 }


private theorem integralHom_map {W : Scheme.{u}}
    (P Q P' Q' : DerivedCategory (scalarReductionSource l E W))
    (f : P' ⟶ P) (g : Q ⟶ Q') (v : P ⟶ Q) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
      ((coefficientIntegralGlobalHom l E W).map (Prod.mkHom f.op g))
        ((coefficientIntegralHomEquiv l E W P Q).symm v) =
      (coefficientIntegralHomEquiv l E W P' Q').symm (f ≫ v ≫ g) := by
  apply (coefficientIntegralHomEquiv l E W P' Q').injective
  have hi := (coefficientHomZeroEquiv_exists.{u, u+1, u}
    (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.1.1
  simpa [coefficientIntegralHomEquiv, coefficientHomZeroEquiv,
    coefficientIntegralGlobalHom, coefficientIntegralSections] using
    hi P Q P' Q' f g ((coefficientIntegralHomEquiv l E W P Q).symm v)

attribute [local irreducible] coefficientSequenceLimit coefficientIntegralHomEquiv
  coefficientIntegralGlobalHom coefficientSequenceGlobalHom totalHom


private theorem totalHom_reduction {W : Scheme.{u}}
    (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemCoherence l E W S)
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N)
    [IsIso (S.adjunction.counit.app (S.reduction.obj K))]
    (b : S.reduction.obj K ⟶ N) :
    totalHom S (S.reduction.obj K) N hN b =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
        (S.gamma l E W K N hN).hom
          ((coefficientIntegralHomEquiv l E W _ _).symm (S.adjunction.homEquiv K N b)) := by
  have he : inv (S.adjunction.counit.app (S.reduction.obj K)) =
      S.reduction.map (S.adjunction.unit.app K) := by
    apply (cancel_mono (S.adjunction.counit.app (S.reduction.obj K))).1
    erw [IsIso.inv_hom_id]
    exact (S.adjunction.left_triangle_components K).symm
  have hg := C.gamma_naturality _ _ N N hN hN (S.adjunction.unit.app K) (𝟙 N)
  try dsimp only [Functor.id_obj, Functor.comp_obj] at hg
  erw [CategoryTheory.Functor.map_id] at hg
  unfold totalHom
  erw [he, ← hg, Functor.map_comp, AddCommGrpCat.comp_apply, integralHom_map]
  simp only [Category.comp_id, Adjunction.homEquiv_unit]
  rfl

private theorem reconstruction_lambda_counit {W : Scheme.{u}}
    (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemCoherence l E W S)
    (K : DerivedCategory (scalarReductionSource l E W))
    (N : coefficientSequenceDerived l E W) (hN : IsNormalizedCoefficientSequence l E W N) :
    ((coefficientIntegralGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op K))
          (S.adjunction.unit.app ((coefficientSequenceLimit l E W).obj N))) ≫
      (S.gamma l E W K
        (S.reduction.obj ((coefficientSequenceLimit l E W).obj N))
        (S.reduction_normalized _)).hom) ≫
      coefficientMappingLimit.{u+1}.map
        ((coefficientSequenceGlobalHom l E W).map
          (Prod.mkHom (𝟙 _) (S.adjunction.counit.app N))) =
      (S.gamma l E W K N hN).hom := by
  have hg := C.gamma_naturality K K _ N (S.reduction_normalized _) hN (𝟙 K)
    (S.adjunction.counit.app N)
  try dsimp only [Functor.id_obj, Functor.comp_obj] at hg
  erw [CategoryTheory.Functor.map_id] at hg
  erw [Category.assoc, ← hg, ← Category.assoc, ← Functor.map_comp]
  have hp : Prod.mkHom (𝟙 (op K))
        (S.adjunction.unit.app ((coefficientSequenceLimit l E W).obj N)) ≫
      Prod.mkHom (𝟙 K).op
        ((coefficientSequenceLimit l E W).map (S.adjunction.counit.app N)) = 𝟙 _ := by
    ext
    · simp
    · exact S.adjunction.right_triangle_components N
  erw [hp, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem homMap_descendedHom
    (CX : CoefficientDerivedSystemCoherence l E X SX)
    (CY : CoefficientDerivedSystemCoherence l E Y SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (a : Enriched r g s βX βY)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y) (v : (left r h).obj K ⟶ M) :
    homMap r h a.iso K M v = descendedHom r h K M v := by
  let P : (domain l E X).FullSubcategory := ⟨SX.reduction.obj K.obj, h.reductionX K⟩
  let Q : (domain l E Y).FullSubcategory := ⟨SY.reduction.obj M.obj, h.reductionY M⟩
  let B := r.F.obj P
  let T := r.G.obj Q
  let := h.unitY M
  let := h.counitX P
  let : IsIso (SX.adjunction.counit.app (SX.reduction.obj K.obj)) := h.counitX P
  let := h.counitX T
  let := h.counitY B
  let := h.lambdaX K ((right r h).obj M)
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0
  let b : B ⟶ Q := ObjectProperty.homMk
    (inv (SY.adjunction.counit.app B.obj) ≫ SY.reduction.map v.hom)
  let t := r.adjunction.homEquiv P Q b
  let w := SX.adjunction.homEquiv K.obj T.obj t.hom
  dsimp only [left, right, reductionX, reductionY, reducedConstructible,
    ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj] at *
  have hb : v.hom ≫ SY.adjunction.unit.app M.obj =
      (coefficientSequenceLimit l E Y).map b.hom := by
    have he : (coefficientSequenceLimit l E Y).map
        (inv (SY.adjunction.counit.app B.obj)) = SY.adjunction.unit.app
          ((coefficientSequenceLimit l E Y).obj B.obj) := by
      apply (cancel_mono ((coefficientSequenceLimit l E Y).map
        (SY.adjunction.counit.app B.obj))).1
      simp only [← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
        SY.adjunction.right_triangle_components]
      rfl
    change _ = (coefficientSequenceLimit l E Y).map
      (inv (SY.adjunction.counit.app B.obj) ≫ SY.reduction.map v.hom)
    erw [Functor.map_comp, he]
    simpa only [Functor.id_map, Functor.comp_map, left, reductionX, reducedConstructible,
      ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj] using
      SY.adjunction.unit.naturality v.hom
  have hinput : H₀.map
      ((coefficientIntegralGlobalHom l E Y).map
          (Prod.mkHom (𝟙 (op ((left r h).obj K).obj)) (SY.adjunction.unit.app M.obj)) ≫
        (SY.gamma l E Y ((left r h).obj K).obj Q.obj Q.property.1).hom ≫
        coefficientMappingLimit.{u+1}.map
          ((coefficientSequenceGlobalHom l E Y).map
            (Prod.mkHom (inv (SY.adjunction.counit.app B.obj)).op (𝟙 Q.obj))))
        ((coefficientIntegralHomEquiv l E Y _ _).symm v.hom) =
      totalHom SY B.obj Q.obj Q.property.1 b.hom := by
    dsimp only [left, reductionX, reducedConstructible, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj]
    unfold totalHom
    simp only [Functor.map_comp, AddCommGrpCat.comp_apply, H₀]
    erw [integralHom_map]
    simp only [Category.id_comp, hb]
    rfl
  have hmiddle := systemTotalEnrichedTranspose r CX CY g s βX βY a P Q b
  have houtput := totalHom_reduction SX CX K.obj T.obj T.property.1 t.hom
  let lambdaXMap := (coefficientIntegralGlobalHom l E X).map
      (Prod.mkHom (𝟙 (op K.obj)) (SX.adjunction.unit.app ((right r h).obj M).obj)) ≫
    (SX.gamma l E X K.obj (SX.reduction.obj ((right r h).obj M).obj)
      (SX.reduction_normalized ((right r h).obj M).obj)).hom
  let e := (coefficientSequenceGlobalHom l E X).map
    (Prod.mkHom (𝟙 (op P.obj)) (SX.adjunction.counit.app T.obj))
  have he : IsIso e := by
    have ht : IsIso (Prod.mkHom (𝟙 (op P.obj)) (SX.adjunction.counit.app T.obj)) := by
      exact (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    exact (coefficientSequenceGlobalHom l E X).map_isIso _
  have hout : H₀.map (inv lambdaXMap)
      (H₀.map (coefficientMappingLimit.{u+1}.map (inv e))
        (totalHom SX P.obj T.obj T.property.1 t.hom)) =
      (coefficientIntegralHomEquiv l E X _ _).symm w := by
    erw [houtput]
    have hγ := reconstruction_lambda_counit SX CX K.obj T.obj T.property.1
    change lambdaXMap ≫ coefficientMappingLimit.{u+1}.map e = _ at hγ
    erw [← hγ, Functor.map_comp, AddCommGrpCat.comp_apply]
    change (H₀.map lambdaXMap ≫ H₀.map (coefficientMappingLimit.{u+1}.map e) ≫
      H₀.map (coefficientMappingLimit.{u+1}.map (inv e)) ≫
      H₀.map (inv lambdaXMap)) _ = _
    simp only [Functor.map_inv, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
      AddCommGrpCat.id_apply]
    rfl
  have hm : (homMap r h a.iso K M v).hom = w := by
    unfold homMap mappingMap
    simp only [Functor.map_comp, AddCommGrpCat.comp_apply]
    have hin := hinput
    simp only [Functor.map_comp, AddCommGrpCat.comp_apply] at hin
    erw [hin, hmiddle]
    have hi : (coefficientSequenceGlobalHom l E X).map
        (Prod.mkHom (𝟙 _) (inv (SX.adjunction.counit.app T.obj))) = inv e := by
      apply (cancel_mono e).1
      simp only [IsIso.inv_hom_id]
      dsimp only [e]
      erw [← Functor.map_comp]
      have hp : Prod.mkHom (𝟙 (op P.obj)) (inv (SX.adjunction.counit.app T.obj)) ≫
          Prod.mkHom (𝟙 (op P.obj)) (SX.adjunction.counit.app T.obj) = 𝟙 _ := by
        ext <;> simp
      erw [hp, CategoryTheory.Functor.map_id]
    erw [hi]
    exact (congrArg (coefficientIntegralHomEquiv l E X _ _) hout).trans
      ((coefficientIntegralHomEquiv l E X _ _).apply_symm_apply w)
  apply (descendedHom r h K M).symm.injective
  erw [Equiv.symm_apply_apply]
  apply (sfIntegralConstructible l E Y).fullyFaithfulι.map_injective
  change ((descendedHom r h K M).symm (homMap r h a.iso K M v)).hom = v.hom
  erw [descendedHom_symm_apply, hm]
  have ht : SX.reduction.map w ≫ SX.adjunction.counit.app T.obj = t.hom :=
    (SX.adjunction.homEquiv K.obj T.obj).symm_apply_apply t.hom
  erw [ht]
  change (coefficientSequenceLimit l E Y).map
      ((r.adjunction.homEquiv P Q).symm (r.adjunction.homEquiv P Q b)).hom ≫
      inv (SY.adjunction.unit.app M.obj) = v.hom
  erw [Equiv.symm_apply_apply, ← hb]
  simp

private theorem descendedHom_unit
    (K : sfIntegralConstructibleCategory l E X) :
    (descendedHom r h K ((left r h).obj K) (𝟙 _)).hom = descendedUnit r h K := by
  let := h.unitY ((left r h).obj K)
  let := h.counitY (r.F.obj ((reductionX r h).obj K))
  dsimp only [descendedHom, left, right, reductionX, reductionY,
    reducedConstructible, ObjectProperty.lift, Functor.comp_obj, ObjectProperty.ι_obj,
    Equiv.trans, Equiv.symm, Iso.homCongr, Functor.FullyFaithful.homEquiv,
    ObjectProperty.fullyFaithfulι, Adjunction.homEquiv, Equiv.coe_fn_mk,
    Function.comp_apply]
  simp only [Iso.refl_hom, Iso.refl_inv, asIso_hom, asIso_inv,
    ObjectProperty.ι_map, Category.id_comp, Category.comp_id,
    ObjectProperty.FullSubcategory.id_hom, SY.adjunction.left_triangle_components,
    ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp]
  rfl

private theorem descendedHom_counit
    (M : sfIntegralConstructibleCategory l E Y) :
    ((descendedHom r h ((right r h).obj M) M).symm (𝟙 _)).hom =
      descendedCounit r h M := by
  erw [descendedHom_symm_apply]
  simp only [ObjectProperty.FullSubcategory.id_hom, Adjunction.homEquiv_counit,
    ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The specified integral exceptional adjunction is exactly the reconstruction
 descent of the specified enriched finite-system adjunction. In particular its
actual counit is u inverse after L(epsilon_sys) after kappa. Equality of adjunction
data includes the natural unit, natural counit and every Hom bijection.

Source: prop-coef-integral-exceptional-adjoint, proof paragraph 2; the accepted
six-step comparison proof
(blueprint: lem-coef-integral-exceptional-descended-counit).

Proof:
1. Domains already supplies normalized finite-Tor membership and invertible actual
reconstruction units and counits. Functoriality makes kappa invertible.
2. For v : F K → M, put P=R_X K, Q=R_Y M, B=F_sys P and T=G_sys Q.
The actual arrow b : B → Q is e_B inverse followed by R_Y(v). Unit naturality
and the right triangle identify L_Y(b) with v followed by u_M. Naturality of the
integral H-zero Hom identification shows that the first two mapping factors
send v to totalHom_SY(b).
3. The system total enriched transpose sends this class to totalHom_SX(t), where
t is the actual system adjunct of b. This is the middle step, isolated as
systemTotalEnrichedTranspose. Gamma naturality in the source, together with the
left reconstruction triangle, identifies this with gamma applied to the integral
adjunct w of t. Naturality in the target and the right triangle show that lambda
followed by the actual counit is gamma. Its inverses cancel the two remaining
mapping factors. Thus the specified Hom map sends v to w.
4. Apply the inverse descended Hom equivalence. Its formula is L_Y of the inverse
system transpose of e_T after R_X(w), followed by u_M inverse. The two actual
adjunction bijections cancel, and step 2 cancels the final unit. This proves the
entire Hom comparison, on total mapping classes without finite projections.
5. Evaluating the descended Hom map and its inverse at identities gives the
stated unit and counit formulas. Adjunction.ext identifies the adjunctions and
hence their natural units and counits. All calculations are naturality or actual
triangle identities; identity geometry, zero objects and empty schemes obey the
same equations, and no nonemptiness or uniform Tor bound enters.
-/
theorem integralExceptionalDescendedCounit
    (_CX : CoefficientDerivedSystemCoherence l E X SX)
    (_CY : CoefficientDerivedSystemCoherence l E Y SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (a : Enriched r g s βX βY) (adj : left r h ⊣ right r h)
    (_specified : IsSpecified r h a.iso adj) :
    (∀ M : sfIntegralConstructibleCategory l E Y,
      domain l E Y (SY.reduction.obj M.obj) ∧
      domain l E X (r.G.obj ((reductionY r h).obj M)).obj ∧
      IsIso (SX.adjunction.counit.app (r.G.obj ((reductionY r h).obj M)).obj) ∧
      IsIso (SY.adjunction.unit.app M.obj) ∧ IsIso (kappa r h M) ∧
      (adj.counit.app M).hom = descendedCounit r h M) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      (adj.unit.app K).hom = descendedUnit r h K) ∧
    (∀ (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y),
      adj.homEquiv K M = descendedHom r h K M) ∧
    adj = descendedAdjunction r h ∧
    adj.unit = (descendedAdjunction r h).unit ∧
    adj.counit = (descendedAdjunction r h).counit := by
  have hhom (K : sfIntegralConstructibleCategory l E X)
      (M : sfIntegralConstructibleCategory l E Y) :
      adj.homEquiv K M = descendedHom r h K M := by
    apply Equiv.ext
    intro v
    exact (_specified K M v).trans
      (homMap_descendedHom r h _CX _CY g s βX βY a K M v)
  have hadj : adj = descendedAdjunction r h := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext K
    erw [← adj.homEquiv_id, ← (descendedAdjunction r h).homEquiv_id, hhom]
    erw [descendedAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  refine ⟨?_, ?_, hhom, hadj, congrArg Adjunction.unit hadj,
    congrArg Adjunction.counit hadj⟩
  · intro M
    let T := r.G.obj ((reductionY r h).obj M)
    let := h.counitX T
    let e : (reductionX r h).obj ((right r h).obj M) ⟶ T :=
      ObjectProperty.homMk (SX.adjunction.counit.app T.obj)
    have he : IsIso e := by
      let : IsIso ((domain l E X).ι.map e) := by
        change IsIso (SX.adjunction.counit.app T.obj)
        infer_instance
      exact (domain l E X).fullyFaithfulι.isIso_of_isIso_map e
    have hk : IsIso (kappa r h M) := by
      unfold kappa
      infer_instance
    refine ⟨h.reductionY M, T.property, h.counitX T, h.unitY M, hk, ?_⟩
    erw [← adj.homEquiv_symm_id, hhom]
    exact descendedHom_counit r h M
  · intro K
    erw [← adj.homEquiv_id, hhom]
    exact descendedHom_unit r h K

end WeilConjectures.IntegralExceptionalMapping
