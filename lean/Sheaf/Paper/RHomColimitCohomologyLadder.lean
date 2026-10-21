/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.Algebra.Homology.RHomColimitSourceTransport
import Sheaf.CategoryTheory.SignedDerivedInternalHomExact

/-! # The filtered-target internal-Hom cohomology ladder

Source: Stacks Project, Tags 03DB, 08JC and 05RS
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).

The arrows below use the recorded internal Hom and its signed source shift.
The comparison is the actual image of the strict model's colimit cocone map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace WeilConjectures.SfbHomFilteredColimit

attribute [local irreducible] CategoryTheory.homComplexFunctor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  (R : Sheaf J CommRingCat.{max u v r})

/-- The strict termwise-colimit Hom model, functorial contravariantly in its source.
Source: Stacks 03DB, 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderModel {I : Type (max u v r)} [SmallCategory I]
    (N : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) :
    (CochainComplex (Modules.{u, v, r} J R) ℤ)ᵒᵖ ⥤
      CochainComplex (Modules.{u, v, r} J R) ℤ :=
  homComplexFunctor.{u, v, max u v r, max u v r} (R := R) ⋙
    (Functor.whiskeringLeft I _ _).obj (N ⋙ coefficientHomResolution.{r, u, v} J R) ⋙ colim

variable [HasDerivedCategory.{w} (Modules.{u, v, r} J R)]

/-- The fixed-target derived internal Hom, using the recorded bifunctor.
Source: Stacks 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
abbrev ladderTarget (M : DerivedCategory (Modules.{u, v, r} J R)) :=
  (Functor.flip (Functor.curry.obj (derivedInternalHomOfUniverses.{u, v, r, w} J R))).obj M

/-- Precomposition, followed by degree-q cohomology, natural in the target.
Source: Stacks 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderPrecomp {A B : DerivedCategory (Modules.{u, v, r} J R)} (f : A ⟶ B) (q : ℤ) :
    RingedHomUniverses.hom.{u, v, r, w} J R B ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q ⟶
      RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q :=
  Functor.whiskerRight ((Functor.curry.obj
    (derivedInternalHomOfUniverses.{u, v, r, w} J R)).map f.op) _

/-- The connecting arrow uses the signed source shift, not an arbitrary boundary.
In Hom degree n the inverse source reindexing has the factor (-1)^n.
Source: Stacks 0A8X, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderBoundary (T : Triangle (DerivedCategory (Modules.{u, v, r} J R))) (q : ℤ) :
    RingedHomUniverses.hom.{u, v, r, w} J R T.obj₁ ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) (q - 1) ⟶
      RingedHomUniverses.hom.{u, v, r, w} J R T.obj₃ ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q :=
  Functor.whiskerLeft (RingedHomUniverses.hom.{u, v, r, w} J R T.obj₁)
      ((DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) 0).shiftIso
        (-1) q (q - 1) (by omega)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (RingedHomUniverses.sourceShift.{u, v, r, w} J R T.obj₁ 1).hom _ ≫
    ladderPrecomp.{u, v, r, w} J R T.mor₃ q

variable {I : Type (max u v r)} [SmallCategory I]
  (N : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ)

/-- The diagram of degree-q derived internal-Hom cohomology sheaves.
Source: Stacks 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
abbrev ladderDiagram (A : DerivedCategory (Modules.{u, v, r} J R)) (q : ℤ) :=
  N ⋙ DerivedCategory.Q ⋙ RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
    DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q

/-- The colimit-row precomposition arrow.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderColimPrecomp {A B : DerivedCategory (Modules.{u, v, r} J R)}
    (f : A ⟶ B) (q : ℤ) :
    colimit (ladderDiagram.{u, v, r, w} J R N B q) ⟶
      colimit (ladderDiagram.{u, v, r, w} J R N A q) :=
  colim.map (Functor.whiskerLeft (N ⋙ DerivedCategory.Q) (ladderPrecomp.{u, v, r, w} J R f q))

/-- The colimit of the signed connecting arrows.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderColimBoundary (T : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
    (q : ℤ) : colimit (ladderDiagram.{u, v, r, w} J R N T.obj₁ (q - 1)) ⟶
      colimit (ladderDiagram.{u, v, r, w} J R N T.obj₃ q) :=
  colim.map (Functor.whiskerLeft (N ⋙ DerivedCategory.Q) (ladderBoundary.{u, v, r, w} J R T q))

/-- The vertical map induced by the actual target cocone, on cohomology sheaves.
Source: Stacks 03DB, 08JC (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderVertical (A : DerivedCategory (Modules.{u, v, r} J R)) (q : ℤ) :
    colimit (ladderDiagram.{u, v, r, w} J R N A q) ⟶
      ((RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
        DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).obj
          (DerivedCategory.Q.obj (colimit N))) :=
  colimit.desc _ ((RingedHomUniverses.hom.{u, v, r, w} J R A ⋙
    DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).mapCocone
      (DerivedCategory.Q.mapCocone (colimit.cocone N)))

/-- The image of the canonical strict Hom-complex cocone map, with its fixed
localization comparison to the derived internal Hom at the target colimit.
Source: Stacks 03DB, 08J7 (blueprint: lem-sfb-rhom-colimit-cohomology-ladder). -/
def ladderStrictAlpha (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    DerivedCategory.Q.obj ((ladderModel.{u, v, r} J R N).obj (op P)) ⟶
      (ladderTarget.{u, v, r, w} J R (DerivedCategory.Q.obj (colimit N))).obj
        (op (DerivedCategory.Q.obj P)) :=
  DerivedCategory.Q.map
      (colimit.desc (N ⋙ homFixed.{u, v, r} J R P)
        ((homFixed.{u, v, r} J R P).mapCocone (colimit.cocone N))) ≫
    (coefficientHomResolutionIso.{r, u, v, w} J R P (colimit N)).inv

set_option linter.unusedSectionVars false in
/-- Cohomology commutes naturally with every filtered termwise complex colimit.
The preservation predicate specifies the canonical comparison isomorphism, including
its equation on every colimit leg.
Source: Stacks 03DB (blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof: filtered colimits are exact in module sheaves. Apply this first to the
kernel-image sequences of the differential, and then to boundaries inside cycles.
This identifies cycles, boundaries and their quotient after colimiting. Each map
is induced by a kernel inclusion or quotient, so the identification is natural
in complex diagrams and agrees with cohomology of every colimit injection. -/
theorem ladder_filtered_cohomology [IsFiltered I] (q : ℤ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q) := by
  let : IsGrothendieckAbelian.{max u v r} (Modules.{u, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  infer_instance

/-- Filtered termwise colimits preserve quasi-isomorphisms and common lower bounds.
Source: Stacks 03DB (blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof: apply ladder_filtered_cohomology in each degree. A colimit of a natural
isomorphism is an isomorphism. A diagram of zero cohomology objects has zero
colimit, so a lower bound shared by all stages survives the colimit. -/
theorem ladder_filtered_consequences [IsFiltered I] :
    (∀ (K L : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (f : K ⟶ L),
      (∀ i : I, QuasiIso (f.app i)) → QuasiIso (colim.map f)) ∧
    (∀ (K : I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ) (a : ℤ),
      (∀ (i : I) (q : ℤ), q < a → IsZero
        ((HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q).obj
          (K.obj i))) →
      ∀ q : ℤ, q < a → IsZero
        ((HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q).obj
          (colimit K))) := by
  let H (q : ℤ) := HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q
  let (q : ℤ) : PreservesColimitsOfShape I (H q) :=
    ladder_filtered_cohomology.{u, v, r} J R q
  constructor
  · intro K L f hf
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let (i : I) : QuasiIso (f.app i) := hf i
    have (i : I) : IsIso ((Functor.whiskerRight f (H q)).app i) := by
      change IsIso (HomologicalComplex.homologyMap (f.app i) q)
      infer_instance
    have : IsIso (Functor.whiskerRight f (H q)) := NatIso.isIso_of_isIso_app _
    have he := (preservesColimitNatIso (J := I) (H q)).hom.naturality f
    change (H q).map (colim.map f) ≫ (preservesColimitIso (H q) L).hom =
      (preservesColimitIso (H q) K).hom ≫
        colim.map (Functor.whiskerRight f (H q)) at he
    have hm : (H q).map (colim.map f) =
        (preservesColimitIso (H q) K).hom ≫
          colim.map (Functor.whiskerRight f (H q)) ≫
          (preservesColimitIso (H q) L).inv := by
      rw [← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change IsIso ((H q).map (colim.map f))
    rw [hm]
    infer_instance
  · intro K a hK q hq
    exact (IsColimit.isZero_pt (colimit.isColimit (K ⋙ H q))
      (Functor.isZero _ (fun i ↦ hK i q hq))).of_iso
        (preservesColimitIso (H q) K)


private def ladderResolution
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    DerivedCategory.Q ⋙ RingedHomUniverses.hom.{u, v, r, w} J R
        (DerivedCategory.Q.obj P) ≅
      homFixed.{u, v, r} J R P ⋙ DerivedCategory.Q := by
  let A := Modules.{u, v, r} J R
  let : IsGrothendieckAbelian.{max u v r} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  let e : (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙
      derivedInternalHomOfUniverses.{u, v, r, w} J R ≅
      (𝟭 _).prod (coefficientHomResolution.{r, u, v} J R) ⋙
        Functor.uncurry.obj (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)) ⋙
          DerivedCategory.Q :=
    Localization.fac _
      (derivedInternalHomOfUniverses_inverts.{u, v, r, w} J R _
        (CochainComplex.toKInjectiveResolution.{max u v r} A)
        (fun F ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max u v r}
          A F).2, CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max u v r}
            A F⟩)) (DerivedCategory.Q.op.prod DerivedCategory.Q)
  exact NatIso.ofComponents
    (fun i ↦ coefficientHomResolutionIso.{r, u, v, w} J R P i)
    (by
      intro i j f
      change (derivedInternalHomOfUniverses.{u, v, r, w} J R).map
        (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map f)) ≫ e.hom.app (op P, j) =
          e.hom.app (op P, i) ≫ DerivedCategory.Q.map
            ((homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).obj
              (op P) |>.map ((coefficientHomResolution.{r, u, v} J R).map f))
      have hn := e.hom.naturality (Prod.mkHom (𝟙 (op P)) f)
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.id_obj,
        Functor.op_map, unop_id, Functor.uncurry_obj_map, Functor.id_map] at hn
      have hQ : (DerivedCategory.Q : CochainComplex (Modules.{u, v, r} J R) ℤ ⥤
          DerivedCategory (Modules.{u, v, r} J R)).map (𝟙 P) = 𝟙 _ :=
        CategoryTheory.Functor.map_id _ P
      have hH : (homComplexFunctor.{u, v, max u v r, max u v r} (R := R)).map
          (𝟙 (op P)) = 𝟙 _ := CategoryTheory.Functor.map_id _ (op P)
      simpa only [hQ, hH, op_id, NatTrans.id_app, Category.id_comp, Functor.op_obj,
        Functor.comp_obj, Functor.prod_obj, Functor.id_obj] using hn)


private def ladderResolutionIso
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
    N ⋙ DerivedCategory.Q ⋙ RingedHomUniverses.hom.{u, v, r, w} J R
        (DerivedCategory.Q.obj P) ≅
      N ⋙ homFixed.{u, v, r} J R P ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft N (ladderResolution.{u, v, r, w} J R P)

private def ladderBeta [IsFiltered I]
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) (q : ℤ) :
    colimit (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) ≅
      (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).obj
        (DerivedCategory.Q.obj ((ladderModel.{u, v, r} J R N).obj (op P))) := by
  let H := DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q
  let : PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q) :=
    ladder_filtered_cohomology.{u, v, r} J R q
  let : PreservesColimitsOfShape I (DerivedCategory.Q ⋙ H) :=
    preservesColimitsOfShape_of_natIso
      (DerivedCategory.homologyFunctorFactors (Modules.{u, v, r} J R) q).symm
  exact colim.mapIso (Functor.isoWhiskerRight (ladderResolutionIso.{u, v, r, w} J R N P) H) ≪≫
    (preservesColimitIso (DerivedCategory.Q ⋙ H) (N ⋙ homFixed.{u, v, r} J R P)).symm

@[reassoc]
private theorem ladderBeta_ι [IsFiltered I]
    (P : CochainComplex (Modules.{u, v, r} J R) ℤ) (q : ℤ) (i : I) :
    colimit.ι (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) i ≫
        (ladderBeta.{u, v, r, w} J R N P q).hom =
      (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).map
        ((coefficientHomResolutionIso.{r, u, v, w} J R P (N.obj i)).hom ≫
          DerivedCategory.Q.map (colimit.ι (N ⋙ homFixed.{u, v, r} J R P) i)) := by
  let : PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (Modules.{u, v, r} J R) (.up ℤ) q) :=
    ladder_filtered_cohomology.{u, v, r} J R q
  let : PreservesColimitsOfShape I
      (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q) :=
    preservesColimitsOfShape_of_natIso
      (DerivedCategory.homologyFunctorFactors (Modules.{u, v, r} J R) q).symm
  dsimp only [ladderBeta, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [colimit.ι_map_assoc]
  dsimp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  change _ ≫ colimit.ι ((N ⋙ homFixed.{u, v, r} J R P) ⋙
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q)) i ≫
      (preservesColimitIso _ (N ⋙ homFixed.{u, v, r} J R P)).inv = _
  rw [ι_preservesColimitIso_inv]
  simp only [ladderResolutionIso,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ladderResolution,
    NatIso.ofComponents_hom_app, Functor.map_comp, Functor.comp_map]

/-- The canonical model cocone descends in the source, and its cohomology is the
vertical colimit map under the canonical cohomology-colimit identification.
The witnesses F and e present the localization of ladderModel; alpha is fixed by
its displayed equation on every complex, and beta is fixed on every colimit leg.
Thus this asserts a normalized canonical comparison, not a chosen unrelated map.
Source: Stacks 03DB, 0A95 and 08JC
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof:
1. The preceding filtered-colimit results identify cohomology of a termwise
   colimit with the colimit of cohomology, naturally on its injections.
2. Source quasi-isomorphisms induce quasi-isomorphisms into each K-injective
   target (lem-pur-rhom-well-defined-universes). The filtered colimit does too.
   Localize this contravariant functor to obtain F and its factorization e.
3. Precomposition commutes with target postcomposition on every Hom component.
   Therefore the canonical cocone map is a natural transformation of the
   unlocalized functors. Localize it to obtain alpha. Naturality for inverted
   source quasi-isomorphisms follows by composing with their inverse maps.
4. Apply cohomology to the strict colimit legs and the fixed resolution
   comparison. The resulting cocone gives beta, an isomorphism by step 1.
   Testing the equality with H(alpha) on each colimit injection proves it.
   No colimit of K-injectives is asserted to be K-injective. -/
theorem ladder_comparison [IsFiltered I] :
    ∃ (F : (DerivedCategory (Modules.{u, v, r} J R))ᵒᵖ ⥤
        DerivedCategory (Modules.{u, v, r} J R))
      (e : DerivedCategory.Q.op ⋙ F ≅ ladderModel.{u, v, r} J R N ⋙ DerivedCategory.Q)
      (alpha : F ⟶ ladderTarget.{u, v, r, w} J R (DerivedCategory.Q.obj (colimit N))),
      (∀ P : CochainComplex (Modules.{u, v, r} J R) ℤ,
        e.hom.app (op P) ≫ ladderStrictAlpha.{u, v, r, w} J R N P =
          alpha.app (op (DerivedCategory.Q.obj P))) ∧
      (∀ (P : CochainComplex (Modules.{u, v, r} J R) ℤ) (q : ℤ),
        ∃ beta : colimit (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) ≅
          (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).obj
            (DerivedCategory.Q.obj ((ladderModel.{u, v, r} J R N).obj (op P))),
          (∀ i : I,
            colimit.ι (ladderDiagram.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) i ≫
                beta.hom =
              (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).map
                ((coefficientHomResolutionIso.{r, u, v, w} J R P (N.obj i)).hom ≫
                  DerivedCategory.Q.map (colimit.ι (N ⋙ homFixed.{u, v, r} J R P) i))) ∧
          beta.hom ≫
              (DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q).map
                (e.inv.app (op P) ≫ alpha.app (op (DerivedCategory.Q.obj P))) =
            ladderVertical.{u, v, r, w} J R N (DerivedCategory.Q.obj P) q) := by
  obtain ⟨G, rho, alpha, t, hα, _⟩ :=
    CategoryTheory.RingedHomColimitTransport.source_transport.{u, v, r, w} J R (I := I)
  let ev := (evaluation (I ⥤ CochainComplex (Modules.{u, v, r} J R) ℤ)
    (DerivedCategory (Modules.{u, v, r} J R))).obj N
  let F := G ⋙ ev
  let e : DerivedCategory.Q.op ⋙ F ≅ ladderModel.{u, v, r} J R N ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight rho ev
  let a : F ⟶ ladderTarget.{u, v, r, w} J R (DerivedCategory.Q.obj (colimit N)) :=
    Functor.whiskerRight alpha ev
  have ha (P : CochainComplex (Modules.{u, v, r} J R) ℤ) :
      e.hom.app (op P) ≫ ladderStrictAlpha.{u, v, r, w} J R N P =
        a.app (op (DerivedCategory.Q.obj P)) := by
    exact (hα P N).symm
  refine ⟨F, e, a, ha, ?_⟩
  intro P q
  refine ⟨ladderBeta.{u, v, r, w} J R N P q,
    ladderBeta_ι.{u, v, r, w} J R N P q, ?_⟩
  have hαP : e.inv.app (op P) ≫ a.app (op (DerivedCategory.Q.obj P)) =
      ladderStrictAlpha.{u, v, r, w} J R N P := by
    rw [← ha P, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  rw [hαP]
  apply colimit.hom_ext
  intro i
  rw [ladderBeta_ι_assoc, ← Functor.map_comp]
  change _ = colimit.ι ((N ⋙ DerivedCategory.Q) ⋙
    RingedHomUniverses.hom.{u, v, r, w} J R (DerivedCategory.Q.obj P) ⋙
      DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) q) i ≫ _
  rw [ladderVertical, colimit.ι_desc]
  have hn := (ladderResolution.{u, v, r, w} J R P).hom.naturality (colimit.ι N i)
  have hc :
      ((coefficientHomResolutionIso.{r, u, v, w} J R P (N.obj i)).hom ≫
          DerivedCategory.Q.map (colimit.ι (N ⋙ homFixed.{u, v, r} J R P) i)) ≫
        ladderStrictAlpha.{u, v, r, w} J R N P =
      (RingedHomUniverses.hom.{u, v, r, w} J R (DerivedCategory.Q.obj P)).map
        (DerivedCategory.Q.map (colimit.ι N i)) := by
    dsimp only [ladderStrictAlpha]
    rw [Category.assoc, ← DerivedCategory.Q.map_comp_assoc, colimit.ι_desc]
    have hn' := congrArg (fun k ↦ k ≫
      (coefficientHomResolutionIso.{r, u, v, w} J R P (colimit N)).inv) hn.symm
    simpa only [ladderResolution, NatIso.ofComponents_hom_app, Functor.comp_map,
      Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Functor.mapCocone_ι_app, colimit.cocone_ι] using hn'
  rw [hc]
  rfl


private theorem ladderVertical_naturality
    {A B : DerivedCategory (Modules.{u, v, r} J R) ⥤ Modules.{u, v, r} J R}
    (f : A ⟶ B) :
    colim.map (Functor.whiskerLeft (N ⋙ DerivedCategory.Q) f) ≫
        colimit.desc _ (B.mapCocone (DerivedCategory.Q.mapCocone (colimit.cocone N))) =
      colimit.desc _ (A.mapCocone (DerivedCategory.Q.mapCocone (colimit.cocone N))) ≫
        f.app (DerivedCategory.Q.obj (colimit N)) := by
  apply colimit.hom_ext
  intro i
  rw [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
  exact (f.naturality (DerivedCategory.Q.map (colimit.ι N i))).symm

set_option linter.unusedSectionVars false in
private theorem ladderColim_exact [IsFiltered I]
    {A B D : I ⥤ Modules.{u, v, r} J R} (f : A ⟶ B) (g : B ⟶ D)
    (h : ∀ i : I, ∃ z : f.app i ≫ g.app i = 0,
      (ShortComplex.mk _ _ z).Exact) :
    ∃ z : colim.map f ≫ colim.map g = 0, (ShortComplex.mk _ _ z).Exact := by
  let : IsGrothendieckAbelian.{max u v r} (Modules.{u, v, r} J R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, v, r}
      J R).1
  have z : f ≫ g = 0 := by
    apply NatTrans.ext
    exact funext (fun i ↦ (h i).choose)
  let K := ShortComplex.mk f g z
  have hK : K.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology]
    apply Functor.isZero
    intro i
    exact ((ShortComplex.exact_iff_isZero_homology _).mp (h i).choose_spec).of_iso
      (K.mapHomologyIso ((evaluation I (Modules.{u, v, r} J R)).obj i)).symm
  exact ⟨_, hK.map colim⟩

private theorem ladderRow_exact
    (T : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
    (hT : T ∈ distTriang (DerivedCategory (Modules.{u, v, r} J R)))
    (M : DerivedCategory (Modules.{u, v, r} J R)) (q : ℤ) :
    (∃ h : (ladderBoundary.{u, v, r, w} J R T q).app M ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app M = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h : (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app M ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₁ q).app M = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h : (ladderPrecomp.{u, v, r, w} J R T.mor₁ (q - 1)).app M ≫
        (ladderBoundary.{u, v, r, w} J R T q).app M = 0,
      (ShortComplex.mk _ _ h).Exact) := by
  let F := Prod.sectL _ M ⋙ derivedInternalHomOfUniverses.{u, v, r, w} J R
  obtain ⟨S, hS, hpos, hneg⟩ := signedDerivedInternalHom_exact.{u, v, r, w} J R M
  let := S
  let := hS
  let H (n : ℤ) := DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) n
  let c : H (q - 1) ≅ shiftFunctor _ (-1 : ℤ) ⋙ H q :=
    ((DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) 0).shiftIso
      (-1) q (q - 1) (by omega)).symm
  let e (X : DerivedCategory (Modules.{u, v, r} J R)) :
      (H (q - 1)).obj (F.obj (op X)) ≅ (H q).obj (F.obj (op (X⟦(1 : ℤ)⟧))) :=
    c.app (F.obj (op X)) ≪≫
      (H q).mapIso ((F.commShiftIso (-1 : ℤ)).symm.app (op X))
  have he (X) : (e X).hom =
      (((DerivedCategory.homologyFunctor (Modules.{u, v, r} J R) 0).shiftIso
        (-1) q (q - 1) (by omega)).inv.app (F.obj (op X))) ≫
        (H q).map ((RingedHomUniverses.sourceShift.{u, v, r, w} J R X 1).hom.app M) := by
    dsimp only [e, c, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Functor.mapIso_hom]
    rw [hneg]
  have hb : (ladderBoundary.{u, v, r, w} J R T q).app M =
      (e T.obj₁).hom ≫ (H q).map (F.map T.mor₃.op) := by
    rw [he]
    rfl
  have hn {X Y : DerivedCategory (Modules.{u, v, r} J R)} (f : X ⟶ Y) :
      (H (q - 1)).map (F.map f.op) ≫ (e X).hom =
        (e Y).hom ≫ (H q).map (F.map (f⟦(1 : ℤ)⟧').op) := by
    have hn₁ : (F.map f.op)⟦(-1 : ℤ)⟧' ≫
        (F.commShiftIso (-1 : ℤ)).inv.app (op X) =
      (F.commShiftIso (-1 : ℤ)).inv.app (op Y) ≫
        F.map (f⟦(1 : ℤ)⟧').op :=
      (F.commShiftIso (-1 : ℤ)).inv.naturality f.op
    have hn₂ := c.hom.naturality (F.map f.op)
    dsimp only [Functor.comp_map] at hn₂
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [← Category.assoc, hn₂]
    simp only [Category.assoc, ← (H q).map_comp]
    rw [hn₁]
  let hrow (U : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
      (hU : U ∈ distTriang (DerivedCategory (Modules.{u, v, r} J R))) (n : ℤ) :=
    (F ⋙ H n).map_distinguished_op_exact U hU
  have h₁ := hrow T.rotate (rot_of_distTriang T hT) q
  have h₂ := hrow T hT q
  have h₃ := hrow T.rotate.rotate (rot_of_distTriang _ (rot_of_distTriang T hT)) q
  constructor
  · have hz : (ladderBoundary.{u, v, r, w} J R T q).app M ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app M = 0 := by
      rw [hb, Category.assoc]
      change (e T.obj₁).hom ≫ ((H q).map (F.map T.mor₃.op) ≫
        (H q).map (F.map T.mor₂.op)) = 0
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp,
        comp_distTriang_mor_zero₂₃ T hT, op_zero, F.map_zero, (H q).map_zero,
        comp_zero]
    refine ⟨hz, ShortComplex.exact_of_iso ?_ h₁⟩
    exact ShortComplex.isoMk (e T.obj₁).symm (Iso.refl _) (Iso.refl _)
      (by simp [hb]) (by simp [ladderPrecomp, F, H])
  constructor
  · exact ⟨_, h₂⟩
  · have hz : (ladderPrecomp.{u, v, r, w} J R T.mor₁ (q - 1)).app M ≫
        (ladderBoundary.{u, v, r, w} J R T q).app M = 0 := by
      rw [hb, ← Category.assoc]
      change ((H (q - 1)).map (F.map T.mor₁.op) ≫ (e T.obj₁).hom) ≫ _ = 0
      rw [hn, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
        comp_distTriang_mor_zero₃₁ T hT, op_zero, F.map_zero, (H q).map_zero,
        comp_zero]
    refine ⟨hz, ShortComplex.exact_of_iso ?_ h₃⟩
    refine ShortComplex.isoMk (-(e T.obj₂).symm) (e T.obj₁).symm (Iso.refl _) ?_ ?_
    · have hc : (-(e T.obj₂).inv) ≫ (H (q - 1)).map (F.map T.mor₁.op) =
          (H q).map (F.map (-T.mor₁⟦(1 : ℤ)⟧').op) ≫ (e T.obj₁).inv := by
        simp only [op_neg, F.map_neg, (H q).map_neg, Preadditive.neg_comp, neg_inj]
        rw [← cancel_mono (e T.obj₁).hom]
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using
            congrArg (fun k ↦ (e T.obj₂).inv ≫ k) (hn T.mor₁)
      simpa only [Preadditive.neg_iso_hom, Iso.symm_hom, ladderPrecomp,
        Functor.whiskerRight_app, ShortComplex.map, ShortComplex.op,
        shortComplexOfDistTriangle, Triangle.rotate, Triangle.mk, Functor.comp_map,
        F, H, Functor.curry_obj_map_app, Prod.sectL_map] using hc
    · simp [hb]

/-- Both cohomology rows are exact and all squares commute, including the signed
connecting square. The three exact spots in every degree give the entire infinite
ladder, including the preceding arrow in degree q-1 and the following one in q+1.
Source: Stacks 03DB, 08JC and 05RS
(blueprint: lem-sfb-rhom-colimit-cohomology-ladder).
Proof:
1. Form termwise colimits of complexes degreewise. The cocone equations show
   that their differential squares to zero and give the complex colimit property.
2. Exact filtered colimits preserve cycles, boundaries and their quotient by
   applying exactness successively to the kernel-image short exact sequences.
3. Hence filtered colimits preserve quasi-isomorphisms and a common lower bound.
4. Use the fixed functorial K-injective targets. Precomposition and target
   postcomposition commute; quasi-isomorphism invariance lets the Hom functors
   and their cocone comparison descend to every derived source morphism.
5. The signed source shift reindexes components by p to p-1 and multiplies
   Hom degree n by (-1)^n. Substitution in the Hom differential verifies it is
   a chain isomorphism. This formula is independent of the target, so commutes
   with every target transition and the colimit cocone. No product is commuted
   with a colimit here.
6. Internal Hom sends the source triangle contravariantly to a distinguished
   triangle (lem-weil-pbc-ringed-internal-hom-exact-restriction). Derived
   cohomology gives its exact sequence (lem-sf-derived-homology-long-exact),
   with the boundary normalized by the signed source shift of step 5.
7. Naturality of precomposition gives the ordinary squares. Naturality of the
   signed shift gives the connecting square too, including for inverted source
   quasi-isomorphisms (lem-weil-pbc-derived-cohomology-ladder).
8. Exact filtered colimits give exactness at each spot of the first row.
   Each square commutes after composition with every colimit injection, hence
   commutes by the universal property. ladder_comparison identifies these
   vertical arrows with H^q(alpha). Vary q to obtain the complete ladder.
There is no boundedness, continuity or constructibility hypothesis. -/
theorem rhom_colimit_cohomology_ladder [IsFiltered I]
    (T : Triangle (DerivedCategory (Modules.{u, v, r} J R)))
    (hT : T ∈ distTriang (DerivedCategory (Modules.{u, v, r} J R))) (q : ℤ) :
    (∃ h :
      ladderColimBoundary.{u, v, r, w} J R N T q ≫
        ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q ≫
        ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ (q - 1) ≫
        ladderColimBoundary.{u, v, r, w} J R N T q = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderBoundary.{u, v, r, w} J R T q).app (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₁ q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (∃ h :
      (ladderPrecomp.{u, v, r, w} J R T.mor₁ (q - 1)).app
      (DerivedCategory.Q.obj (colimit N)) ≫
        (ladderBoundary.{u, v, r, w} J R T q).app (DerivedCategory.Q.obj (colimit N)) = 0,
      (ShortComplex.mk _ _ h).Exact) ∧
    (ladderColimPrecomp.{u, v, r, w} J R N T.mor₂ q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₂ q =
      ladderVertical.{u, v, r, w} J R N T.obj₃ q ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₂ q).app
          (DerivedCategory.Q.obj (colimit N))) ∧
    (ladderColimPrecomp.{u, v, r, w} J R N T.mor₁ q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₁ q =
      ladderVertical.{u, v, r, w} J R N T.obj₂ q ≫
        (ladderPrecomp.{u, v, r, w} J R T.mor₁ q).app
          (DerivedCategory.Q.obj (colimit N))) ∧
    (ladderColimBoundary.{u, v, r, w} J R N T q ≫
        ladderVertical.{u, v, r, w} J R N T.obj₃ q =
      ladderVertical.{u, v, r, w} J R N T.obj₁ (q - 1) ≫
        (ladderBoundary.{u, v, r, w} J R T q).app
          (DerivedCategory.Q.obj (colimit N))) := by
  have hr (M : DerivedCategory (Modules.{u, v, r} J R)) :=
    ladderRow_exact.{u, v, r, w} J R T hT M q
  refine ⟨?_, ?_, ?_, (hr _).1, (hr _).2.1, (hr _).2.2, ?_, ?_, ?_⟩
  · exact ladderColim_exact.{u, v, r} J R _ _
      (fun i ↦ (hr (DerivedCategory.Q.obj (N.obj i))).1)
  · exact ladderColim_exact.{u, v, r} J R _ _
      (fun i ↦ (hr (DerivedCategory.Q.obj (N.obj i))).2.1)
  · exact ladderColim_exact.{u, v, r} J R _ _
      (fun i ↦ (hr (DerivedCategory.Q.obj (N.obj i))).2.2)
  · exact ladderVertical_naturality.{u, v, r, w} J R N
      (ladderPrecomp.{u, v, r, w} J R T.mor₂ q)
  · exact ladderVertical_naturality.{u, v, r, w} J R N
      (ladderPrecomp.{u, v, r, w} J R T.mor₁ q)
  · exact ladderVertical_naturality.{u, v, r, w} J R N
      (ladderBoundary.{u, v, r, w} J R T q)

end WeilConjectures.SfbHomFilteredColimit
