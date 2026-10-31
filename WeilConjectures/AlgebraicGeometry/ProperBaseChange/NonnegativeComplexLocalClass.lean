/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import all WeilConjectures.AlgebraicGeometry.Section.SectionCohomologyCycleFormula
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryLocalClassCycles

/-! # Ordinary local classes and extension by zero

Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images.
(blueprint: lem-weil-pbc-nonnegative-complex-local-class).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

set_option maxHeartbeats 800000 in
-- Transport cycles through extension and the two section forgetful functors.
/-- The module cocycle class map is the abelian sheafification class map, compatibly
with extension by zero and exact evaluation. No derived category or acyclicity
hypothesis is used.
Source: Stacks Project, Cohomology, Tag 01E4, lemma-describe-higher-direct-images.
(blueprint: lem-weil-pbc-nonnegative-complex-local-class).

Proof: Precompose both sides with the epimorphism from cycles to the cohomology
of the section complex. The module-sheafification adjunction identifies the left
side with the map from sections of the kernel to the cokernel defining the
cohomology sheaf. For the right side, apply the abelian-sheafification adjunction
and commute its exact left adjoint with homology. The counit and the exact
forgetful functor from module sheaves to abelian sheaves identify this with the
same kernel-to-cokernel map. The two kernel comparisons agree because their
composites with the kernel inclusion agree. Extension by zero identifies these
kernels using extendCyclesIso and these quotients using extendHomologyIso;
mapExtendIso gives the degreewise functor comparison. Its compatibility with
composition follows degreewise (identity on nonnegative indices and uniqueness
of morphisms between zero objects on the remaining indices). Exact evaluation
commutes with the kernel and quotient constructions through mapHomologyIso.
Cancel the cycle epimorphism. This includes degree zero, where the incoming
differential is zero on both complexes, and empty opens and zero complexes. -/
theorem nonnegativeComplex_localClass {X Y : Scheme.{u}}
    (D : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace)) [D.Additive]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ)
    (q : ℕ) (V : Y.Opens) :
    let P := D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace
    letI : P.Additive := inferInstanceAs
      (D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace).Additive
    let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let Γ := P ⋙ E
    letI : Γ.Additive := inferInstanceAs (P ⋙ E).Additive
    let B := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
    let a :=
      (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
        ComplexShape.embeddingUpNat (j := q) rfl).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        (q : ℤ)).mapIso (L.mapExtendIso ComplexShape.embeddingUpNat Γ).symm ≪≫
      (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.extend ComplexShape.embeddingUpNat)).sc (q : ℤ)).mapHomologyIso E
    let J := (D.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.extend ComplexShape.embeddingUpNat)
    let d :=
      (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) (q : ℤ)).mapIso
        (L.mapExtendIso ComplexShape.embeddingUpNat D) ≪≫
      B.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj B).sc q).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙ E)).hom ≫
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          (sectionCohomologyTheta B q)).app (op V) =
      a.hom ≫
        ((sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          (((RingedSpace.localAbelianSections Y.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J |>.homology (q : ℤ))).app (op V) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (RingedSpace.localSectionComplexSheafificationIso Y.toRingedSpace (q : ℤ) J).hom).app
            (op V) ≫
        ((RingedSpace.localAbelianSections Y.toRingedSpace).map d.hom).app (op V) := by
  dsimp only
  let F := RingedSpace.localAbelianSections Y.toRingedSpace
  let P := D ⋙ F
  let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let Γ := P ⋙ E
  let B := (D.mapHomologicalComplex (.up ℕ)).obj L
  let I := L.extend ComplexShape.embeddingUpNat
  let J := (D.mapHomologicalComplex (.up ℤ)).obj I
  let A := (P.mapHomologicalComplex (.up ℤ)).obj I
  let C := (Γ.mapHomologicalComplex (.up ℕ)).obj L
  let a :=
    (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      (q : ℤ)).mapIso (L.mapExtendIso ComplexShape.embeddingUpNat Γ).symm ≪≫
    (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.extend ComplexShape.embeddingUpNat)).sc (q : ℤ)).mapHomologyIso E
  let d :=
    (HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) (q : ℤ)).mapIso
      (L.mapExtendIso ComplexShape.embeddingUpNat D) ≪≫
    B.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
  let z := (C.extendCyclesIso ComplexShape.embeddingUpNat (j := q) rfl).inv ≫
    HomologicalComplex.cyclesMap (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv
      (q : ℤ) ≫ ((A.sc (q : ℤ)).mapCyclesIso E).hom
  have hπ : C.homologyπ q ≫ a.hom = z ≫ E.map (A.homologyπ (q : ℤ)) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    erw [HomologicalComplex.homologyπ_extendHomologyIso_inv_assoc,
      HomologicalComplex.homologyπ_naturality_assoc]
    erw [homologyπ_mapHomologyIso_hom E (A.sc (q : ℤ))]
    rfl
  have hz : z ≫ E.map (A.iCycles (q : ℤ)) =
      C.iCycles q ≫ (C.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv.f (q : ℤ) := by
    dsimp only [z]
    simp only [Category.assoc]
    erw [ShortComplex.mapCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.extendCyclesIso_inv_iCycles_assoc]
  let zD := HomologicalComplex.cyclesMap
      (L.mapExtendIso ComplexShape.embeddingUpNat D).hom (q : ℤ) ≫
    (B.extendCyclesIso ComplexShape.embeddingUpNat (j := q) rfl).hom
  have hdπ : J.homologyπ (q : ℤ) ≫ d.hom = zD ≫ B.homologyπ q := by
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom]
    erw [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_extendHomologyIso_hom]
    rfl
  have hdz : zD ≫ B.iCycles q = J.iCycles (q : ℤ) ≫
      (L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ) ≫
      (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom := by
    dsimp only [zD]
    erw [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i_assoc]
  let k := ((J.sc (q : ℤ)).map F).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (J.sc (q : ℤ)).cyclesIsKernel F) |>.inv
  let M := (B.sc q).map (SheafOfModules.forget Y.ringCatSheaf)
  let E' := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙ E
  let kM := M.isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (B.sc q).cyclesIsKernel
      (SheafOfModules.forget Y.ringCatSheaf)) |>.inv
  let zM := (M.mapCyclesIso E').hom ≫ E'.map kM
  have hzM : zM ≫ E.map (F.map (B.iCycles q)) = C.iCycles q := by
    change ((M.mapCyclesIso E').hom ≫ E'.map kM) ≫
      E'.map ((SheafOfModules.forget Y.ringCatSheaf).map (B.iCycles q)) = _
    rw [Category.assoc, ← E'.map_comp]
    erw [M.isoCyclesOfIsLimit_inv_ι]
    exact M.mapCyclesIso_hom_iCycles E'
  have hcomponent :
      (C.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv.f (q : ℤ) ≫
        E.map (F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ))) ≫
        E.map (F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) =
      𝟙 (C.X q) := by
    have hr : ComplexShape.embeddingUpNat.r (q : ℤ) = some q :=
      ComplexShape.embeddingUpNat.r_f q
    dsimp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
    erw [HomologicalComplex.mapExtendX_hom_eq L Γ hr,
      HomologicalComplex.mapExtendX_hom_eq L D hr]
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans, eqToHom_refl]
  have hcycles : z ≫ E.map k ≫ E.map (F.map zD) = zM := by
    apply (cancel_mono (E.map (F.map (B.iCycles q)))).1
    have hh : k ≫ F.map zD ≫ F.map (B.iCycles q) =
        A.iCycles (q : ℤ) ≫
          F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ)) ≫
          F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom := by
      erw [← F.map_comp zD (B.iCycles q), hdz, F.map_comp, F.map_comp]
      erw [← Category.assoc k (F.map (J.iCycles (q : ℤ))),
        ((J.sc (q : ℤ)).map F).isoCyclesOfIsLimit_inv_ι]
      rfl
    have hhE := congrArg E.map hh
    simp only [Functor.map_comp] at hhE
    calc
      _ = z ≫ E.map (A.iCycles (q : ℤ)) ≫
          E.map (F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ))) ≫
          E.map (F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) := by
        simpa only [Category.assoc] using congrArg (fun m ↦ z ≫ m) hhE
      _ = C.iCycles q := by
        erw [← Category.assoc z (E.map (A.iCycles (q : ℤ))), hz]
        simp only [Category.assoc, hcomponent, Category.comp_id]
      _ = _ := hzM.symm
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
    (A.homology (q : ℤ))
  let c := (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
    (RingedSpace.localSectionComplexSheafificationIso Y.toRingedSpace (q : ℤ) J).hom
  have hh : E.map (A.homologyπ (q : ℤ)) ≫ E.map η ≫ E.map c =
      E.map k ≫ E.map (F.map (J.homologyπ (q : ℤ))) := by
    have h := congrArg E.map (ordinaryLocalClass_cycles J (q : ℤ))
    change E.map (A.homologyπ (q : ℤ) ≫ η ≫ c) =
      E.map (k ≫ F.map (J.homologyπ (q : ℤ))) at h
    simpa only [Functor.map_comp] using h
  apply (cancel_epi (C.homologyπ q)).1
  change C.homologyπ q ≫
      ((M.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta B q)) =
    C.homologyπ q ≫ (a.hom ≫ E.map η ≫ E.map c ≫ E.map (F.map d.hom))
  have hleft := section_comparison_cycles B q V
  change C.homologyπ q ≫ (M.mapHomologyIso E').hom ≫
      E'.map (sectionCohomologyTheta B q) = zM ≫ E.map (F.map (B.homologyπ q)) at hleft
  erw [hleft, reassoc_of% hπ, reassoc_of% hh]
  erw [← E.map_comp (F.map (J.homologyπ (q : ℤ))) (F.map d.hom),
    ← F.map_comp (J.homologyπ (q : ℤ)) d.hom, hdπ,
    F.map_comp zD (B.homologyπ q), E.map_comp (F.map zD) (F.map (B.homologyπ q))]
  simpa only [Category.assoc] using
    congrArg (fun z' ↦ z' ≫ E.map (F.map (B.homologyπ q))) hcycles.symm

end AlgebraicGeometry
