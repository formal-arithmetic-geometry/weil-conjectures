/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.DerivedSingleOpenLocus
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-! # Pullback cohomology on a locus with one locally free cohomology sheaf

## References

* Stacks Project, Tag 0B9S
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Derived pullback of a flat sheaf in one degree is ordinary pullback in that degree.

(Stacks, Tags 06YD and 06YJ) -/
private theorem nonempty_derivedPullback_flat_single_iso
    {T T' : Scheme.{u}} (g : T' ⟶ T)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T'.toRingedSpace))]
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) (n : ℤ)
    (hM : SheafOfModules.IsFlat M) :
    Nonempty ((AlgebraicGeometry.derivedPullback g).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj M) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) n).obj
          ((Modules.pullback g).obj M)) := by
  let A := SheafOfModules.{u} (moduleRings T.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings T'.toRingedSpace)
  let K := (CochainComplex.singleFunctor A n).obj M
  let := SheafOfModules.monoidalCategory T.sheaf
  obtain ⟨⟨hpreadd⟩, _⟩ := SheafOfModules.tensorClosed T.sheaf
  let := hpreadd
  have hbounded : ∃ b : ℤ, ∀ q : ℤ, b < q → IsZero (K.X q) := by
    refine ⟨n, fun q hq ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hflat : ∀ q : ℤ, SheafOfModules.IsFlat (K.X q) := by
    intro q
    by_cases hq : q = n
    · subst q
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso e.symm) hM
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)).2
  obtain ⟨F, hF, _, hFadd, _, _, ⟨e, _⟩⟩ :=
    flatComplexDerivedPullback g K hbounded hflat
  let := hFadd
  let eFM : F.obj M ≅ (Modules.pullback g).obj M :=
    eqToIso (hF M) ≪≫
      ((Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction g)).app M
  refine ⟨(AlgebraicGeometry.derivedPullback g).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ A n).app M ≪≫
      ((DerivedCategory.quotientCompQhIso A).app K).symm) ≪≫ e.symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ B n).app (F.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor B n).mapIso eFM⟩

/-- On a locus where a connective derived object has locally free cohomology in one
nonnegative degree only, derived pullback cohomology is ordinary pullback cohomology.

(Stacks, Tag 0B9S) -/
theorem nonempty_homology_derivedPullback_iso_of_locally_single
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{u}} (g : T' ⟶ T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ Set.range g.base, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) i).obj
        ((AlgebraicGeometry.derivedPullback g).obj E) ≅ (Modules.pullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E)) := by
  obtain ⟨W, hW, hflat, ⟨eW⟩⟩ :=
    exists_flat_single_open_locus (Set.range g.base) E i hneg hloc
  let f : T' ⟶ W.toScheme := IsOpenImmersion.lift W.ι g (by simpa using hW)
  have hfac : f ≫ W.ι = g := IsOpenImmersion.lift_fac W.ι g _
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition
  obtain ⟨eS⟩ := nonempty_derivedPullback_flat_single_iso f _ i hflat
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) (i : ℤ)
  refine ⟨H.mapIso
    ((eqToIso (congrArg (fun k ↦ (AlgebraicGeometry.derivedPullback k).obj E) hfac)).symm ≪≫
      ((c f W.ι).app E).symm ≪≫ (AlgebraicGeometry.derivedPullback f).mapIso eW ≪≫ eS) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (i : ℤ)).app _ ≪≫
    (Modules.pullback f).mapIso ((Modules.restrictFunctorIsoPullback W.ι).app _) ≪≫
    (Modules.pullbackComp f W.ι).app _ ≪≫ ?_⟩
  exact eqToIso (congrArg (fun k ↦ (Modules.pullback k).obj
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E)) hfac)

end AlgebraicGeometry.Scheme.Modules
