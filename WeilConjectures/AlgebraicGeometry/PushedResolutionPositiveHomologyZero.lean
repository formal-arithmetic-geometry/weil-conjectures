/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.ObjectCohomologyPresheafResolution
import Mathlib.CategoryTheory.Sites.LocallyBijective
/-!
# Positive homology of a continuously pushed resolution

## References

* Stacks Project, Cohomology on Sites, Tags 072W and 0733.
-/

@[expose] public section
universe u v w r t
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction
private theorem locallyInjective_zero_ulift_iff
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsLocallyInjective J
        (0 : P ⋙ AddCommGrpCat.uliftFunctor.{r, w} ⟶
          P ⋙ AddCommGrpCat.uliftFunctor.{r, w}) ↔
      Presheaf.IsLocallyInjective J (0 : P ⟶ P) := by
  constructor
  · intro h
    constructor
    intro V x y _
    have hS := h.equalizerSieve_mem (X := V) (ULift.up x) (ULift.up y) (by simp)
    convert hS using 1
    ext U f
    change P.map f.op x = P.map f.op y ↔
      ULift.up (P.map f.op x) = ULift.up (P.map f.op y)
    exact ULift.up_inj.symm
  · intro h
    constructor
    intro V x y _
    have hS := h.equalizerSieve_mem (X := V) x.down y.down (by simp)
    convert hS using 1
    ext U f
    change ULift.up (P.map f.op x.down) = ULift.up (P.map f.op y.down) ↔
      P.map f.op x.down = P.map f.op y.down
    exact ULift.up_inj

private theorem locallyInjective_zero_of_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (e : P ≅ Q)
    (h : Presheaf.IsLocallyInjective J (0 : P ⟶ P)) :
    Presheaf.IsLocallyInjective J (0 : Q ⟶ Q) := by
  have : Presheaf.IsLocallyInjective J (e.inv ≫ (0 : P ⟶ P) ≫ e.hom) :=
    inferInstance
  simpa using this

/-- Positive homology of the pushed injective resolution is zero, under the local-vanishing
(acyclicity) hypothesis (Stacks, Tags 072W and 0733). -/
theorem pushed_resolution_positive_homology_isZero
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{t} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvan : ∀ q : ℕ, 0 < q →
      Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.carrier)
        (0 : i.op ⋙ Sheaf.cohomologyPresheaf F q ⟶
          i.op ⋙ Sheaf.cohomologyPresheaf F q)) :
    ∀ (I : InjectiveResolution F) (n : ℕ), 0 < n →
      IsZero (((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex |>.homology n) := by
  intro I n hn
  let J := Opens.grothendieckTopology X.carrier
  let P := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J X.smallEtaleTopology
  let K := (P.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := ((sheafToPresheaf J AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℕ)).obj K
  let M := ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let T := (Functor.whiskeringLeft X.Opensᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj i.op
  let eT : i.op ⋙ M.homology n ≅ L.homology n := ((M.sc n).mapHomologyIso T).symm
  obtain ⟨e⟩ := objectCohomologyPresheaf_resolution X.smallEtaleTopology F I n
  let e' := Functor.isoWhiskerLeft i.op e
  -- Local vanishing is invariant under the universe lifts used by Ext.
  have hP := (locallyInjective_zero_ulift_iff.{u + 1, u + 1, t, u + 2}
    J (i.op ⋙ F.cohomologyPresheaf n)).2
    (hvan n hn)
  have hQ := locallyInjective_zero_of_iso J e' hP
  have hM := (locallyInjective_zero_ulift_iff.{u + 1, u + 1, u + 1, max (u + 2) t}
    J (i.op ⋙ M.homology n)).1 hQ
  have hL := locallyInjective_zero_of_iso J eT hM
  -- A locally injective zero map sheafifies to a zero monomorphism.
  let a := presheafToSheaf J AddCommGrpCat.{u + 1}
  have : a.Additive := Functor.additive_of_preserves_binary_products _
  have : Sheaf.IsLocallyInjective (a.map (0 : L.homology n ⟶ L.homology n)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).2 hL
  have : Mono (a.map (0 : L.homology n ⟶ L.homology n)) :=
    Sheaf.mono_of_isLocallyInjective _
  have hZ : IsZero (a.obj (L.homology n)) :=
    IsZero.of_mono_eq_zero (a.map (0 : L.homology n ⟶ L.homology n)) (a.map_zero _ _)
  -- Sheafification recovers K, and its exactness commutes with homology.
  let eK : (a.mapHomologicalComplex (.up ℕ)).obj L ≅ K :=
    (Functor.mapHomologicalComplexCompIso
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm (.up ℕ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).app K
  let eH := ((L.sc n).mapHomologyIso a).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) n).mapIso eK
  exact hZ.of_iso eH.symm
