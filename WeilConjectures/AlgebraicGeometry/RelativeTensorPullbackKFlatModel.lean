/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFunctor
import WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackComplexComparison
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The relative tensor comparison on K-flat representatives

Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE).
(blueprint: lem-pc-relative-tensor-pullback-kflat-model)
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme

noncomputable local instance modelModuleTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option profiler true in
-- Derived and ordinary homology comparisons involve several nested functors.
/-- On K-flat representatives in both source module categories, the balanced tensor
identity computes the underlying homology of derived tensor with derived pullback.
This is only the representative calculation: no replacement of the restricted first
complex by an arbitrary K-flat resolution is asserted here.
Source: Stacks Project, Cohomology, Lemma 20.27.4 (Tag 08DE), proof.

Proof: the K-flat counit for derived pullback identifies Lf*(Q(L)) with Q(f*L).
The K-flat first-factor comparison then identifies Q(A) tensor Q(f*L) with
Q(Tot(A tensor f*L)). In each bidegree the balanced tensor isomorphism
A^p tensor over O_X (O_X tensor over f-inverse O_S f-inverse L^q)
is A^p restricted to f-inverse O_S tensor f-inverse L^q. Its naturality
commutes with both differentials; the same sign (-1)^p occurs on both sides.
Restriction of scalars preserves coproducts, so these summand identifications
induce an isomorphism of total complexes. Exact restriction of scalars commutes
with homology, and forgetting to abelian sheaves removes the scalar action.
Compose these identifications with the localization homology comparison.
The construction is valid for unbounded complexes and empty schemes; it does not
require the restriction of A to be K-flat.
(blueprint: lem-pc-relative-tensor-pullback-kflat-model) -/
theorem relativeTensorPullback_kFlat_model
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (A : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hA : CochainComplex.IsKFlatTensor (R := X.sheaf) A)
    (L : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := S.sheaf) L) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (DerivedCategory.Q.obj A ⊗ (derivedPullback f).obj
              (DerivedCategory.Q.obj L))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor
            (((SheafOfModules.restrictScalars
              ((sheafCompose (Opens.grothendieckTopology X)
                (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj A)
            (((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
               (ComplexShape.up ℤ)).obj L)
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)) := by
  classical
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let B := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let V := SheafOfModules.toSheaf B
  let W := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  have hV := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    B
  have : PreservesFiniteLimits V := hV.2.1
  have : PreservesFiniteColimits V := hV.2.2.1
  have hW := CategoryTheory.moduleSheaves_colimits_forgetful.{u, u, u, u}
    (moduleRings X.toRingedSpace)
  have : PreservesFiniteLimits W := hW.2.1
  have : PreservesFiniteColimits W := hW.2.2.1
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    G, hG, hGmap, hGadd, ε, _, _, hε⟩ :=
    (derivedPullback_spec f)
  have := hGadd
  let T := G
  let TL := (T.mapHomologicalComplex (.up ℤ)).obj L
  have := hε L hL
  let ep : (derivedPullback f).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj TL :=
    (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso D).app L).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient D (.up ℤ)).obj L)) ≪≫
      DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors (.up ℤ)).app L) ≪≫
      (DerivedCategory.quotientCompQhIso C).app TL
  obtain ⟨ec⟩ := kFlat_derivedTensor_comparison_natIso X
    ((CategoryTheory.Functor.const (Discrete PUnit.{1})).obj A)
    ((CategoryTheory.Functor.const (Discrete PUnit.{1})).obj TL) (fun _ ↦ hA)
  let et : DerivedCategory.Q.obj A ⊗ DerivedCategory.Q.obj TL ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A TL (curriedTensor C)) :=
    (ec.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  let ed := (tensorLeft (DerivedCategory.Q.obj A)).mapIso ep ≪≫ et
  obtain ⟨eb⟩ := relativeTensorPullback_complex_comparison f G hG hGmap A L
  let Z := CochainComplex.mapBifunctor A TL (curriedTensor C)
  let U := SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Modules.tensorPullbackRingMap f))
  let IL := ((TopCat.Sheaf.inverseImageModuleFunctor f.base S.sheaf).mapHomologicalComplex
     (.up ℤ)).obj L
  let := SheafOfModules.monoidalCategory R
  let Z' := CochainComplex.mapBifunctor
    ((U.mapHomologicalComplex (.up ℤ)).obj A) IL (curriedTensor (SheafOfModules.{u} B))
  exact ⟨W.mapIso ((DerivedCategory.homologyFunctor C i).mapIso ed ≪≫
      (DerivedCategory.homologyFunctorFactors C i).app Z) ≪≫
    ((Z.sc i).mapHomologyIso W).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso eb ≪≫
    (Z'.sc i).mapHomologyIso V⟩

end AlgebraicGeometry.Scheme
