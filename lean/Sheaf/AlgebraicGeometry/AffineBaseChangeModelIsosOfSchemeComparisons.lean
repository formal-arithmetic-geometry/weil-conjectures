/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Algebra.Homology.KFlatModuleBaseChange

/-! # Coherent complex comparisons over an identified affine diagram

Source: Stacks Project, Tags 08DW, 09RE and 0D5S.
(blueprint: lem-pc-affine-base-change-model-isos-of-scheme-comparisons). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- For fixed compatible scheme identifications and fixed localized derived
transports, construct coherent comparison data from the model isomorphisms and
their conjugated Hom equations.
Unlike the geometric construction, F and C may be any diagram and cocone with
these identifications. No directedness or colimit property is used here. The
localized transports d and dlim are inputs; the construction below uses them
as the existential transports in affineModelComparisonData.

Source: Stacks Project, Tags 08DW(2), 09RE (affine calculation), 06Y1 and 0D5S
(blueprint: lem-pc-affine-base-change-model-isos-of-scheme-comparisons).

Proof: Rewrite E and K using hEr and hKr. The supplied native K-flat
hypotheses say that E₀ and K₀ preserve quasi-isomorphisms under tensoring.
Extension of scalars preserves this
property without any flatness assumption on the ring map, by the scalar-extension
K-flat criterion. Apply it along r and then along every stage or cocone arrow.
Open affineModelComparisonData and use the supplied d,dlim as its transports.
Use the natural affine pullback/tilde comparison on these models.
Its composite with the scalar-extension associativity isomorphism identifies
extension first along r and then along the stage map with extension along
their composite. The first two equations in hgeom identify the corresponding
scheme maps with σ(j) followed by the geometric projection, and τ followed
by the limit projection. Transport through hd, hdlim and he, and through
hPE, hQK and the counit of e, to obtain αE, αK, βE and βK.
For f at stage j, use naturality of the K-flat affine comparison, now applied
to the ring map from j to k (or to C.pt), not just to maps descended from E₀.
The last two equations in hgeom identify these affine maps with the geometric
base-change arrows. The pullback composition isomorphisms are pinned by their
counits and agree with perfectHomComposition. Scalar-extension associativity
conjugates the chain map to scalarExtensionHom. Cancel the comparison and
inverse components, giving exactly the two displayed Hom equations. This
argument uses no morphism descent or flatness of the ring maps. Zero complexes,
zero rings, equal indices and empty spectra are covered by the same naturality
and universal-property arguments. -/
theorem exists_affineBaseChangeModelIsosOfSchemeComparisons
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y)
    (e : schemeDerivedCategory (Spec (Scheme.Γ.obj (.op Y))) ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (P Q : schemeDerivedCategory Y)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (Scheme.Γ.obj (.op Y))) ℤ)
    (hE : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat E₀)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
      (.up ℤ)).kFlat K₀)
    (hPE : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E₀))
    (hQK : e.inverse.obj Q ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K₀))
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (r : Scheme.Γ.obj (.op Y) →+* F.obj ⟨i, le_rfl⟩)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hEr : E = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀)
    (hKr : K = ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (hgeom :
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        (σ j).hom ≫ pullback.fst s (Spec.map (R.map (homOfLE j.val.property))) =
          Spec.map (CommRingCat.ofHom r ≫ F.map (homOfLE j.property)) ≫ t.hom) ∧
      (τ.hom ≫ pullback.fst s (Spec.map (c.ι.app i)) =
        Spec.map (CommRingCat.ofHom r ≫ C.ι.app ⟨i, le_rfl⟩) ≫ t.hom) ∧
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    affineModelComparisonData R c i Y s P Q F C E K := by sorry

end AlgebraicGeometry
