/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.PerfectDescentCompatibleLocalData
import Sheaf.AlgebraicGeometry.OpenPerfectModelTransport
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionDetectsIso
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # PerfectDescentOpenUnion

Source: Stacks Project, Tag 09RF (blueprint: lem-pc-perfect-descent-open-union).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem isIso_restricted_adjoint
    {C D CU DU : Type*} [Category C] [Category D] [Category CU] [Category DU]
    (L : C ⥤ D) (R : D ⥤ C) (RU : C ⥤ CU) (RX : D ⥤ DU) (LU : CU ⥤ DU)
    (adj : L ⊣ R) (γ : L ⋙ RX ≅ RU ⋙ LU)
    {F : C} {E : D} {A : CU} (iU : RU.obj F ≅ A)
    (a : A ⟶ RU.obj (R.obj E)) (d : F ⟶ R.obj E)
    (hd : RU.map d = iU.hom ≫ a)
    (ha : IsIso (LU.map a ≫ γ.inv.app (R.obj E) ≫ RX.map (adj.counit.app E))) :
    IsIso (RX.map ((adj.homEquiv F E).symm d)) := by
  have hn : RX.map (L.map d) =
      γ.hom.app F ≫ LU.map (RU.map d) ≫ γ.inv.app (R.obj E) := by
    rw [← cancel_mono (γ.hom.app (R.obj E))]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simpa only [Functor.comp_map, Functor.comp_obj, Category.comp_id] using γ.hom.naturality d
  have heq : RX.map ((adj.homEquiv F E).symm d) =
      γ.hom.app F ≫ LU.map iU.hom ≫
        (LU.map a ≫ γ.inv.app (R.obj E) ≫ RX.map (adj.counit.app E)) := by
    rw [Adjunction.homEquiv_symm_apply, Functor.map_comp, hn, hd, Functor.map_comp]
    simp only [Category.assoc]
  rw [heq]
  infer_instance

set_option synthInstance.maxSize 2048 in

/-- The induction step for descent: glue descent on a quasi-compact open and an
additional affine open.
Source: Stacks Project, Tag 09RF, the two-open induction step
(blueprint: lem-pc-perfect-descent-open-union).

Proof: Given an open-immersion presentation of `W ⊔ V` and a perfect complex on
its limit base change, restrict to the inverse images of `W` and `V`. Apply the two
hypotheses to descend those restrictions. Directedness gives a common later stage;
derived pullback preserves perfectness. Quasi-separatedness makes `W ∩ V`
quasi-compact, so its map to `Spec R_i` is finitely presented. Apply Tag 09RE to
the overlap identification and its inverse, then stabilize the two inverse
relations, obtaining an isomorphism on a stage overlap. Use derived adjunction to
view the two comparison maps as maps into the restriction of `Rf_* E`. Restriction
of derived direct image to opens agrees with the restricted morphism's direct
image (Tag 08FE). The overlap equation makes these adjoints compatible. Tag 08DG
glues the two objects and their maps into `Rf_* E`. The glued object is perfect
because this is local on the two opens. The adjoint of the glued map is an
isomorphism: on each member of the pulled-back cover it is the given comparison
isomorphism, so the cone has zero cohomology sheaves. Open-immersion and pullback
identifications give exactly the stated canonical map for the union. -/
theorem perfect_descent_open_union
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c) (i : I) (Xi : Scheme.{u}) (s : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (W V : Xi.Opens) (hW : IsCompact (W : Set Xi)) (hV : IsAffineOpen V)
    (dW : PerfectDescentOnOpen R c i Xi s W)
    (dV : PerfectDescentOnOpen R c i Xi s V) :
    PerfectDescentOnOpen R c i Xi s (W ⊔ V) := by
  classical
  intro Z f _ hf
  dsimp only
  intro E hE
  obtain ⟨j, hij, hdata⟩ :=
    perfect_descent_compatible_local_data R c hc i Xi s W V hW hV dW dV Z f hf E hE
  let Xj := pullback (f ≫ s) (Spec.map (R.map (homOfLE hij)))
  let XL := pullback (f ≫ s) (Spec.map (c.ι.app i))
  let g := baseChangeMap (f ≫ s)
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))
  obtain ⟨U, V, hcover, adj, γU, γV, A, B, e, a, b, hA, hB, hab, ha, hb⟩ := hdata
  obtain ⟨F, iU, iV, _, hm⟩ := derived_open_gluing Xj U V hcover A B e
  obtain ⟨d, hdU, hdV⟩ := hm ((schemeDerivedDirectImage g).obj E) a b hab
  have hF : Xj.IsPerfect F := by
    intro x
    have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact Scheme.local_perfect_of_openRestriction_iso Xj U F A hA iU x hx
    · exact Scheme.local_perfect_of_openRestriction_iso Xj V F B hB iV x hx
  let φ := (adj.homEquiv F E).symm d
  have hφU : IsIso ((schemeOpenRestriction XL (g ⁻¹ᵁ U)).mapDerivedCategory.map φ) :=
    isIso_restricted_adjoint _ _ _ _ _ adj γU iU a d hdU ha
  have hφV : IsIso ((schemeOpenRestriction XL (g ⁻¹ᵁ V)).mapDerivedCategory.map φ) :=
    isIso_restricted_adjoint _ _ _ _ _ adj γV iV b d hdV hb
  have hpre : (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hφ : IsIso φ := schemeDerived_isIso_of_openRestriction φ (by
    intro x
    have hx : x ∈ (g ⁻¹ᵁ U) ⊔ (g ⁻¹ᵁ V) := by rw [hpre]; trivial
    rcases hx with hx | hx
    · exact ⟨g ⁻¹ᵁ U, hx, hφU⟩
    · exact ⟨g ⁻¹ᵁ V, hx, hφV⟩)
  exact ⟨j, hij, F, hF, ⟨asIso φ⟩⟩

end AlgebraicGeometry
