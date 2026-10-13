/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.PerfectDescendMorphisms
import Sheaf.AlgebraicGeometry.DerivedPullbackPerfect
import Sheaf.AlgebraicGeometry.DerivedOpenGluing
import Sheaf.AlgebraicGeometry.OpenPerfectModelTransport
import Sheaf.AlgebraicGeometry.SchemeDerivedHomGluing
import Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

/-! # Geometric stage model from prescribed local pullback models

Source: Stacks Project, Tag 09RF, the construction of a, b and c before Tag 08DG.
(blueprint: lem-pc-perfect-local-models-stage-gluing).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The geometric descent-and-gluing part of eventual local compatibility.
Source: Stacks Project, Tag 09RE and Tag 09RF, two-open induction using Tag 08DG.
(blueprint: lem-pc-perfect-local-models-stage-gluing).

Proof: Pass to the directed tail above j. On the overlap U intersection V,
restrict A and B. They are perfect by Tag 09UA. The overlap is compact since
Y_j is quasi-separated and U,V are compact, and its map to Spec R_j is finitely
presented. Restrict the given isomorphisms to the inverse-image overlap and
compose one with the inverse of the other, using the coherent pullback/restriction
comparisons. Apply Tag 09RE there to descend this isomorphism and its inverse,
and stabilize the inverse equations at a common later stage k. The resulting
stage isomorphism has exactly this prescribed limit pullback, not merely an
unspecified isomorphism between the objects. Pull A and B to the inverse-image
cover on Y_k. Tag 08DG glues these objects along that descended isomorphism to
an object F, with local identifications realizing its transition. The local restrictions
of F are perfect because pullback preserves perfectness; the covering opens
therefore give the displayed neighbourhood witnesses, without asserting global
perfectness.
The local identifications of Lg_k*F with E induced by the original comparisons
agree on the overlap by the prescribed-pullback equation. The derived Hom
Mayer-Vietoris surjectivity glues their morphisms to a global map Lg_k*F to E.
Its two restrictions are the given isomorphisms. The inverse-image cover
therefore gives the displayed local invertibility witnesses. Global detection of
perfectness and invertibility are left to the caller. No adjunction or
maps to Rg_k*E occur in this argument. Empty schemes, empty overlaps, equal
opens and non-strict preorders work by the same restrictions and directed tail.
The auxiliary object F is an existential theorem witness, never a definition
chosen from an unproved mere existence statement. -/
theorem perfect_local_models_stage_gluing
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (pullback t (Spec.map (R.map (homOfLE hij))) : Scheme.{u})))
    (hV : IsCompact (V : Set (pullback t (Spec.map (R.map (homOfLE hij))) : Scheme.{u})))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ ((baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app j))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)]))) ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    ∃ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap t
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (Spec.map (c.ι.app i)))
        (Over.homMk (Spec.map (c.ι.app k))
          (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))]))
      ∃ (F : schemeDerivedCategory
          (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))))
        (a : (derivedPullback g).obj F ⟶ E),
        (∀ x : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk)))) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (R.map (homOfLE (hij.trans hjk))))).Opens,
            x ∈ W ∧ W.toScheme.IsPerfect ((derivedPullback W.ι).obj F)) ∧
        (∀ x : (pullback t (Spec.map (c.ι.app i)) : Scheme.{u}),
          ∃ W : (pullback t (Spec.map (c.ι.app i))).Opens, x ∈ W ∧
            IsIso ((schemeOpenRestriction _ W).mapDerivedCategory.map a)) := by sorry

end AlgebraicGeometry
