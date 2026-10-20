/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectOpenGluingData
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.PerfectLocalModelsStageGluing
import WeilConjectures.AlgebraicGeometry.PerfectOpenGluingDataOfGlobalModel
import WeilConjectures.AlgebraicGeometry.PerfectOfOpenPullbacks
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionDetectsIso

/-! # Eventual compatibility of two prescribed local perfect models

Source: Stacks Project, Tag 09RF, the construction of a, b and c before Tag 08DG.
(blueprint: lem-pc-perfect-local-models-eventually-compatible).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Two prescribed local models with limit comparisons acquire compatible adjoint
maps after a further base change. No descent-on-opens hypothesis is assumed.
Source: Stacks Project, Tag 09RF, two-open induction, construction of a, b and c.
(blueprint: lem-pc-perfect-local-models-eventually-compatible).

Proof: Work on the tail above j. Restrict A and B to U intersection V.
The stage scheme is quasi-separated and U and V are compact, so this intersection
is compact. Its structure map is locally of finite presentation and quasi-compact.
The given limit comparisons identify the pullbacks of the two restricted objects.
Tag 09RE descends this identification as an isomorphism after increasing the stage;
its equality clause stabilizes the inverse relations if needed. Pull A and B to
this later stage and use the coherent composition comparisons to transport φU and
φV; their restrictions agree through the descended overlap isomorphism. They remain
perfect by Tag 09UA. Choose the global derived adjunction and the canonical
pullback/restriction comparisons. Tag 08FE identifies the local right adjoints
with the restrictions of the global derived direct image. Take the local adjoints
of the transported φU and φV to obtain a and b. Naturality of the adjunction and
its counit identifies their restrictions through the overlap isomorphism. The
inverse Hom equivalences express φU and φV as the two composites in the IsIso
clauses of PerfectOpenGluingData. This gives the required local datum, without
constructing or gluing a global stage object. The argument also applies to an
empty overlap, an empty member of the cover, and a non-strict preorder.
-/
theorem perfect_local_models_eventually_compatible
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
      PerfectOpenGluingData g E := by
  obtain ⟨k, hjk, F, a, hF, ha⟩ := perfect_local_models_stage_gluing
    R c hc i Z t j hij U V hcover hU hV A B hA hB E φU φV
  refine ⟨k, hjk, ?_⟩
  have hperfect := perfect_of_open_pullbacks F hF
  have hcomparison : IsIso a := schemeDerived_isIso_of_openRestriction a ha
  let := hcomparison
  exact perfect_open_gluing_data_of_global_model _ E F hperfect (asIso a)

end AlgebraicGeometry
