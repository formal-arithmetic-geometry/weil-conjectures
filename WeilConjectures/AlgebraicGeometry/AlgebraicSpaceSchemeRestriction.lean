/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Zariski restriction of algebraic-space modules to an étale scheme

Source: Stacks Project, Properties of Spaces, Tag 03G7; Descent, Tags 03DX and 03FH
(blueprint: def-trf-space-module-scheme-restriction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (F : AlgebraicSpace S) (T : F.EtaleSite)

/-- Open subschemes of an étale test scheme, viewed as schemes over the base.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensOver : ((F.etaleForget).obj T).Opens ⥤ Over S :=
  ((F.etaleForget).obj T).restrictFunctor ⋙ Over.map T.obj.left.hom

/-- The map to the space on each open is the composite with the test-scheme map.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensArrow : ((F.etaleForget).obj T).Opens ⥤
    CostructuredArrow yoneda F.obj.obj :=
  (schemeOpensOver F T).toCostructuredArrow yoneda F.obj.obj
    (fun U ↦ yoneda.map (Over.homMk U.ι) ≫ T.obj.hom)
    (by
      intro U V i
      simp only [← Category.assoc, ← Functor.map_comp]
      congr 2
      ext1
      exact Scheme.homOfLE_ι _ i.le)

/-- The open-subscheme composites are representable étale.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction).
Proof: the Yoneda map of an open immersion is representable étale: its base change
is the ordinary scheme pullback, an open immersion. Compose this map with the given
representable étale test map, using `isEtale_comp`. -/
theorem schemeOpensArrow_isEtale (U : ((F.etaleForget).obj T).Opens) :
    IsEtale ((schemeOpensArrow F T).obj U).hom := by
  let r : (schemeOpensOver F T).obj U ⟶ T.obj.left := Over.homMk U.ι rfl
  exact isEtale_comp (yoneda.map r) T.obj.hom
    (((representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1 _ _ r).2
      (inferInstance : Etale U.ι)) T.property

/-- The inclusion of Zariski opens in the small étale site of the space.
Source: Stacks, Tags 03ED and 03G7
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpens : ((F.etaleForget).obj T).Opens ⥤ F.EtaleSite :=
  ObjectProperty.lift _ (schemeOpensArrow F T) (schemeOpensArrow_isEtale F T)

set_option backward.isDefEq.respectTransparency false in
private theorem schemeOpens_compatiblePreserving :
    CompatiblePreserving F.etaleTopology (schemeOpens F T) := by
  constructor
  intro G W R x hx U V X f g i j hi hj e
  have e' : f.hom.left.left ≫ ((F.etaleForget).obj T).homOfLE i.le =
      g.hom.left.left ≫ ((F.etaleForget).obj T).homOfLE j.le :=
    congrArg (fun k ↦ k.hom.left.left) e
  let h := isPullback_opens_inf_le i.le j.le
  let r := h.lift f.hom.left.left g.hom.left.left e'
  have hr : r ≫ ((F.etaleForget).obj T).homOfLE inf_le_left = f.hom.left.left :=
    h.lift_fst _ _ _
  have hs : r ≫ ((F.etaleForget).obj T).homOfLE inf_le_right = g.hom.left.left :=
    h.lift_snd _ _ _
  have hrι : r ≫ (U ⊓ V).ι = f.hom.left.left ≫ U.ι := by
    calc
      r ≫ (U ⊓ V).ι =
          (r ≫ ((F.etaleForget).obj T).homOfLE inf_le_left) ≫ U.ι := by
        rw [Category.assoc, Scheme.homOfLE_ι]
      _ = _ := congrArg (fun q ↦ q ≫ U.ι) hr
  let rOver : X.obj.left ⟶ (schemeOpensOver F T).obj (U ⊓ V) :=
    Over.homMk r (by
      change r ≫ ((U ⊓ V).ι ≫ T.obj.left.hom) = X.obj.left.hom
      calc
        _ = (r ≫ (U ⊓ V).ι) ≫ T.obj.left.hom := (Category.assoc _ _ _).symm
        _ = (f.hom.left.left ≫ U.ι) ≫ T.obj.left.hom :=
          congrArg (fun q ↦ q ≫ T.obj.left.hom) hrι
        _ = _ := f.hom.left.w)
  let k : X ⟶ (schemeOpens F T).obj (U ⊓ V) :=
    ObjectProperty.homMk (CostructuredArrow.homMk rOver (by
      change yoneda.map rOver ≫
        (yoneda.map (Over.homMk (U ⊓ V).ι) ≫ T.obj.hom) = X.obj.hom
      rw [← Category.assoc, ← Functor.map_comp]
      have heq : rOver ≫ Over.homMk (U ⊓ V).ι =
          f.hom.left ≫ Over.homMk U.ι := by
        ext1
        change r ≫ (U ⊓ V).ι = f.hom.left.left ≫ U.ι
        exact hrι
      rw [heq, Functor.map_comp, Category.assoc]
      exact f.hom.w))
  have hk₁ : k ≫ (schemeOpens F T).map (homOfLE inf_le_left) = f := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    exact hr
  have hk₂ : k ≫ (schemeOpens F T).map (homOfLE inf_le_right) = g := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    apply Over.OverMorphism.ext
    exact hs
  have hx' := hx (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    (homOfLE (show U ⊓ V ≤ V from inf_le_right)) hi hj (Subsingleton.elim _ _)
  have hh := congrArg (G.obj.map k.op) hx'
  change G.obj.map k.op (G.obj.map ((schemeOpens F T).map (homOfLE inf_le_left)).op
      (x i hi)) = G.obj.map k.op
      (G.obj.map ((schemeOpens F T).map (homOfLE inf_le_right)).op (x j hj)) at hh
  simpa only [← Functor.map_comp_apply, ← op_comp, hk₁, hk₂] using hh

/-- Zariski-open restriction is continuous.
Source: Stacks, Tags 03ED, 03G7 and 03FH
(blueprint: def-trf-space-module-scheme-restriction).
Proof: an open cover of an open subscheme is jointly surjective and étale, hence
is a cover in the small étale site. Its intersections are the same scheme
intersections. The sheaf equalizers for these covers therefore restrict to the
Zariski sheaf equalizers. The generating-cover criterion gives continuity. -/
theorem schemeOpens_isContinuous :
    (schemeOpens F T).IsContinuous
      (Opens.grothendieckTopology ((F.etaleForget).obj T))
      F.etaleTopology := by
  apply Functor.isContinuous_of_coverPreserving (schemeOpens_compatiblePreserving F T)
  constructor
  intro U R hR
  have hpush : R.functorPushforward (schemeOpens F T) =
      Sieve.generate (R.arrows.map (schemeOpens F T)) := by
    rw [Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve]
  rw [hpush]
  apply Precoverage.generate_mem_toGrothendieck
  constructor
  · intro V f hf
    cases hf with
    | @of V g hg =>
      change Etale (((F.etaleForget).obj T).homOfLE g.le)
      infer_instance
  · intro x
    obtain ⟨V, f, hf, hx⟩ := hR x.1 x.2
    refine ⟨(schemeOpens F T).obj V, (schemeOpens F T).map f,
      Presieve.map.of hf, ⟨x.1, hx⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply f.le ⟨x.1, hx⟩

/-- The structure-ring comparison is the canonical identification
`O_T(U) ≅ Γ(U.toScheme, O)` on every open, with the usual restrictions.
Source: Stacks, Tags 03G7 and 03FH
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeOpensRingHom : ((F.etaleForget).obj T).ringCatSheaf.obj ⟶
    (schemeOpens F T).op ⋙ F.structurePresheaf :=
  Functor.whiskerRight (((F.etaleForget).obj T).restrictFunctorΓ.inv)
    (forget₂ CommRingCat RingCat)

/-- Restriction of an algebraic-space module to the Zariski opens of an étale
scheme. Its sections over `U` are precisely the given module's sections at
`U.toScheme → T → F`; the scalar action uses the canonical ring comparison.
For line modules this is the ordinary invertible module in the Zariski/étale
comparison: the inverse comparison functor is restriction to open subschemes.
Source: Stacks, Tags 03DX and 03FH
(blueprint: def-trf-space-module-scheme-restriction). -/
noncomputable def schemeRestriction : F.Modules ⥤ ((F.etaleForget).obj T).Modules :=
  haveI := schemeOpens_isContinuous F T
  SheafOfModules.pushforward (F := schemeOpens F T) ⟨schemeOpensRingHom F T⟩

end AlgebraicGeometry.AlgebraicSpace
