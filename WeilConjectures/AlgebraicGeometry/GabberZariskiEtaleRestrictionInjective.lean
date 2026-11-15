/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.GabberZariskiEtaleUnitNatural
import WeilConjectures.AlgebraicGeometry.GabberZariskiEtaleComparisonStalkInjective
import Mathlib.Topology.Sheaves.Stalks

/-! # Gabber's Zariski--étale restriction injectivity

## References

* [Stacks, Tag 09ZF]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The canonical Zariski comparison is the unique sheaf morphism compatible with
both inverse-image units, and is injective on every open (Stacks, Tag 09ZF). -/
theorem gabber_zariski_etale_restriction_injective
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (Fzar : TopCat.Sheaf (Type (max (u + 1) v)) X.carrier)
    (eX : Fzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        X.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙ F.obj)
    (iFzar : TopCat.Sheaf (Type (max (u + 1) v)) Z.carrier)
    (eZ : iFzar.obj ≅
      (MorphismProperty.Comma.lift (P := @Etale) (Q := ⊤) (W := ⊤)
        Z.restrictFunctor (fun U => (inferInstance : Etale U.ι)) (fun _ => trivial)
        (fun _ => trivial)).op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
        (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).obj F).obj)
    (a : ∀ W : X.Opens, Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅
      (MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk W.ι))
    (ha : ∀ W : X.Opens,
      (a W).hom.left ≫ pullback.fst W.ι i = i ∣_ W) :
    ∃ beta :
      (Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map i.base) (Type (max (u + 1) v))
        (Opens.grothendieckTopology X.carrier)
        (Opens.grothendieckTopology Z.carrier)).obj Fzar ⟶ iFzar,
      (∀ V : Z.Opens, Function.Injective (beta.hom.app (op V))) ∧
      ∀ beta' :
        (Functor.sheafPullbackConstruction.sheafPullback
          (Opens.map i.base) (Type (max (u + 1) v))
          (Opens.grothendieckTopology X.carrier)
          (Opens.grothendieckTopology Z.carrier)).obj Fzar ⟶ iFzar,
        (∀ (W : X.Opens) (s : Fzar.obj.obj (op W)),
        beta'.hom.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map i.base) (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier)
            (Opens.grothendieckTopology Z.carrier)).unit.app Fzar).hom.app (op W) s) =
        eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s)))) ↔ beta' = beta := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map i.base) (Type (max (u + 1) v))
    (Opens.grothendieckTopology X.carrier) (Opens.grothendieckTopology Z.carrier)
  obtain ⟨alpha, halpha⟩ := gabber_zariski_etale_unit_natural i F Fzar eX iFzar eZ a ha
  let beta := (adj.homEquiv Fzar iFzar).symm alpha
  have htranspose : adj.homEquiv Fzar iFzar beta = alpha :=
    (adj.homEquiv Fzar iFzar).apply_symm_apply alpha
  have hbeta : ∀ (W : X.Opens) (s : Fzar.obj.obj (op W)),
        beta.hom.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map i.base) (Type (max (u + 1) v))
            (Opens.grothendieckTopology X.carrier)
            (Opens.grothendieckTopology Z.carrier)).unit.app Fzar).hom.app (op W) s) =
        eZ.inv.app (op (i ⁻¹ᵁ W))
          (((Functor.sheafPullbackConstruction.sheafPullback
            (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
            (X.smallGrothendieckTopology @Etale)
            (Z.smallGrothendieckTopology @Etale)).obj F).obj.map (a W).hom.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ i) (Type (max (u + 1) v))
              (X.smallGrothendieckTopology @Etale)
              (Z.smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op (Scheme.Etale.mk W.ι)) (eX.hom.app (op W) s))) := by
    intro W s
    have h := congrArg (fun f => f.hom.app (op W) s) htranspose
    rw [Adjunction.homEquiv_apply] at h
    exact h.trans (halpha W s)
  refine ⟨beta, ?_, ?_⟩
  · intro V s t hst
    classical
    let H := (Functor.sheafPullbackConstruction.sheafPullback
      (Opens.map i.base) (Type (max (u + 1) v))
      (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology Z.carrier)).obj Fzar
    have hlocal (z : V) : ∃ (W : Z.Opens) (_ : z.val ∈ W) (f : W ⟶ V),
        H.obj.map f.op s = H.obj.map f.op t := by
      let D := (OpenNhds.inclusion z.val).op ⋙ H.obj
      let n : (OpenNhds z.val)ᵒᵖ := op ⟨V, z.property⟩
      have hinj := gabber_zariski_etale_comparison_stalk_injective
        i F Fzar eX iFzar eZ a ha beta hbeta z.val
      have hg : colimit.ι D n s = colimit.ι D n t := by
        apply hinj
        have hs := congrArg (fun f => f s)
          (congrArg ConcreteCategory.hom
            (colimit.ι_map (Functor.whiskerLeft (OpenNhds.inclusion z.val).op beta.hom) n))
        have ht := congrArg (fun f => f t)
          (congrArg ConcreteCategory.hom
            (colimit.ι_map (Functor.whiskerLeft (OpenNhds.inclusion z.val).op beta.hom) n))
        exact hs.trans ((congrArg
          (colimit.ι ((OpenNhds.inclusion z.val).op ⋙ iFzar.obj) n) hst).trans ht.symm)
      obtain ⟨W, f, hf⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit D) (i := n) s t).mp hg
      exact ⟨W.unop.val, W.unop.property, f.unop, hf⟩
    choose W hz f hf using hlocal
    apply TopCat.Sheaf.eq_of_locally_eq' H W V f _ s t hf
    intro z hzV
    simp only [Opens.mem_iSup]
    exact ⟨⟨z, hzV⟩, hz ⟨z, hzV⟩⟩
  · intro beta'
    constructor
    · intro hbeta'
      apply (adj.homEquiv Fzar iFzar).injective
      rw [htranspose]
      ext W s
      rw [Adjunction.homEquiv_apply]
      exact (hbeta' W.unop s).trans (halpha W.unop s).symm
    · rintro rfl
      exact hbeta

end AlgebraicGeometry
