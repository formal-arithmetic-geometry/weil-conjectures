/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiConstructions
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiTargetComparison
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiLocalComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # One local representative equation

## References

* [Stacks, Tag 09ZF]
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private lemma sheaf_restriction {S : Scheme.{u}}
    {K D : Sheaf S.smallEtaleTopology (Type (u + 1))} (c : K ≅ D)
    {V U : S.Etale} (r : V ⟶ U) (t : K.obj.obj (op U)) :
    D.obj.map r.op (c.hom.hom.app (op U) t) =
      c.hom.hom.app (op V) (K.obj.map r.op t) := by
  have hc := ConcreteCategory.congr_hom (c.hom.hom.naturality r.op) t
  simp only [types_comp_apply] at hc
  exact hc.symm

/-- A representative on one open gives the restriction of the transported section
(Stacks, Tag 09ZF). -/
theorem gabber_h0_zariski_representative_equation
    {X Z U X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (q : U ⟶ X) [Etale q] (h : X' ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    (s : F.obj.obj (op (Scheme.Etale.mk q)))
    (hs : etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
      ((Scheme.etaleSetPullback i).obj F).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ i).map
          (MorphismProperty.Over.homMk q (Category.comp_id q) :
            Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    (W : X'.Opens) (phi : W.toScheme ⟶ U) (hphi : phi ≫ q = W.ι ≫ h)
    (beta : (gabberZariskiPull (pullback.snd i h)).obj (gabberZariskiG h F) ⟶
      gabberZariskiH i h F)
    (hbeta : GabberZariskiUnitCompatible i h F beta) :
    beta.hom.app (op ((pullback.snd i h) ⁻¹ᵁ W))
      (gabberZariskiUnit (pullback.snd i h) (gabberZariskiG h F) W
        (gabberLocalRepresentative q h F s W phi hphi)) =
      (gabberZariskiH i h F).obj.map (homOfLE le_top).op
        (gabberZariskiTargetSection i h F t) := by
  let j := pullback.snd i h
  let k := j ≫ h
  let K := (Scheme.etaleSetPullback j).obj ((Scheme.etaleSetPullback h).obj F)
  let D := (Scheme.etaleSetPullback k).obj F
  let c := ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
    X X' (pullback i h) h j).app F
  let V' := Scheme.Etale.mk (j ⁻¹ᵁ W).ι
  let r : V' ⟶ Scheme.Etale.mk (⊤ : (pullback i h).Opens).ι :=
    (gabberOpenEtale (pullback i h)).map (homOfLE le_top)
  refine (hbeta W (gabberLocalRepresentative q h F s W phi hphi)).trans ?_
  apply (((sheafToPresheaf _ _).mapIso c).app (op V')).toEquiv.injective
  change c.hom.hom.app (op V')
      (K.obj.map (gabberPreimageEtaleIso j W).hom.op
        (etaleSetDescentUnit j ((Scheme.etaleSetPullback h).obj F)
          (Scheme.Etale.mk W.ι) (gabberLocalRepresentative q h F s W phi hphi))) =
    c.hom.hom.app (op V') (K.obj.map r.op (gabberZariskiTargetSection i h F t))
  have hl := gabberZariskiLocalComparison i q h F t s hs W phi hphi
  have ht := gabberZariskiTargetComparison i h F t
  exact hl.trans ((congrArg (fun z ↦ D.obj.map r.op z) ht.symm).trans
    (sheaf_restriction c r (gabberZariskiTargetSection i h F t)))

end AlgebraicGeometry
