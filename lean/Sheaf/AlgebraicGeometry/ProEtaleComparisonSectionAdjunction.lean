/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V4
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
import Sheaf.AlgebraicGeometry.ProEtaleComparisonSectionUnitUniversal

/-! # The adjunction for the section-valued comparison sheaf

Source: Stacks Project, Tag 0GLZ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 0GLZ, the adjunction construction and final paragraph.
(blueprint: lem-cbc-comparison-section-adjunction).
Proof: restrict a pro-etale sheaf G to Y_et; etale covers are pro-etale covers, so
this restriction is a sheaf. Concretely use restriction along the composite of
`Scheme.toProEt Y.left` with `MorphismProperty.Over.map` for Y.hom; both functors
are continuous by the existing site instances. For alpha : F -> nu_* G use restriction to Y
times_X U
to obtain F -> f_* (G|Y_et). Transpose under f inverse image and evaluate at the
identity of Y to obtain beta_Y. Two successive inverse-image adjunction transposes
show naturality under arbitrary X-maps Z -> Y: both restrict alpha_U(s) to Z times_X U.
These maps are natural in F and G. Conversely send beta to nu_*(beta) composed with
the etale diagonal-unit map, decoded by e inverse. The etale inverse-image/restriction
isomorphism identifies the first composite with alpha. For the other composite, fix Y and let V
range over etale Y-schemes.
Etale inverse image is restriction, so composition identifies (f inverse image F)(V)
with A(F)(V viewed over X). The components beta_V consequently define a morphism
f inverse image F -> G_Y. Naturality of beta at Y times_X U -> U and the diagonal
unit formula show that its transpose is the defining map b_Y. Uniqueness of
adjunction transpose therefore identifies it with t_Y. Evaluate at V = Y to recover
the original beta_Y. These mutually inverse natural Hom
bijections define adj. Their unit is precisely the diagonal-unit map decoded by e,
which proves the displayed formula. -/
theorem proEtaleComparisonSectionAdjunction (X : Scheme.{u})
    (A : Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (e : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (Y : X.ProEt),
      (A.obj F).obj.obj (op Y) ≃
        ((Scheme.etaleSetPullback Y.hom).obj F).obj.obj
          (op (Scheme.Etale.mk (𝟙 Y.left))))
    (hres : ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (Y Z : X.ProEt) (g : Z ⟶ Y) (s : (A.obj F).obj.obj (op Y)),
      e F Z ((A.obj F).obj.map g.op s) =
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ g.left) (Type (u + 1))
            (Y.left.smallGrothendieckTopology @Etale)
            (Z.left.smallGrothendieckTopology @Etale)).unit.app
              ((Scheme.etaleSetPullback Y.hom).obj F)).hom.app
                (op (Scheme.Etale.mk (𝟙 Y.left))) ≫
            (etaleSetTerminalTransport Y.hom g.left Z.hom g.w F).inv) (e F Y s))
    (hfun : ∀ (F F' : Sheaf X.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (Y : X.ProEt) (s : (A.obj F).obj.obj (op Y)),
      e F' Y ((A.map ψ).hom.app (op Y) s) =
        ((Scheme.etaleSetPullback Y.hom).map ψ).hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (e F Y s))
    : ∃ adj : A ⊣ (Scheme.toProEt X).sheafPushforwardContinuous
        (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X),
    ∀ (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (U : X.Etale) (s : F.obj.obj (op U)),
      letI : (MorphismProperty.Over.pullback @Etale ⊤ U.hom).IsContinuous
          (X.smallGrothendieckTopology @Etale)
          (U.left.smallGrothendieckTopology @Etale) :=
        Scheme.isContinuous_overPullback @Etale @Etale le_rfl U.hom
      e F ((Scheme.toProEt X).obj U)
        ((adj.unit.app F).hom.app (op U) s) =
        ((Scheme.etaleSetPullback U.hom).obj F).obj.map
          (MorphismProperty.Over.homMk
            (pullback.lift (𝟙 U.left) (𝟙 U.left) (by simp)) (by simp) :
            Scheme.Etale.mk (𝟙 U.left) ⟶
              (MorphismProperty.Over.pullback @Etale ⊤ U.hom).obj U).op
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @Etale ⊤ U.hom) (Type (u + 1))
            (X.smallGrothendieckTopology @Etale)
            (U.left.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op U) s) := by
  let R := (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let η := proEtaleComparisonSectionUnit X A e hres hfun
  let E (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :=
    Equiv.ofBijective (fun f : A.obj F ⟶ G ↦ η.app F ≫ R.map f)
      (proEtaleComparisonSectionUnit_bijective X A e hres hfun F G)
  let h : Adjunction.CoreHomEquiv A R := {
    homEquiv := E
    homEquiv_naturality_left_symm := by
      intro F' F G f g
      apply (E F' G).injective
      erw [Equiv.apply_symm_apply]
      change f ≫ g = η.app F' ≫ R.map (A.map f ≫ (E F G).symm g)
      have hn : f ≫ η.app F = η.app F' ≫ R.map (A.map f) := η.naturality f
      rw [R.map_comp, ← Category.assoc, ← hn, Category.assoc]
      change f ≫ g = f ≫ (E F G) ((E F G).symm g)
      erw [Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro F G G' f g
      change η.app F ≫ R.map (f ≫ g) = (η.app F ≫ R.map f) ≫ R.map g
      rw [R.map_comp, Category.assoc]
  }
  let adj := Adjunction.mkOfHomEquiv h
  refine ⟨adj, ?_⟩
  intro F U s
  have hu : adj.unit.app F = η.app F := by
    change η.app F ≫ R.map (𝟙 (A.obj F)) = η.app F
    rw [R.map_id]
    exact Category.comp_id _
  rw [hu]
  change e F ((Scheme.toProEt X).obj U)
    ((e F ((Scheme.toProEt X).obj U)).symm
      _) = _
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry
