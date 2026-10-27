/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.Paper.RelativeProfiniteTestLabels
public import Sheaf.Paper.ProfinitePointPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.Paper.ContinuousSetConstructions
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-! # Normalized continuous-set Kan comparison and affine evaluation

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; Bhatt--Scholze,
Lemma 4.2.13(1), pp. 30--31; Stacks, Tags 00VE, 00WH, 00WX and 0B65
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation).

The Kan functor and its legs below abbreviate the existing Mathlib constructions.
The comparison is normalized by equality of the adjunction hom equivalences.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuity of the relative test functor, by composition of the two existing
continuous functors. Source: HRS Example 3.1; Stacks Tag 00WX
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation). -/
noncomputable instance normalizedContinuousSetKan_isContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)

/-- The actual left Kan presheaf functor on profinite set sheaves.
Source: Stacks Tag 00VE, lemma-adjoints-u
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation). -/
noncomputable abbrev relativeProfiniteSetKan (X : Scheme.{u}) :=
  sheafToPresheaf (coherentTopology Profinite.{u}) (Type (u + 1)) ⋙
    (profiniteToProEtOf X).op.lan

/-- Sheafification of the actual relative Kan extension, with no choice of inverse image.
Source: Stacks Tag 00WX, lemma-adjoint-sheaves
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation). -/
noncomputable abbrev relativeProfiniteSetKanPullback (X : Scheme.{u}) :=
  relativeProfiniteSetKan X ⋙ presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1))

/-- The Kan/sheafification adjunction, whose right adjoint is restriction to X[S].
Source: Stacks Tags 00VE and 00WX
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation). -/
noncomputable abbrev relativeProfiniteSetKanAdjunction (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (profiniteToProEtOf X)
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)

/-- The colimit leg sending b to the class [(S,phi),b], using the actual Kan unit.
Source: Stacks Tag 00VE, lemma-adjoints-u, explicit construction
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation). -/
noncomputable abbrev relativeProfiniteSetKanLeg (X : Scheme.{u})
    (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (U : X.ProEt) (S : Profinite.{u}) (φ : U ⟶ (profiniteToProEtOf X).obj S) :
    H.obj.obj (op S) ⟶ ((relativeProfiniteSetKan X).obj H).obj (op U) :=
  ((profiniteToProEtOf X).op.lanUnit.app H.obj).app (op S) ≫
    ((relativeProfiniteSetKan X).obj H).map φ.op

private theorem label_naturality (X : Scheme.{u}) (S T : Profinite.{u}) (v : S ⟶ T) :
    (continuousSetRelativeTestProjection X T).comp
        ((profiniteToProEtOf X).map v).left.base.hom =
      v.hom.hom.comp (continuousSetRelativeTestProjection X S) := by
  obtain ⟨_, r, _, hr, _, hn, _⟩ := relative_profinite_test_labels.{u}
  have he (S : Profinite.{u}) : r X S = continuousSetRelativeTestProjection X S := by
    ext z
    exact hr X S z
  simpa only [he] using hn X S T v

private noncomputable def labelMap (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] : continuousSetProfiniteSheaf D ⟶
      ((profiniteToProEtOf X).sheafPushforwardContinuous (Type (u + 1))
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)).obj
        (continuousSetSheaf X D) :=
  ⟨{ app := fun S ↦ ↾fun b ↦ b.comp (continuousSetRelativeTestProjection X S.unop)
     naturality := by
       intro S T v
       apply ConcreteCategory.ext_apply
       intro b
       apply ContinuousMap.ext
       intro z
       exact (congrArg (fun f ↦ b.comp f) (label_naturality X T.unop S.unop v.unop)
         |> congrArg (fun f ↦ f z)).symm }⟩

private theorem kan_representative (X : Scheme.{u})
    (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (U : X.ProEt)
    (z : ((relativeProfiniteSetKan X).obj H).obj (op U)) :
    ∃ (S : Profinite.{u}) (φ : U ⟶ (profiniteToProEtOf X).obj S)
      (b : H.obj.obj (op S)), relativeProfiniteSetKanLeg X H U S φ b = z := by
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (profiniteToProEtOf X).op H.obj (op U)) z
  exact ⟨j.left.unop, j.hom.unop, b, hb⟩

private theorem leg_change (X : Scheme.{u})
    (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) (U : X.ProEt)
    (S T : Profinite.{u}) (v : S ⟶ T) (φ : U ⟶ (profiniteToProEtOf X).obj S)
    (b : H.obj.obj (op T)) :
    relativeProfiniteSetKanLeg X H U T (φ ≫ (profiniteToProEtOf X).map v) b =
      relativeProfiniteSetKanLeg X H U S φ (H.obj.map v.op b) := by
  have hn := ((profiniteToProEtOf X).op.lanUnit.app H.obj).naturality v.op
  have he := congrArg (fun f ↦ f ≫ ((relativeProfiniteSetKan X).obj H).map φ.op) hn
  change H.obj.map v.op ≫
      ((profiniteToProEtOf X).op.lanUnit.app H.obj).app (op S) ≫
        ((relativeProfiniteSetKan X).obj H).map φ.op =
    (((profiniteToProEtOf X).op.lanUnit.app H.obj).app (op T) ≫
      ((relativeProfiniteSetKan X).obj H).map ((profiniteToProEtOf X).map v).op) ≫
        ((relativeProfiniteSetKan X).obj H).map φ.op at he
  simpa only [relativeProfiniteSetKanLeg, op_comp, Functor.map_comp,
    Category.assoc, types_comp_apply] using (ConcreteCategory.congr_hom he b).symm

private theorem affine_labels (X : Scheme.{u}) (U : X.ProEt) [IsAffine U.left] :
    ∃ φU : U ⟶ (profiniteToProEtOf X).obj
        (Profinite.of (ConnectedComponents U.left)),
      (continuousSetRelativeTestProjection X (Profinite.of (ConnectedComponents U.left))).comp
          φU.left.base.hom = ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ ∧
      ∀ (S : Profinite.{u}) (φ : U ⟶ (profiniteToProEtOf X).obj S),
        ∃ g : Profinite.of (ConnectedComponents U.left) ⟶ S,
          φ = φU ≫ (profiniteToProEtOf X).map g := by
  obtain ⟨_, r, _, hr, _, _, _, _, _, _, hterminal⟩ :=
    relative_profinite_test_labels.{u}
  have he (S : Profinite.{u}) : r X S = continuousSetRelativeTestProjection X S := by
    ext z
    exact hr X S z
  obtain ⟨φ, hφ, hfac⟩ := hterminal X U.left U.hom
  let φU : U ⟶ (profiniteToProEtOf X).obj
      (Profinite.of (ConnectedComponents U.left)) := MorphismProperty.Over.Hom.mk φ trivial
  refine ⟨φU, ?_, ?_⟩
  · rw [he] at hφ
    exact hφ
  · intro S ψ
    let c : C(U.left, S) := (r X S).comp ψ.left.base.hom
    let g : Profinite.of (ConnectedComponents U.left) ⟶ S :=
      CompHausLike.ofHom (fun T ↦ TotallyDisconnectedSpace T)
        ((continuousMapPresheafEquivOfTotallyDisconnectedSpace S U.left) c)
    refine ⟨g, ?_⟩
    apply (Scheme.ProEt.forget X).map_injective
    apply hfac S g ((Scheme.ProEt.forget X).map ψ)
    exact ((continuousMapPresheafEquivOfTotallyDisconnectedSpace S U.left).symm_apply_apply
      c).symm

private theorem kan_adjunction_formula (X : Scheme.{u})
    (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
    (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (f : (relativeProfiniteSetKanPullback X).obj H ⟶ G) :
    ((relativeProfiniteSetKanAdjunction X).homEquiv H G f).hom =
      (profiniteToProEtOf X).op.lanUnit.app H.obj ≫
        Functor.whiskerLeft (profiniteToProEtOf X).op
          (toSheafify (Scheme.ProEt.topology X) ((relativeProfiniteSetKan X).obj H) ≫
            f.hom) := by
  unfold relativeProfiniteSetKanAdjunction
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
  change (((profiniteToProEtOf X).op.lanAdjunction (Type (u + 1))).comp
    (sheafificationAdjunction (Scheme.ProEt.topology X) (Type (u + 1)))).unit.app
      H.obj ≫ _ = _
  rw [Adjunction.comp_unit_app, Functor.lanAdjunction_unit]
  rfl

private theorem comparison_normalization (X : Scheme.{u}) :
    ∃ e : relativeProfiniteSetKanPullback X ≅ profinitePointSetSchemeInverseImage X,
      ∀ (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
        (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
        (f : (profinitePointSetSchemeInverseImage X).obj H ⟶ G),
        (relativeProfiniteSetKanAdjunction X).homEquiv H G (e.hom.app H ≫ f) =
          (continuousSetPointAdjunction X).homEquiv H G f := by
  let e := Adjunction.leftAdjointUniq (relativeProfiniteSetKanAdjunction X)
    (continuousSetPointAdjunction X)
  refine ⟨e, ?_⟩
  intro H G f
  rw [Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact ((continuousSetPointAdjunction X).homEquiv_unit H G f).symm

/-- The normalized comparison identifies both adjunctions and computes the continuous-set
map on every Kan leg. On weakly contractible affines its normal representatives are
continuous functions on the actual component quotient, and all three section maps are
bijective, including the canonical sheafification unit.

Source: HRS Example 3.1, p. 6; Bhatt--Scholze Lemma 4.2.13(1), pp. 30--31
(blueprint: lem-sfb-normalized-continuous-set-kan-evaluation).

Proof plan, following all six steps of the node:
1. Expand `lem-weil-pbc-profinite-point-pullback`, `def-weil-proetale-inverse-image`
and `def-weil-pbc-composite-adjunction`. The composite right adjoint evaluates G at
X[S], with the identification of `lem-sfb-relative-profinite-test-labels`.
2. `lem-sfb-pointwise-kan-colimit` identifies the Kan legs with representatives.
Apply `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction` and then
`lem-weil-pbc-conjugate-iso-unit-equation`. Uniqueness of left adjoints gives e
with the displayed equality of hom equivalences, hence also of their units.
3. Label naturality makes b -> b r a morphism into the right adjoint.
Transpose under the specified composite adjunction to get the unique sigma.
Its Kan adjunct alpha sends a leg to b r |phi|. The colimit universal property
and `def-weil-pbc-sheafification` give the displayed factorization through the
canonical unit and e; the unit normalization is essential for this equation.
4. For affine U, `lem-sfb-continuous-set-descent-components` makes its component
quotient profinite. `lem-sfb-relative-profinite-test-labels` supplies phi_U labelled
by q_U. Each phi factors uniquely through phi_U via its component label g, and
the Kan relation replaces [(S,phi),b] by [(T,phi_U),b g].
5. The component-factorization bijection sends c to c q_U. It proves surjectivity
of alpha; equality of two images forces equality of c by surjectivity of q_U,
which proves injectivity. Empty U and empty D are included.
6. `lem-weil-pbc-proetale-sheafification-wcontractible-sections` makes the canonical
unit bijective on precisely these U. The factorization, e and step 5 then make
sigma(U) bijective, with the stated normalization throughout. -/
theorem normalized_continuous_set_kan_evaluation (X : Scheme.{u}) :
    ∃ e : relativeProfiniteSetKanPullback X ≅ profinitePointSetSchemeInverseImage X,
      (∀ (H : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
        (G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
        (f : (profinitePointSetSchemeInverseImage X).obj H ⟶ G),
        (relativeProfiniteSetKanAdjunction X).homEquiv H G (e.hom.app H ≫ f) =
          (continuousSetPointAdjunction X).homEquiv H G f) ∧
      ∀ (D : Type (u + 1)) [TopologicalSpace D],
        (∃! σ : (profinitePointSetSchemeInverseImage X).obj
            (continuousSetProfiniteSheaf D) ⟶ continuousSetSheaf X D,
          IsContinuousSetRealization X D σ) ∧
        ∀ (σ : (profinitePointSetSchemeInverseImage X).obj
            (continuousSetProfiniteSheaf D) ⟶ continuousSetSheaf X D),
          IsContinuousSetRealization X D σ →
          ∃ α : (relativeProfiniteSetKan X).obj (continuousSetProfiniteSheaf D) ⟶
              continuousSetPresheaf X D,
            (∀ (U : X.ProEt) (S : Profinite.{u})
              (φ : U ⟶ (profiniteToProEtOf X).obj S) (b : C(S, D)),
              α.app (op U) (relativeProfiniteSetKanLeg X
                (continuousSetProfiniteSheaf D) U S φ b) =
                  (b.comp (continuousSetRelativeTestProjection X S)).comp φ.left.base.hom) ∧
            α = toSheafify (Scheme.ProEt.topology X)
                ((relativeProfiniteSetKan X).obj (continuousSetProfiniteSheaf D)) ≫
              (e.hom.app (continuousSetProfiniteSheaf D)).hom ≫ σ.hom ∧
            ∀ [T2Space D] [TotallyDisconnectedSpace D] (U : X.ProEt) [IsAffine U.left],
              (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} U →
              ∃ φU : U ⟶ (profiniteToProEtOf X).obj
                  (Profinite.of (ConnectedComponents U.left)),
                (continuousSetRelativeTestProjection X
                    (Profinite.of (ConnectedComponents U.left))).comp φU.left.base.hom =
                  ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ ∧
                (∀ z : ((relativeProfiniteSetKan X).obj
                    (continuousSetProfiniteSheaf D)).obj (op U),
                  ∃ c : C(ConnectedComponents U.left, D),
                    relativeProfiniteSetKanLeg X (continuousSetProfiniteSheaf D) U
                      (Profinite.of (ConnectedComponents U.left)) φU c = z) ∧
                (∀ c : C(ConnectedComponents U.left, D),
                  α.app (op U) (relativeProfiniteSetKanLeg X
                    (continuousSetProfiniteSheaf D) U
                    (Profinite.of (ConnectedComponents U.left)) φU c) =
                    c.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) ∧
                Function.Bijective (α.app (op U)) ∧
                Function.Bijective ((toSheafify (Scheme.ProEt.topology X)
                  ((relativeProfiniteSetKan X).obj
                    (continuousSetProfiniteSheaf D))).app (op U)) ∧
                Function.Bijective (σ.hom.app (op U))  := by
  classical
  obtain ⟨e, he⟩ := comparison_normalization X
  refine ⟨e, he, ?_⟩
  intro D _
  have huniq : ∃! σ : (profinitePointSetSchemeInverseImage X).obj
      (continuousSetProfiniteSheaf D) ⟶ continuousSetSheaf X D,
      IsContinuousSetRealization X D σ := by
    let σ := ((continuousSetPointAdjunction X).homEquiv _ _).symm (labelMap X D)
    refine ⟨σ, ?_, ?_⟩
    · intro S b
      change (((continuousSetPointAdjunction X).homEquiv _ _ σ).hom.app (op S)) b = _
      rw [Equiv.apply_symm_apply]
      rfl
    · intro τ hτ
      apply ((continuousSetPointAdjunction X).homEquiv _ _).injective
      rw [Equiv.apply_symm_apply]
      ext S b
      exact hτ S.unop b
  refine ⟨huniq, ?_⟩
  intro σ hσ
  let α := toSheafify (Scheme.ProEt.topology X)
      ((relativeProfiniteSetKan X).obj (continuousSetProfiniteSheaf D)) ≫
    (e.hom.app (continuousSetProfiniteSheaf D)).hom ≫ σ.hom
  have hα : (profiniteToProEtOf X).op.lanUnit.app
        (continuousSetProfiniteSheaf D).obj ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op α = (labelMap X D).hom := by
    have hn := kan_adjunction_formula X (continuousSetProfiniteSheaf D)
      (continuousSetSheaf X D) (e.hom.app _ ≫ σ)
    rw [he] at hn
    change _ = (profiniteToProEtOf X).op.lanUnit.app _ ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op α at hn
    exact hn.symm.trans (by
      ext S b
      exact hσ S.unop b)
  have hleg (U : X.ProEt) (S : Profinite.{u})
      (φ : U ⟶ (profiniteToProEtOf X).obj S) (b : C(S, D)) :
      α.app (op U) (relativeProfiniteSetKanLeg X
        (continuousSetProfiniteSheaf D) U S φ b) =
      (b.comp (continuousSetRelativeTestProjection X S)).comp φ.left.base.hom := by
    have h := congrArg (fun f ↦ f.app (op S)) hα
    change ((profiniteToProEtOf X).op.lanUnit.app
      (continuousSetProfiniteSheaf D).obj).app (op S) ≫
        α.app (op ((profiniteToProEtOf X).obj S)) = (labelMap X D).hom.app (op S) at h
    have hn := α.naturality φ.op
    have heq := congrArg (fun f ↦
      ((profiniteToProEtOf X).op.lanUnit.app
        (continuousSetProfiniteSheaf D).obj).app (op S) ≫ f) hn
    rw [← Category.assoc, ← Category.assoc, h] at heq
    exact ConcreteCategory.congr_hom heq b
  refine ⟨α, hleg, rfl, ?_⟩
  intro _ _ U _ hU
  obtain ⟨φU, hφU, hfac⟩ := affine_labels X U
  have hrep : ∀ z : ((relativeProfiniteSetKan X).obj
      (continuousSetProfiniteSheaf D)).obj (op U),
      ∃ c : C(ConnectedComponents U.left, D),
        relativeProfiniteSetKanLeg X (continuousSetProfiniteSheaf D) U
          (Profinite.of (ConnectedComponents U.left)) φU c = z := by
    intro z
    obtain ⟨S, φ, b, hb⟩ := kan_representative X (continuousSetProfiniteSheaf D) U z
    obtain ⟨g, rfl⟩ := hfac S φ
    refine ⟨b.comp g.hom.hom, ?_⟩
    exact (leg_change X (continuousSetProfiniteSheaf D) U _ S g φU b).symm.trans hb
  have hnormal (c : C(ConnectedComponents U.left, D)) :
      α.app (op U) (relativeProfiniteSetKanLeg X
        (continuousSetProfiniteSheaf D) U
        (Profinite.of (ConnectedComponents U.left)) φU c) =
      c.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    rw [hleg, ContinuousMap.comp_assoc, hφU]
  have hc : Function.Bijective (fun c : C(ConnectedComponents U.left, D) ↦
      c.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) :=
    (continuousMapPresheafEquivOfTotallyDisconnectedSpace D U.left).symm.bijective
  have hb : Function.Bijective (α.app (op U)) := by
    constructor
    · intro z w h
      obtain ⟨c, rfl⟩ := hrep z
      obtain ⟨d, rfl⟩ := hrep w
      rw [hnormal, hnormal] at h
      rw [hc.injective h]
    · intro f
      obtain ⟨c, hc⟩ := hc.surjective f
      exact ⟨_, (hnormal c).trans hc⟩
  have hw : PointLanWeaklyContractible X U := by
    intro F G f hf
    exact hU f ((Sheaf.isLocallySurjective_iff_epi f).mpr hf)
  have hi := ((proEtale_sheafification_wcontractible_sections X).1
    (continuousSetProfiniteSheaf D) _
    ((profiniteToProEtOf X).op.lanUnit.app (continuousSetProfiniteSheaf D).obj)
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit _ _) U inferInstance hw).1
  have : IsIso ((toSheafify (Scheme.ProEt.topology X)
      ((relativeProfiniteSetKan X).obj (continuousSetProfiniteSheaf D))).app (op U)) := hi
  have hη := (isIso_iff_bijective ((toSheafify (Scheme.ProEt.topology X)
    ((relativeProfiniteSetKan X).obj (continuousSetProfiniteSheaf D))).app (op U))).mp hi
  refine ⟨φU, hφU, hrep, hnormal, hb, hη, ?_⟩
  have heiso : IsIso ((e.hom.app (continuousSetProfiniteSheaf D)).hom.app (op U)) :=
    inferInstance
  have heb := (isIso_iff_bijective _).mp heiso
  exact (Function.Bijective.of_comp_iff _ (heb.comp hη)).mp hb

end AlgebraicGeometry.ProEtale
