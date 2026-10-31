/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Normalized labels of relative profinite test schemes

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; Bhatt--Scholze,
Lemma 4.2.13(1), pp. 30--31 (blueprint: lem-sfb-relative-profinite-test-labels).

The existing `profiniteToProEtOf` supplies the chosen inverse-limit model. All
comparison maps below are specified by their projections, and labels are specified
by the evaluation-prime homeomorphism. No new copy of the test-object construction
or the locally constant ring is introduced.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private noncomputable def label (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((profiniteToProEtOf X).obj S).left, S) :=
  (ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩).comp
      (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom

private lemma label_natural (X : Scheme.{u}) (S T : Profinite.{u}) (v : S ⟶ T) :
    (label X T).comp ((profiniteToProEtOf X).map v).left.base.hom =
      v.hom.hom.comp (label X S) := by
  have h : ((profiniteToProEtOf X).map v).left ≫
      pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X) =
      pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) ≫
        profiniteToScheme.map v := by
    dsimp [profiniteToProEtOf, MorphismProperty.Over.pullback]
    exact pullback.lift_fst _ _ _
  ext z
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (( ((profiniteToProEtOf X).map v).left ≫ pullback.fst _ _) z)).1 = _
  erw [h]
  exact profiniteProjection_natural S T v _

private noncomputable def overMapEquiv (X U : Scheme.{u}) (uX : U ⟶ X)
    (S : Profinite.{u}) :
    (Over.mk uX ⟶ (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S)) ≃
      (U ⟶ profiniteToScheme.obj S) where
  toFun f := f.left ≫ pullback.fst _ _
  invFun f := Over.homMk (pullback.lift f uX (specULiftZIsTerminal.hom_ext _ _)) (by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simp)
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd]
      exact f.w.symm
  right_inv f := by simp

private lemma label_bijective (X U : Scheme.{u}) [IsAffine U] (uX : U ⟶ X)
    (S : Profinite.{u}) :
    Function.Bijective (fun φ : Over.mk uX ⟶
        (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S) ↦
      (label X S).comp φ.left.base.hom) := by
  have he : (fun φ : Over.mk uX ⟶
      (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S) ↦
        (label X S).comp φ.left.base.hom) =
      (overMapEquiv X U uX S).trans (affineMapEquiv U S) := by
    funext φ
    ext x
    exact (affineMapEquiv_apply U S (φ.left ≫ pullback.fst _ _) x).symm
  rw [he]
  exact ((overMapEquiv X U uX S).trans (affineMapEquiv U S)).bijective

private noncomputable def pointRingIso :
    CommRingCat.of (LocallyConstant point.{u} ℤ) ≅ CommRingCat.of (ULift.{u} ℤ) :=
  ({ toFun := fun f ↦ ULift.up (f PUnit.unit)
     invFun := fun z ↦ LocallyConstant.const _ z.down
     left_inv := fun f ↦ by ext x; exact congrArg f (Subsingleton.elim _ _)
     right_inv := fun z ↦ rfl
     map_mul' := fun _ _ ↦ rfl
     map_add' := fun _ _ ↦ rfl } :
    LocallyConstant point.{u} ℤ ≃+* ULift.{u} ℤ).toCommRingCatIso

private noncomputable def pointSchemeIso : profiniteToScheme.obj point.{u} ≅ specZ.{u} :=
  (Scheme.Spec.mapIso pointRingIso.op).symm

private lemma finite_labels (X : Scheme.{u}) (S : Profinite.{u}) [Finite S] :
    ∃ (j : S → (X ⟶ ((profiniteToProEtOf X).obj S).left)),
      Nonempty (IsColimit (Cofan.mk ((profiniteToProEtOf X).obj S).left j)) ∧
      (∀ s : S, j s ≫ ((profiniteToProEtOf X).obj S).hom = 𝟙 X ∧
        j s ≫ pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) =
          toSpecZ X ≫ Spec.map (CommRingCat.ofHom
            ((Int.castRingHom (ULift.{u} ℤ)).comp (LocallyConstant.evalRingHom s)))) ∧
      (∀ s : S, (label X S).comp (j s).base.hom = ContinuousMap.const X s) := by
  let F := profiniteToProEtOf X ⋙ Scheme.ProEt.forget X
  have : PreservesFiniteLimits (profiniteToProEtOf X) :=
    (profinite_test_object_functor X).1
  have : PreservesFiniteLimits F := inferInstance
  have := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have : (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite)
      (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
  have : F.IsContinuous (coherentTopology Profinite) (Scheme.proetaleTopology.over X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
  have : PreservesColimitsOfShape (Discrete S) F :=
    coproducts_of_continuous F (Scheme.proetaleTopology.over X) S
  let c : Cofan (fun _ : S ↦ point.{u}) := Cofan.mk S (pointMap S)
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk _ (fun t ↦ CompHausLike.ofHom _
      ⟨fun s ↦ t.inj s PUnit.unit, continuous_of_discreteTopology⟩) ?_ ?_
    · intro t s
      ext x
      exact congrArg (t.inj s) (Subsingleton.elim _ _)
    · intro t m hm
      ext s
      exact ConcreteCategory.congr_hom (hm s) PUnit.unit
  let e : F.obj point ≅ Over.mk (𝟙 X) :=
    (Profinite.isTerminalPUnit.isTerminalObj F _).uniqueUpToIso Over.mkIdTerminal
  let G := Over.forget X
  let j (s : S) : X ⟶ ((profiniteToProEtOf X).obj S).left :=
    e.inv.left ≫ (F.map (pointMap S s)).left
  have he : e.inv.left ≫ ((profiniteToProEtOf X).obj point).hom = 𝟙 X := e.inv.w
  have hi := isColimitCofanMkObjOfIsColimit (F ⋙ G) _ _ hc
  have hj : IsColimit (Cofan.mk ((profiniteToProEtOf X).obj S).left j) := by
    refine Cofan.IsColimit.mk _ (fun t ↦ hi.desc
      (Cofan.mk t.pt (fun s ↦ e.hom.left ≫ t.inj s))) ?_ ?_
    · intro t s
      change (e.inv.left ≫ (F.map (pointMap S s)).left) ≫ _ = _
      rw [Category.assoc]
      erw [hi.fac (Cofan.mk t.pt _) ⟨s⟩]
      change (e.inv.left ≫ e.hom.left) ≫ t.inj s = _
      simp [← Over.comp_left]
    · intro t m hm
      apply hi.hom_ext
      rintro ⟨s⟩
      change (F.map (pointMap S s)).left ≫ m = _
      erw [hi.fac (Cofan.mk t.pt _) ⟨s⟩]
      have h := congrArg (fun q ↦ e.hom.left ≫ q) (hm s)
      simpa [j, ← Category.assoc, ← Over.comp_left] using h
  refine ⟨j, ⟨hj⟩, ?_, ?_⟩
  · intro s
    constructor
    · change (e.inv.left ≫ (F.map (pointMap S s)).left) ≫ _ = _
      rw [Category.assoc]
      erw [(F.map (pointMap S s)).w]
      exact he
    · have ha : toSpecZ (profiniteToScheme.obj point.{u}) = pointSchemeIso.hom :=
        specULiftZIsTerminal.hom_ext _ _
      have hp : e.inv.left ≫ pullback.fst
          (toSpecZ (profiniteToScheme.obj point.{u})) (toSpecZ X) =
          toSpecZ X ≫ pointSchemeIso.inv := by
        apply (cancel_mono pointSchemeIso.hom).mp
        rw [Category.assoc, ← ha, pullback.condition]
        change e.inv.left ≫ ((profiniteToProEtOf X).obj point).hom ≫ toSpecZ X = _
        erw [← Category.assoc, he]
        simp
      have hv : pointSchemeIso.inv ≫ profiniteToScheme.map (pointMap S s) =
          Spec.map (CommRingCat.ofHom ((Int.castRingHom (ULift.{u} ℤ)).comp
            (LocallyConstant.evalRingHom s))) := by
        change Spec.map pointRingIso.hom ≫ Spec.map
          (CommRingCat.ofHom (LocallyConstant.comapRingHom (pointMap S s).hom.hom)) = _
        rw [← Spec.map_comp]
        congr 1
      change (e.inv.left ≫ ((profiniteToProEtOf X).map (pointMap S s)).left) ≫ _ = _
      rw [Category.assoc]
      have hm : ((profiniteToProEtOf X).map (pointMap S s)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) =
          pullback.fst (toSpecZ (profiniteToScheme.obj point.{u})) (toSpecZ X) ≫
            profiniteToScheme.map (pointMap S s) := by
        dsimp [profiniteToProEtOf, MorphismProperty.Over.pullback]
        exact pullback.lift_fst _ _ _
      erw [hm, ← Category.assoc, hp, Category.assoc, hv]
  · intro s
    have h := congrArg (fun q ↦ q.comp e.inv.left.base.hom)
      (label_natural X point S (pointMap S s))
    exact h.trans (by ext x; rfl)

/-- The relative profinite tests have canonical, base-change compatible labels and
represent continuous maps on every affine scheme over the base.

Source: Hemo--Richarz--Scholbach, Example 3.1, p. 6; Bhatt--Scholze,
Lemma 4.2.13(1), pp. 30--31 (blueprint: lem-sfb-relative-profinite-test-labels).

Proof plan, following the node's seven steps:
1. `def-sfb-profinite-test-objects` and `lem-weil-pbc-profinite-test-object-functor`
identify the finite-quotient limit with the base change of `Spec LC(S,Z)`.
Exchange the two projections by `def-pc-fibre-product`; their uniqueness gives
naturality in both the scheme and the profinite parameter.
2. Apply `lem-weil-pbc-locally-constant-prime-spectrum`. Precomposition pulls the
prime evaluated at `(s,p)` back to the prime evaluated at `(v(s),p)`, proving label
naturality for `def-sfb-profinite-to-proetale`.
3. `lem-weil-pbc-finite-affine-coproduct-spectrum` identifies evaluation at s with
the s-th coprojection. Base change by `lem-sc-etale-fibre-product-base-change-coproduct`
and `lem-weil-pbc-scheme-coproduct-family` gives the finite summands and their labels.
4. The fibre-product universal property identifies the iterated base change with
Y[S], preserving the Y and absolute-test projections. It therefore preserves labels.
5. An affine is qcqs by `lem-weil-pbc-affine-scheme-qcqs`, hence spectral by
`lem-weil-pbc-qcqs-scheme-spectral`. Its component quotient is profinite by
`lem-pe-spectral-components-profinite`. Continuous maps to S factor uniquely through
that quotient, since S is totally disconnected; the factor is continuous by the
quotient topology, also for the empty affine.
6. By `def-weil-affine-spectrum`, affine maps to `Spec LC(S,Z)` are ring maps.
`def-weil-pbc-profinite-locally-constant-hom-equiv` identifies them with continuous
component maps, with exactly the evaluation-prime normalization. The fibre-product
universal property gives the asserted bijection over X.
7. Associativity of composition and step 2 give naturality. Apply the inverse
bijection to the component quotient to obtain phi_U; injectivity gives its stated
factorization property. Empty test spaces and empty affines are included. -/
theorem relative_profinite_test_labels :
    ∃ (e : ∀ (X : Scheme.{u}) (S : Profinite.{u}),
        ((profiniteToProEtOf X).obj S).left ≅
          pullback (toSpecZ X) (toSpecZ (profiniteToScheme.obj S)))
      (r : ∀ (X : Scheme.{u}) (S : Profinite.{u}),
        C(((profiniteToProEtOf X).obj S).left, S)),
      (∀ (X : Scheme.{u}) (S : Profinite.{u}),
        (e X S).hom ≫ pullback.fst _ _ = ((profiniteToProEtOf X).obj S).hom ∧
        (e X S).hom ≫ pullback.snd _ _ =
          pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)) ∧
      (∀ (X : Scheme.{u}) (S : Profinite.{u})
        (z : ((profiniteToProEtOf X).obj S).left),
        r X S z = ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
          ((pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)) z)).1) ∧
      (∀ (X : Scheme.{u}) (S : Profinite.{u}) [Finite S],
        ∃ (j : S → (X ⟶ ((profiniteToProEtOf X).obj S).left)),
          Nonempty (IsColimit (Cofan.mk ((profiniteToProEtOf X).obj S).left j)) ∧
          (∀ s : S, j s ≫ ((profiniteToProEtOf X).obj S).hom = 𝟙 X ∧
            j s ≫ pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) =
              toSpecZ X ≫ Spec.map (CommRingCat.ofHom
                ((Int.castRingHom (ULift.{u} ℤ)).comp (LocallyConstant.evalRingHom s)))) ∧
          (∀ s : S, (r X S).comp (j s).base.hom = ContinuousMap.const X s)) ∧
      (∀ (X : Scheme.{u}) (S T : Profinite.{u}) (v : S ⟶ T),
        (r X T).comp ((profiniteToProEtOf X).map v).left.base.hom =
          v.hom.hom.comp (r X S)) ∧
      (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (S : Profinite.{u}),
        ∃ (b : pullback f ((profiniteToProEtOf X).obj S).hom ≅
            ((profiniteToProEtOf Y).obj S).left),
          b.inv ≫ pullback.fst _ _ = ((profiniteToProEtOf Y).obj S).hom ∧
          b.inv ≫ pullback.snd _ _ ≫
              pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) =
            pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ Y) ∧
          (r X S).comp ((b.inv ≫ pullback.snd _ _).base.hom) = r Y S) ∧
      (∀ (X U : Scheme.{u}) [IsAffine U] (uX : U ⟶ X) (S : Profinite.{u}),
        Function.Bijective (fun φ : Over.mk uX ⟶
            (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S) ↦
          (r X S).comp φ.left.base.hom)) ∧
      (∀ (X U : Scheme.{u}) [IsAffine U] (uX : U ⟶ X)
        (S T : Profinite.{u}) (v : S ⟶ T)
        (φ : Over.mk uX ⟶ (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S)),
        (r X T).comp
            (φ.left ≫ ((profiniteToProEtOf X).map v).left).base.hom =
          v.hom.hom.comp ((r X S).comp φ.left.base.hom)) ∧
      (∀ (X U V : Scheme.{u}) [IsAffine U] [IsAffine V]
        (uX : U ⟶ X) (vX : V ⟶ X) (k : Over.mk vX ⟶ Over.mk uX)
        (S : Profinite.{u})
        (φ : Over.mk uX ⟶ (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S)),
        (r X S).comp (k.left ≫ φ.left).base.hom =
          ((r X S).comp φ.left.base.hom).comp k.left.base.hom) ∧
      (∀ (X U : Scheme.{u}) [IsAffine U] (uX : U ⟶ X),
        ∃ (φU : Over.mk uX ⟶ (Scheme.ProEt.forget X).obj
            ((profiniteToProEtOf X).obj (Profinite.of (ConnectedComponents U)))),
          (r X (Profinite.of (ConnectedComponents U))).comp φU.left.base.hom =
              ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ ∧
          ∀ (S : Profinite.{u}) (g : Profinite.of (ConnectedComponents U) ⟶ S)
            (φ : Over.mk uX ⟶
              (Scheme.ProEt.forget X).obj ((profiniteToProEtOf X).obj S)),
            (r X S).comp φ.left.base.hom =
                g.hom.hom.comp
                  ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ →
              φ = φU ≫ (Scheme.ProEt.forget X).map ((profiniteToProEtOf X).map g)) := by
  classical
  refine ⟨fun X S ↦ pullbackSymmetry (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X),
    label, ?_, ?_, ?_, label_natural, ?_,
    label_bijective, ?_, ?_, ?_⟩
  · intro X S
    change (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ = pullback.snd _ _ ∧ _
    exact ⟨by simp, by simp⟩
  · intro X S z
    rfl
  · exact finite_labels
  · intro X Y f S
    let a := toSpecZ (profiniteToScheme.obj S)
    let b : pullback f ((profiniteToProEtOf X).obj S).hom ≅
        ((profiniteToProEtOf Y).obj S).left :=
      pullbackSymmetry f (pullback.snd a (toSpecZ X)) ≪≫
        pullbackLeftPullbackSndIso a (toSpecZ X) f ≪≫
        pullback.congrHom rfl (comp_toSpecZ f)
    have hfst : b.inv ≫ pullback.fst _ _ = ((profiniteToProEtOf Y).obj S).hom := by
      change b.inv ≫ pullback.fst f (pullback.snd a (toSpecZ X)) =
        pullback.snd a (toSpecZ Y)
      simp [b]
    have hsnd : b.inv ≫ pullback.snd _ _ ≫ pullback.fst a (toSpecZ X) =
        pullback.fst a (toSpecZ Y) := by
      change b.inv ≫ pullback.snd f (pullback.snd a (toSpecZ X)) ≫
        pullback.fst a (toSpecZ X) = pullback.fst a (toSpecZ Y)
      simp [b]
    refine ⟨b, hfst, hsnd, ?_⟩
    ext y
    change ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
      ((b.inv ≫ pullback.snd _ _ ≫ pullback.fst a (toSpecZ X)) y)).1 = _
    rw [hsnd]
    rfl
  · intro X U hU uX S T v φ
    have h := congrArg (fun q ↦ q.comp φ.left.base.hom) (label_natural X S T v)
    exact h
  · intro X U V hU hV uX vX k S φ
    rfl
  · intro X U hU uX
    obtain ⟨φU, hφU⟩ := (label_bijective X U uX
      (Profinite.of (ConnectedComponents U))).surjective
        ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
    refine ⟨φU, hφU, ?_⟩
    intro S g φ hφ
    apply (label_bijective X U uX S).injective
    change (label X S).comp φ.left.base.hom = _
    erw [hφ]
    have h := congrArg (fun q ↦ q.comp φU.left.base.hom)
      (label_natural X (Profinite.of (ConnectedComponents U)) S g)
    change _ = (label X S).comp
      (φU.left ≫ ((profiniteToProEtOf X).map g).left).base.hom
    erw [← hφU]
    exact h.symm

end AlgebraicGeometry.ProEtale
