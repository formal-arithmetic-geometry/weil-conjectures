/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Maps to relative profinite test schemes

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-point-components-maps).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

private noncomputable def componentMapEquiv (A : Type u) [TopologicalSpace A]
    (S : Profinite.{u}) : C(A, S) ≃ C(ConnectedComponents A, S) where
  toFun f := ⟨f.continuous.connectedComponentsLift,
    f.continuous.connectedComponentsLift_continuous⟩
  invFun f := f.comp ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  left_inv f := by ext x; simp
  right_inv f := by
    ext x
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    simp

private noncomputable def profiniteHomContinuousEquiv (A S : Profinite.{u}) :
    (A ⟶ S) ≃ C(A, S) where
  toFun f := f.hom.hom
  invFun f := ConcreteCategory.ofHom f

-- Reuse the proved locally constant ring correspondence from Basic. Its inverse
-- sends a ring map to the first coordinate of its map on prime spectra.
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private noncomputable def specMapEquiv (R : CommRingCat.{u}) (S : Profinite.{u}) :
    (Spec R ⟶ profiniteToScheme.obj S) ≃ C(Spec R, S) :=
  Spec.homEquiv.trans ((opEquiv _ _).symm.trans
    ((profiniteLocallyConstantHomEquiv (op R) S).symm.trans
      ((profiniteHomContinuousEquiv _ S).trans (componentMapEquiv (Spec R) S).symm)))
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma specMapEquiv_apply (R : CommRingCat.{u}) (S : Profinite.{u})
    (f : Spec R ⟶ profiniteToScheme.obj S) (x : Spec R) :
    specMapEquiv R S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := by
  sorry
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private noncomputable def affineMapEquiv (A : Scheme.{u}) [IsAffine A]
    (S : Profinite.{u}) : (A ⟶ profiniteToScheme.obj S) ≃ C(A, S) :=
  (Iso.homCongr A.isoSpec (Iso.refl _)).trans
    ((specMapEquiv _ S).trans
      ((Scheme.homeoOfIso A.isoSpec.symm).continuousMapCongr (Homeomorph.refl S)))
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma affineMapEquiv_apply (A : Scheme.{u}) [IsAffine A] (S : Profinite.{u})
    (f : A ⟶ profiniteToScheme.obj S) (x : A) :
    affineMapEquiv A S f x =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm (f x)).1 := by
  sorry
-/

-- Maps over X into the base change are maps into Spec LC(S, Z), since Spec Z is terminal.
private noncomputable def relativeMapEquiv (X : Scheme.{u}) (U : X.ProEt)
    (S : Profinite.{u}) : (U ⟶ (profiniteToProEtOf X).obj S) ≃
      (U.left ⟶ profiniteToScheme.obj S) where
  toFun f := f.left ≫ Limits.pullback.fst _ _
  invFun f := MorphismProperty.Over.homMk
    (Limits.pullback.lift f U.hom (by
      change f ≫ toSpecZ _ = U.hom ≫ toSpecZ X
      exact specULiftZIsTerminal.hom_ext _ _)) (by
        change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
        simp)
  left_inv f := by
    apply MorphismProperty.Over.Hom.ext
    apply Limits.pullback.hom_ext
    · simp
    · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
      rw [Limits.pullback.lift_snd]
      exact f.w.symm
  right_inv f := by simp

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private noncomputable def pointComponentsEquiv (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u}) :
    (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S) :=
  (relativeMapEquiv X U S).trans
    ((affineMapEquiv U.left S).trans (componentMapEquiv U.left S))
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma pointComponentsEquiv_apply (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S : Profinite.{u})
    (f : U ⟶ (profiniteToProEtOf X).obj S) (x : U.left) :
    pointComponentsEquiv X U S f (ConnectedComponents.mk x) =
      ((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm
        ((f.left ≫ Limits.pullback.fst _ _) x)).1 := by
  change (affineMapEquiv U.left S (relativeMapEquiv X U S f)) x = _
  exact affineMapEquiv_apply _ _ _ _
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private lemma profiniteProjection_natural (S T : Profinite.{u}) (b : S ⟶ T)
    (x : profiniteToScheme.obj S) :
    ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (profiniteToScheme.map b x)).1 =
    b (((LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm x).1) := by
  sorry
-/

private lemma relativeMapEquiv_target (X : Scheme.{u}) (U : X.ProEt)
    (S T : Profinite.{u}) (b : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S) :
    relativeMapEquiv X U T (f ≫ (profiniteToProEtOf X).map b) =
      relativeMapEquiv X U S f ≫ profiniteToScheme.map b := by
  change (f.left ≫ ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).map
      (profiniteToProEt.map b)).left) ≫ Limits.pullback.fst _ _ = _
  rw [MorphismProperty.Over.pullback_map_left]
  simp [Category.assoc, relativeMapEquiv, profiniteToProEt]

/-- The component quotient of an affine weakly contractible pro-etale object is profinite.
Maps to `X[S]` are naturally continuous maps from this quotient to `S`.
Weak contractibility means surjectivity on sections of every epimorphism of set sheaves;
the sheaf values live in the larger universe of the small-site convention.
The single family `e` is covariant in profinite targets and contravariant in these objects.

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1), with the finite-quotient argument;
RefactorInstruction, Section 4, proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-point-components-maps).

Proof for stage 3:
1. An affine scheme is compact and quasi-separated, hence spectral by
   lem-weil-pbc-qcqs-scheme-spectral and def-weil-spectral-space. By
   lem-weil-pbc-quasicompact-components-clopen-intersection, distinct components are
   separated by clopens. Clopens are saturated for the component quotient, giving
   Hausdorffness and total disconnectedness. Compactness descends along the quotient.
2. For a finite discrete target, lem-weil-pbc-profinite-test-object-functor identifies
   the test scheme with a coproduct of copies of X. Use
   lem-galois-coproduct-copies-morphisms-clopen to identify its maps with continuous
   finite-valued functions. Such functions factor uniquely through the component
   quotient, and the quotient topology gives continuity of that factor.
3. Present S by its finite quotients. The limit clause of
   lem-weil-pbc-profinite-test-object-functor identifies scheme maps with compatible
   families of finite-stage maps, hence with compatible continuous finite-stage functions.
4. The topological inverse-limit property identifies these families with continuous
   maps to S. Basic opens give continuity. Empty targets give no maps from a nonempty
   source and a unique map from an empty source; singleton targets give a unique map.
5. Precomposition pulls back finite-stage clopen fibres and induces the usual map on
   component quotients. For a target map, compose with any finite quotient of its target
   and factor this finite-valued function through a finite quotient of its source.
   The test-object functor respects these maps. Equality at every finite quotient proves
   both naturality identities. -/
theorem proEtale_point_components_maps (X : Scheme.{u}) :
    (∀ (U : X.ProEt), IsAffine U.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
        Epi f → Function.Surjective (f.hom.app (op U))) →
      CompactSpace (ConnectedComponents U.left) ∧
        T2Space (ConnectedComponents U.left) ∧
        TotallyDisconnectedSpace (ConnectedComponents U.left)) ∧
    ∃ e : ∀ (U : X.ProEt), IsAffine U.left →
        (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U))) →
        ∀ S : Profinite.{u},
          (U ⟶ (profiniteToProEtOf X).obj S) ≃ C(ConnectedComponents U.left, S),
      (∀ (U : X.ProEt) (hU : IsAffine U.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (S T : Profinite.{u}) (b : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e U hU wU T (f ≫ (profiniteToProEtOf X).map b) =
          b.hom.hom.comp (e U hU wU S f)) ∧
      (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (wU : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op U)))
        (wV : ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
          Epi f → Function.Surjective (f.hom.app (op V)))
        (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
        e V hV wV S (a ≫ f) = (e U hU wU S f).comp
          ⟨a.left.continuous.connectedComponentsMap,
            a.left.continuous.connectedComponentsMap_continuous⟩) := by
  sorry

end AlgebraicGeometry.ProEtale
