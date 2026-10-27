/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEventuallySurjectiveMap
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound

/-! # Arithmetic models of a group algebraic space and its open

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144;
Stacks Project, spaces-limits.tex, Tags 07SK, 0CN2, 0851 and 07SN
(blueprint: lem-sfb-group-open-arithmetic-model).

Group-valued functors encode the actual group laws, without commutativity.
Restriction along `Over.map` is base change: a test scheme over the new base
already supplies its projection to that base. The final equivalence of membership
identifies the two open subfunctors under the group isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Locally on a locally Noetherian base, a smooth separated finitely presented
integral-fibre group and its fibrewise nonempty quasi-compact open descend to an
arithmetic affine model with constant geometric-fibre dimension.
Source: Deligne, Lemma 4.6, printed p.144; Stacks, Tags 07SK, 0CN2, 0851, 07SN
(blueprint: lem-sfb-group-open-arithmetic-model).

Proof:
1. Choose an affine neighbourhood U of s. Its immersion into S is quasi-compact
   by lem-sfb-noetherian-open-immersion-qc, so V_U is quasi-compact by
   lem-sfb-space-quasicompact-fppf-local. Smoothness, separatedness and finite
   presentation persist by lem-sfb-space-smooth-surjective-fppf-locality,
   lem-sfb-space-flat-proper-fp-locality and lem-sfb-space-separated-fp-composition.
   Apply lemma-nagata-noetherian-inverse-system-affine to express U as the limit
   of spectra of finitely generated integer subalgebras; these are qcqs by
   lem-weil-pbc-affine-scheme-qcqs.
2. Descend G_U by lem-sfb-fp-space-limit-category, and descend its multiplication,
   inverse and identity using the square, cube and terminal models. The equality
   clause makes the finitely many group identities hold at a common later stage.
   Products are finitely presented by the locality and composition lemmas above.
3. Increase the stage using lem-sfb-space-eventually-smooth and
   lem-sfb-space-descend-separated. Descend the quasi-compact open by
   lem-sfb-space-limit-open-cover-descent applied to the cover (G_U,V_U).
   The transition maps are affine, and lem-sfb-space-fp-qcqs-source supplies qcqs.
   The open is locally finitely presented over the base; its limit is surjective,
   so lem-sfb-space-eventually-surjective-map makes it surjective at a later stage.
4. The stage is Noetherian by lem-weil-pbc-finite-type-over-noetherian.
   Its constructible integral-fibre locus, from
   lem-sfb-smooth-space-integral-fibre-locus, contains the image of U. By
   lem-weil-pbc-limit-contained-in-constructible, a later stage lies in that locus.
   Its base-change equality gives integral geometric fibres everywhere.
5. The fibre dimension is locally constant by lem-sfb-smooth-group-fibre-dimension.
   Restrict to a principal affine neighbourhood of the image of s on which it
   equals d, and restrict U to its principal inverse image. The base-change
   clauses of the preceding lemmas preserve all properties, including integrality
   and dimension. Quasi-compactness of the descended open follows from
   lem-sfb-space-qcqs-permanence and lem-sfb-space-quasicompact-fppf-local.
6. The new ring is a localization at one element of a finitely generated integer
   algebra, hence still finitely generated. Apply
   lem-cbc-compactification-geometry-fibre-bound to its finite-type map to Spec Z:
   it is Noetherian of finite Krull dimension. The descended group isomorphism
   identifies the opens by construction. For empty S there is no point s. -/
theorem exists_group_open_arithmetic_model
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    (G : AlgebraicSpace S) (F : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : F ⋙ forget GrpCat ≅ G.obj.obj)
    (hG : IsSmoothIntegralGroupSpace G) (V : OpenSubspace G)
    (hVqc : CompactSpace (Point V.val.toFunctor))
    (hV : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S),
      Nonempty (Point (Limits.pullback (V.val.ι ≫ (groupSpaceProjection G).hom.hom)
        (yoneda.map (Over.homMk (U := Over.mk a) (V := Over.mk (𝟙 S)) a
          (by simp)))))) (s : S) :
    ∃ (U : S.Opens), s ∈ U ∧ IsAffineOpen U ∧
      ∃ (R : CommRingCat.{u}) (f : U.toScheme ⟶ Spec R),
        Algebra.FiniteType ℤ R ∧ IsNoetherian (Spec R) ∧
        (∃ n : ℕ, topologicalKrullDim (Spec R) ≤ (n : WithBot ℕ∞)) ∧
        ∃ (d : ℕ) (G₀ : AlgebraicSpace (Spec R))
          (F₀ : (Over (Spec R))ᵒᵖ ⥤ GrpCat.{u})
          (e₀ : F₀ ⋙ forget GrpCat ≅ G₀.obj.obj) (V₀ : OpenSubspace G₀),
          IsSmoothIntegralGroupSpace G₀ ∧ CompactSpace (Point V₀.val.toFunctor) ∧
          (∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec R),
            topologicalKrullDim (Point
              (Limits.pullback (groupSpaceProjection G₀).hom.hom
                (yoneda.map (Over.homMk (U := Over.mk a)
                  (V := Over.mk (𝟙 (Spec R))) a (by simp))))) = (d : WithBot ℕ∞) ∧
            Nonempty (Point
              (Limits.pullback (V₀.val.ι ≫ (groupSpaceProjection G₀).hom.hom)
                (yoneda.map (Over.homMk (U := Over.mk a)
                  (V := Over.mk (𝟙 (Spec R))) a (by simp)))))) ∧
          ∃ α : (Over.map U.ι).op ⋙ F ≅ (Over.map f).op ⋙ F₀,
            ∀ (T : (Over U.toScheme)ᵒᵖ) (x : F.obj ((Over.map U.ι).op.obj T)),
              e.hom.app ((Over.map U.ι).op.obj T) x ∈
                  V.val.obj ((Over.map U.ι).op.obj T) ↔
                e₀.hom.app ((Over.map f).op.obj T) (α.hom.app T x) ∈
                  V₀.val.obj ((Over.map f).op.obj T) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
