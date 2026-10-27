/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Sheaf.AlgebraicGeometry.NormalCrossingsBranchCount
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Compactification.StrictTransform
import Sheaf.AlgebraicGeometry.NCMaximalBranchBlowup
import Sheaf.TraceFormula.CoordinateMaximalBranchStratum
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.StrictTransformFlatBaseChange
import Sheaf.AlgebraicGeometry.PermissibleBoundaryPreservation
import Sheaf.TraceFormula.EtaleComponentCoordinateIdentification
import Sheaf.AlgebraicGeometry.CartierDivisorNowhereDense
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry
import Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple
import Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation
import Sheaf.AlgebraicGeometry.ProjectiveBundleComposition
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.Blowup.FlatBaseChange

/-! # Relative maximal-branch strictification

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII 4.1.2--4.1.8,
4.2.8--4.2.9, pp.117--121, and X Lemma 2.2, pp.149--150
(blueprint: lem-sfb-relative-nc-maximal-branch-strictification).

The coordinate substitution retains the exceptional coordinate, replaces the other
center coordinates by its products with their ratios, and fixes the remaining coordinates.
The theorem records the entire ordinary tower, including a terminal Cartier-center blowup.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The coordinate substitution of the j-th chart of the blowup of the first m coordinate
hyperplanes' intersection. The input coordinates are z_j, v_k for k < m and k ≠ j,
and the unchanged z_k for k ≥ m, in their original slots. This is an actual map of
Mathlib affine spaces, not an unspecified comparison.
Source: ILO VIII Lemma 4.2.9, p.121
(blueprint: lem-sfb-relative-nc-maximal-branch-strictification). -/
def maximalBranchChartMap (F : Type u) [Field F] (r m : ℕ) (j : Fin r) :
    AffineSpace (ULift.{u} (Fin r)) (Spec (.of F)) ⟶
      AffineSpace (ULift.{u} (Fin r)) (Spec (.of F)) :=
  AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin r)) (Spec (.of F)) ↘ _) fun k ↦
    if k.down.val < m ∧ k.down ≠ j then
      AffineSpace.coord (Spec (.of F)) (ULift.up j) * AffineSpace.coord _ k
    else AffineSpace.coord _ k

/-- An arbitrary-field smooth normal-crossings pair admits equivariant strictification by
successive maximal-old-branch blowups. Left field actions are converted contravariantly
using the inverse group element under Spec. All boundary equalities are ideal equalities;
union is infimum, and reduced inverse image is radical after comap. The Cartesian chart
squares identify the actual blowup charts and the coordinate functions v_k = z_k/z_j.
The generic-point stalk-map clause expresses birationality of each map and of the composite.

Source: ILO VIII 4.1.2--4.1.8, pp.117--118, 4.2.8--4.2.9, pp.120--121,
and the smooth-pair variant used in X Lemma 2.2, pp.149--150
(blueprint: lem-sfb-relative-nc-maximal-branch-strictification).

Proof:
1. Start with D = B and empty H. Smooth coordinate parameters give normal crossings;
   smoothness over F gives regularity, and finite type gives Noetherianity.
2. The maximal-branch blowup lemma supplies a positive attained maximum and its reduced
   closed locus. Reduced etale pullback and flat going down select exactly the old factors.
   The coordinate maximal-stratum lemma identifies the center with their intersection.
   This intersection is smooth over F; etale source descent proves smoothness of the center.
   Its intrinsic branch-count description makes it invariant, including semilinear actions.
3. Flat base change identifies the blowup on every etale chart. Going down verifies the
   generic-dominance hypothesis of strict-transform flat base change. The j-th coordinate
   chart has the substitution recorded above, full boundary the product of all new
   coordinates, and old strict transform the product of the m-1 ratio coordinates.
   Away from the center the blowup is an isomorphism. Discard unit factors and project
   smoothly to the remaining coordinates to retain pointed smooth boundary charts.
4. Permissible boundary preservation gives regularity and H+ = (b^(-1)(H union Z))red.
   Strict-transform closure commutes with finite union, so B+ = D+ union H+.
5. Etale component-coordinate identification assigns distinct factors to the regular
   components of H+. Their intersections are smooth of the expected codimension in the
   coordinate charts; etale descent gives relative strict normal crossings, including
   the empty intersection. This uses no regular-implies-smooth assertion over F.
6. The Cartier complement is nonempty and dense. The integral blowup projective-geometry
   lemma gives integral stages and projectivity in the projective-bundle convention;
   projectivity gives finite type. The common dense open gives the function-field isomorphism.
7. Each action preserves the Rees algebra degreewise. Relative Proj functoriality lifts it.
   On homogeneous localization fractions substitution respects identity and composition,
   proving the group law. The old and accumulated divisors remain invariant.
8. The next old branch count is at most m-1. For m=1 its equation is the empty product,
   hence the old transform is empty, even for an identity blowup. Induction terminates
   after at most the initial maximum; for empty B use the zero-length tower.
9. Noetherian stages are qcqs. Projective-bundle composition gives projectivity of every
   composite. Complement isomorphisms compose, proving birationality and equivariance.
-/
theorem exists_relative_nc_maximal_branch_strictification
    (F : Type u) [Field F] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of F)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (B : X.IdealSheafData) (hB : B.IsInvertible) (hBred : IsReduced B.subscheme)
    (hcharts : ∀ x : X, ∃ (W : Scheme.{u}) (e : W ⟶ X) (w : W)
      (r : ℕ) (c : W ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))),
      Etale e ∧ e w = x ∧ Smooth c ∧ c ≫ (AffineSpace _ _ ↘ Spec (.of F)) = e ≫ f ∧
      (∀ k : ULift.{u} (Fin r), W.Γevaluation w (c.appTop (AffineSpace.coord _ k)) = 0) ∧
      B.comap e = Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {∏ k : ULift.{u} (Fin r), c.appTop (AffineSpace.coord _ k)}))
    (J : Type v) [Group J] [Finite J] (rho : J →* (F ≃+* F)) (a : J →* Aut X)
    (ha : ∀ g : J, (a g).hom ≫ f =
      f ≫ Spec.map (CommRingCat.ofHom (rho g⁻¹).toRingHom))
    (hBa : ∀ g : J, B.comap (a g).hom = B) :
    ∃ (T : OrdinaryBlowupTower X)
      (D H : ∀ i : Fin (T.length + 1), (T.level i).IdealSheafData)
      (m : Fin T.length → ℕ) (act : ∀ i : Fin (T.length + 1), J →* Aut (T.level i)),
      D 0 = B.comap T.initial.hom ∧ H 0 = ⊤ ∧
      (∀ g : J, (act 0 g).hom ≫ T.initial.hom = T.initial.hom ≫ (a g).hom) ∧
      (∀ i : Fin (T.length + 1),
        IsIntegral (T.level i) ∧ IsRegularScheme (T.level i) ∧
        Smooth (T.toBase i ≫ f) ∧ LocallyOfFiniteType (T.toBase i ≫ f) ∧
        QuasiCompact (T.toBase i ≫ f) ∧
        (B.comap (T.toBase i)).radical = D i ⊓ H i ∧
        (H i).IsSmoothStrictNormalCrossingsDivisor (T.toBase i ≫ f) ∧
        (∀ g : J, (act i g).hom ≫ T.toBase i = T.toBase i ≫ (a g).hom) ∧
        (∀ g : J, (D i).comap (act i g).hom = D i ∧
          (H i).comap (act i g).hom = H i) ∧
        (∀ x : T.level i, ∃ (W : Scheme.{u}) (e : W ⟶ T.level i) (w : W)
          (r : ℕ) (c : W ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))),
          Etale e ∧ e w = x ∧ Smooth c ∧
          c ≫ (AffineSpace _ _ ↘ Spec (.of F)) = e ≫ T.toBase i ≫ f ∧
          (∀ k : ULift.{u} (Fin r),
            W.Γevaluation w (c.appTop (AffineSpace.coord _ k)) = 0) ∧
          ((B.comap (T.toBase i)).radical).comap e = Scheme.IdealSheafData.ofIdealTop
            (Ideal.span {∏ k : ULift.{u} (Fin r), c.appTop (AffineSpace.coord _ k)})) ∧
        IsProjectiveBundle (T.toBase i) ∧ IsIso (T.toBase i ∣_ B.support.compl) ∧
        Dense ((T.toBase i ⁻¹ᵁ B.support.compl : (T.level i).Opens) : Set (T.level i)) ∧
        (∃ eta : T.level i, IsGenericPoint eta Set.univ ∧
          IsGenericPoint (T.toBase i eta) Set.univ ∧ IsIso ((T.toBase i).stalkMap eta))) ∧
      (∀ i : Fin T.length,
        Nonempty (D i.castSucc).subscheme ∧ 1 ≤ m i ∧
        (∀ x : T.level i.castSucc, (D i.castSucc).ncBranchCount x ≤ m i) ∧
        (∃ x : T.level i.castSucc, (D i.castSucc).ncBranchCount x = m i) ∧
        (T.center i).radical = T.center i ∧
        (∀ x : T.level i.castSucc,
          x ∈ (T.center i).support ↔ (D i.castSucc).ncBranchCount x = m i) ∧
        Smooth ((T.center i).subschemeι ≫ T.toBase i.castSucc ≫ f) ∧
        (∀ g : J, (T.center i).comap (act i.castSucc g).hom = T.center i) ∧
        D i.succ =
          (AlgebraicGeometry.strictTransformMap (D i.castSucc).subschemeι
            (T.center i).blowupMap (T.center i).support.compl).ker.comap
              (T.blowupIso i).hom ∧
        H i.succ = (((H i.castSucc ⊓ T.center i).comap
          (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ))).radical) ∧
        (∀ y : T.level i.succ, (D i.succ).ncBranchCount y ≤ m i - 1) ∧
        (m i = 1 → D i.succ = ⊤ ∧
          ((D i.castSucc).comap
            (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ))).support ≤
              (H i.succ).support) ∧
        (∀ g : J, (act i.succ g).hom ≫
          T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) =
          T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ≫
            (act i.castSucc g).hom) ∧
        IsProjectiveBundle (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)) ∧
        IsIso (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ∣_
          ((B.comap (T.toBase i.castSucc)).radical).support.compl) ∧
        (∃ eta : T.level i.succ, IsGenericPoint eta Set.univ ∧
          IsGenericPoint
            (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) eta) Set.univ ∧
          IsIso ((T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)).stalkMap
            eta)) ∧
        (∀ x : T.level i.castSucc, x ∈ (T.center i).support →
          ∃ (W : Scheme.{u}) (e : W ⟶ T.level i.castSucc) (w : W)
            (r : ℕ) (hmr : m i ≤ r)
            (c : W ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))),
            Etale e ∧ e w = x ∧ Smooth c ∧
            c ≫ (AffineSpace _ _ ↘ Spec (.of F)) = e ≫ T.toBase i.castSucc ≫ f ∧
            (∀ k : ULift.{u} (Fin r),
              W.Γevaluation w (c.appTop (AffineSpace.coord _ k)) = 0) ∧
            ((B.comap (T.toBase i.castSucc)).radical).comap e =
              Scheme.IdealSheafData.ofIdealTop
                (Ideal.span {∏ k : ULift.{u} (Fin r), c.appTop (AffineSpace.coord _ k)}) ∧
            (D i.castSucc).comap e = Scheme.IdealSheafData.ofIdealTop
              (Ideal.span {∏ k : Fin (m i),
                c.appTop (AffineSpace.coord _ (ULift.up (Fin.castLE hmr k)))}) ∧
            (T.center i).comap e = Scheme.IdealSheafData.ofIdealTop
              (Ideal.span (Set.range (fun k : Fin (m i) ↦
                c.appTop (AffineSpace.coord _ (ULift.up (Fin.castLE hmr k)))))) ∧
            ∃ (U : Fin (m i) → Scheme.{u})
              (q : ∀ j : Fin (m i), U j ⟶ pullback
                (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)) e)
              (d : ∀ j : Fin (m i),
                U j ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))),
              (∀ y : (pullback
                (T.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ)) e : Scheme.{u}),
                ∃ (j : Fin (m i)) (z : U j), q j z = y) ∧
              ∀ j : Fin (m i), IsOpenImmersion (q j) ∧ Smooth (d j) ∧
                IsPullback (q j ≫ pullback.snd _ _) (d j) c
                  (maximalBranchChartMap F r (m i) (Fin.castLE hmr j)) ∧
                ((B.comap (T.toBase i.succ)).radical).comap
                  (q j ≫ pullback.fst _ _) = Scheme.IdealSheafData.ofIdealTop
                    (Ideal.span {∏ k : ULift.{u} (Fin r),
                      (d j).appTop (AffineSpace.coord _ k)}) ∧
                (D i.succ).comap (q j ≫ pullback.fst _ _) =
                  Scheme.IdealSheafData.ofIdealTop
                    (Ideal.span {∏ k ∈ Finset.univ.filter (fun k : Fin (m i) ↦ k ≠ j),
                      (d j).appTop
                        (AffineSpace.coord _ (ULift.up (Fin.castLE hmr k)))}))) ∧
      D (Fin.last T.length) = ⊤ ∧
      (B.comap (T.toBase (Fin.last T.length))).radical = H (Fin.last T.length) ∧
      (IsEmpty B.subscheme → T.length = 0) ∧
      (Nonempty B.subscheme → ∃ M : ℕ, T.length ≤ M ∧
        (∀ x : X, B.ncBranchCount x ≤ M) ∧ ∃ x : X, B.ncBranchCount x = M) := by
  sorry

end AlgebraicGeometry
