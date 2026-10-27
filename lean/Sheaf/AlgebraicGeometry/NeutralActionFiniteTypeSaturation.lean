/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Finite-type saturation under a fibrewise neutral open subgroup

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 6.6 Theorem 2 and its proof (a),
printed pp.164--165; 6.4 before Lemma 3, printed pp.154--155; 10.1, printed p.290
(blueprint: lem-sfb-neutral-action-finite-type-saturation).

Products in `Over S` are fibre products over S. The open X is characterized by the
point-set image of multiplication. The fibre clauses use its inverse image under the
first pullback projection, the underlying open of its base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Saturating a quasi-compact open by the finite-type neutral open subgroup gives a
smooth separated finite-type open, stable under that subgroup. Its geometric fibres
are unions of connected components, and each such component is one orbit even on
points over an algebraically closed extension of the geometric base field.

Source: BLR, Néron Models, 6.6 Theorem 2 and proof (a), pp.164--165; 6.4 before
Lemma 3, pp.154--155; 10.1, p.290; Stacks Tag 0B7R for geometric identity components
(blueprint: lem-sfb-neutral-action-finite-type-saturation).

Proof:
1. Restrict smoothness to H. The action H ×_S G → G is the second projection after
   the automorphism (h,g) ↦ (h,hg), with inverse (h,g) ↦ (h,h⁻¹g). Its restriction
   to H ×_S W is smooth, hence flat and locally of finite presentation and therefore
   open (lem-weil-pbc-smooth-restrict-open-subschemes, lem-pc-proper-base-change,
   lem-pc-smooth-flat, lem-weil-pbc-flat-lfp-open).
2. H is quasi-compact over S. Its pullback to W is quasi-compact, and W is
   quasi-compact, so H ×_S W is quasi-compact. Its continuous image is quasi-compact
   (lem-pc-quasi-compact-base-change,
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open,
   lem-weil-pbc-continuous-image-quasi-compact). Give this open image its open-scheme structure.
3. Restrict smoothness and separatedness to X. Smoothness implies local finite
   presentation, hence local finite type. Since S is affine and thus quasi-separated,
   quasi-compactness of X implies quasi-compactness of X → S, proving finite type
   (lem-trf-immersion-over-separated-base, lem-weil-pbc-affine-scheme-qcqs,
   lem-weil-pbc-qcqs-morphism-permanence, def-sbc-locally-finite-presentation).
4. The identity gives W ⊆ X. For a point of H ×_S X, pass to its residue field,
   then to a residue field of a nonempty fibre of H ×_S W → X. There x = aw,
   hence hx = (ha)w is again in X (lem-weil-pbc-base-change-image). Multiplication
   factors uniquely through the open X, and its unit and associativity identities
   descend through the open immersion (lem-weil-pbc-morphism-factors-through-open-subscheme).
5. On a geometric fibre F with neutral component C = H, C is clopen, geometrically
   irreducible and compatible with field extensions
   (lem-sfb-locally-algebraic-group-identity-component). Each component D of F has a
   rational closed point g by the Jacobson and residue-field lemmas
   (lem-sc-lft-over-field-jacobson-space, lem-weil-pbc-closed-point-residue-field-base).
   Right translation identifies C with D, by connectedness and the clopen property.
6. Base change preserves the multiplication image (lem-weil-pbc-base-change-image).
   If D meets X, the smooth nonempty open D ∩ X has a rational point w
   (lem-pc-rational-points-dense). Thus D = Cw, and stability gives D ⊆ X.
7. The translation C → D base changes to an isomorphism after every algebraically
   closed extension Ω/k (def-pc-base-change). Write x = aw and y = bw; then
   h = ba⁻¹ belongs to H(Ω) and hx = y. The empty W case gives empty X and
   vacuous component and orbit assertions. -/
theorem neutralAction_finiteType_saturation
    (S : Scheme.{u}) [IsAffine S] [IsLocallyNoetherian S]
    (G H : Over S) [GrpObj G] [GrpObj H]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    (i : H ⟶ G) [IsMonHom i] [IsOpenImmersion i.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Set.range ((Over.pullback s).map i).left =
        connectedComponent (GrpObj.onePoint ((Over.pullback s).obj G)))
    (W : G.left.Opens) (hW : IsCompact (W : Set G.left)) :
    ∃ X : G.left.Opens,
      (X : Set G.left) = Set.range
        ((lift (fst H (Over.mk (W.ι ≫ G.hom)) ≫ i)
          (snd H (Over.mk (W.ι ≫ G.hom)) ≫ Over.homMk (V := G) W.ι) ≫ μ[G]).left) ∧
      W ≤ X ∧
      Smooth (X.ι ≫ G.hom) ∧ IsSeparated (X.ι ≫ G.hom) ∧
      LocallyOfFiniteType (X.ι ≫ G.hom) ∧ QuasiCompact (X.ι ≫ G.hom) ∧
      (∃ a : ModObj H (Over.mk (X.ι ≫ G.hom)),
        a.smul ≫ Over.homMk (V := G) X.ι =
          lift (fst H (Over.mk (X.ι ≫ G.hom)) ≫ i)
            (snd H (Over.mk (X.ι ≫ G.hom)) ≫ Over.homMk (V := G) X.ι) ≫ μ[G]) ∧
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
        (∀ z : ((Over.pullback s).obj G).left,
          (pullback.fst G.hom s) z ∈ X →
          connectedComponent z ⊆ (pullback.fst G.hom s) ⁻¹' (X : Set G.left)) ∧
        ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
          (x y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶
            (Over.pullback s).obj G),
          Set.range x.left ⊆ (pullback.fst G.hom s) ⁻¹' (X : Set G.left) →
          Set.range y.left ⊆ (pullback.fst G.hom s) ⁻¹' (X : Set G.left) →
          y.left (IsLocalRing.closedPoint Ω) ∈
            connectedComponent (x.left (IsLocalRing.closedPoint Ω)) →
          ∃ h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶
              (Over.pullback s).obj H,
            (h ≫ (Over.pullback s).map i) * x = y := by
  sorry

end AlgebraicGeometry
