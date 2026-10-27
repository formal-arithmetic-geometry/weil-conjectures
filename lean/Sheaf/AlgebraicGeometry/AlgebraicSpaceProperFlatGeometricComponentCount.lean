/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Geometric component counts for proper flat algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 0E1E;
Spaces over Fields, Tags 0A12, 0A13 and 0A10
(blueprint: lem-sfb-space-proper-flat-geometric-component-count).

Fibres are actual presheaf fibre products, with the existing field-valued point quotient
and atlas topology. A residue-field homomorphism specifies each field extension and its
canonical map to the base scheme. No scheme representability of the source is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper flat finitely presented algebraic-space family with reduced geometric fibres
has finite, locally constant geometric connected-component counts, independent of the
algebraically closed residue-field extension. Empty fibres have count zero; count one is
exactly nonempty geometric connectedness, and its locus is open.
Source: Stacks, Tag 0E1E and Spaces over Fields, Tags 0A12, 0A13 and 0A10
(blueprint: lem-sfb-space-proper-flat-geometric-component-count).

Proof:
1. At t put k = κ(t). Embed any two algebraically closed extensions into a common
   algebraically closed extension using lem-weil-common-extension-fields and
   def-weil-algebraic-closure. Pullback associativity from
   lem-trf-space-fibre-products-etale-covers identifies the resulting fibres.
   By lem-sfb-space-sepclosed-components-base-change their component sets are in
   bijection, proving independence, including every chosen algebraic closure.
2. By lem-sfb-space-proper-base-change the geometric fibre is proper. It is reduced
   by hypothesis. Apply lem-sfb-space-proper-global-algebra-components: its finitely
   many clopen components identify its global algebra with one copy of the algebraically
   closed field per component. The dimension of this algebra is its component count,
   including dimension zero for the empty fibre.
3. Apply lem-sfb-proper-flat-space-derived-base-change to the structure sheaf, which
   is quasi-coherent, finitely presented and flat over the base. Its derived direct
   image is perfect (def-pc-perfect-complex), and derived fibres compute the fibre
   direct image. Left exactness of sections identifies degree-zero cohomology with
   ordinary global sections. Thus the degree-zero fibre Betti number is the count.
4. By lem-sc-perfect-jump-loci this Betti number is upper semicontinuous and commutes
   with base change. By lem-sfb-space-flat-proper-components-lower-semicontinuous the
   component count is lower semicontinuous. Intersect the open neighbourhood where
   the count is at least n(t) with the open sublevel set where it is less than n(t)+1.
   The count is constant there, proving local constancy without a Noetherian assumption.
5. One component means a nonempty connected point space. By the separably closed
   component theorem a connected algebraically closed fibre remains connected after
   further extension. For any extension L/k, amalgamate L with an algebraic closure
   and then algebraically close the common extension. The map from that fibre onto
   the L-fibre is continuous and surjective by lem-a1-space-point-open-calculus and
   its fibre-product point-image formula. Its image is nonempty and connected.
   Conversely geometric connectedness includes the algebraic-closure fibre. The
   empty fibre has no components, hence count zero.
6. The geometric-connectedness locus is the inverse image of {1} under the locally
   constant count, so is open. No smoothness or scheme-source assumption was used. -/
theorem proper_flat_geometric_component_count {S : Scheme.{u}} (T : Over S)
    (Y : AlgebraicSpace S) (h : Y ⟶ schemeSpace T)
    (hproper : MapIsProper h) (hflat : MapIsFlat h)
    (hlfp : MapIsLocallyOfFinitePresentation h)
    (hqc : MapIsQuasiCompact h.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal h.hom.hom))
    (hred : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left)
      (U : Over S) (b : yoneda.obj U ⟶
        Limits.pullback h.hom.hom (yoneda.map (Over.homMk
          (U := Over.mk (a ≫ T.hom)) (V := T) a rfl))),
      IsEtale b → ∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x)) :
    ∃ n : T.left → ℕ,
      (∀ (t : T.left) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (ι : T.left.residueField t ⟶ CommRingCat.of Ω),
        Finite (ConnectedComponents (Point (Limits.pullback h.hom.hom
          (yoneda.map (Over.homMk
            (U := Over.mk ((Spec.map ι ≫ T.left.fromSpecResidueField t) ≫ T.hom))
            (V := T) (Spec.map ι ≫ T.left.fromSpecResidueField t) rfl))))) ∧
        Nat.card (ConnectedComponents (Point (Limits.pullback h.hom.hom
          (yoneda.map (Over.homMk
            (U := Over.mk ((Spec.map ι ≫ T.left.fromSpecResidueField t) ≫ T.hom))
            (V := T) (Spec.map ι ≫ T.left.fromSpecResidueField t) rfl))))) = n t) ∧
      IsLocallyConstant n ∧
      (∀ t : T.left,
        IsEmpty (Point (Limits.pullback h.hom.hom (yoneda.map (Over.homMk
          (U := Over.mk (T.left.fromSpecResidueField t ≫ T.hom))
          (V := T) (T.left.fromSpecResidueField t) rfl)))) → n t = 0) ∧
      (∀ t : T.left, n t = 1 ↔
        ∀ (L : Type u) [Field L] (ι : T.left.residueField t ⟶ CommRingCat.of L),
          ConnectedSpace (Point (Limits.pullback h.hom.hom
            (yoneda.map (Over.homMk
              (U := Over.mk ((Spec.map ι ≫ T.left.fromSpecResidueField t) ≫ T.hom))
              (V := T) (Spec.map ι ≫ T.left.fromSpecResidueField t) rfl))))) ∧
      IsOpen {t : T.left |
        ∀ (L : Type u) [Field L] (ι : T.left.residueField t ⟶ CommRingCat.of L),
          ConnectedSpace (Point (Limits.pullback h.hom.hom
            (yoneda.map (Over.homMk
              (U := Over.mk ((Spec.map ι ≫ T.left.fromSpecResidueField t) ≫ T.hom))
              (V := T) (Spec.map ι ≫ T.left.fromSpecResidueField t) rfl))))} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
