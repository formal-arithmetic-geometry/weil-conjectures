/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Proper algebraic spaces admit proper Noetherian approximations

Source: Stacks Project, Spaces and Morphisms of Spaces, Tag 0A0X,
lemma-proper-limit-of-proper-finite-presentation-noetherian, specialized to a scheme base
(blueprint: lem-sfb-space-proper-noetherian-approximation).

The two limiting cones retain the specified source, target and morphism. Finite
presentation includes both quasi-compactness and quasi-separatedness. Stage spaces have
explicit quasi-compact surjective etale atlases, including when they are empty.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical projection of an algebraic space over S to S. Its presheaf map is the
unique map to the Yoneda presheaf of the terminal object (S, identity) of Sch/S.
Source: Stacks Project, Spaces, Tag 025Y; structure maps in Tag 0A0X
(blueprint: lem-sfb-space-proper-noetherian-approximation). -/
def baseSchemeProjection {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X ⟶ schemeSpace (Over.mk (𝟙 S)) :=
  ObjectProperty.homMk
    ⟨(Over.mkIdTerminal.isTerminalObj yoneda (Over.mk (𝟙 S))).from X.obj.obj⟩

/-- Every proper algebraic space over a qcqs scheme is the limit of proper finitely
presented maps of qcqs algebraic spaces over finitely presented integer bases.
Source: Stacks Project, Tag 0A0X,
lemma-proper-limit-of-proper-finite-presentation-noetherian
(blueprint: lem-sfb-space-proper-noetherian-approximation).

Proof:
1. By lem-sfb-proper-space-fixed-base-fp-limit, write X over T as a directed limit
   of proper finitely presented X_k over T, with closed-immersion transitions.
   Apply prop-nagata-noetherian-inverse-system and def-nagata-noetherian-inverse-system
   to T, then lem-weil-pbc-cofiltered-limit-directed-reindex, to obtain affine
   transitions and finite-type integer stages T_j. They are Noetherian, hence
   quasi-separated by lem-weil-pbc-locally-noetherian-quasi-separated and locally
   finitely presented by pqf-lem-lft-fp-locnoeth. Finite type gives quasi-compactness,
   so their structure maps are finitely presented.
2. Descend each X_k by lem-sfb-fp-space-qcqs-base-limit-descent and enlarge the base
   index using lem-sfb-space-qcqs-base-eventually-proper. Properness and finite
   presentation persist by lem-sfb-space-flat-proper-fp-locality. Composition with
   the integer base is finitely presented by lem-sfb-space-separated-fp-composition,
   so the descended models Z are qcqs.
3. Form the category of models (k,j,Z,alpha), where alpha identifies the pullback
   to T with X_k. An arrow consists of larger k,j and a closed immersion into the
   base change of the target model, inducing the given transition of the X_k.
   Closed immersions compose and survive base change by def-weil-closed-immersion;
   lem-trf-space-fibre-products-etale-covers supplies fibre-product identifications.
   These data form a small category in the universes of def-weil-size-convention.
4. It is nonempty by step 2. To refine two models, dominate their k-indices and
   descend the two maps by lem-sfb-fp-space-qcqs-base-limit-descent. Apply
   lem-sfb-space-qcqs-base-descend-closed-immersion after increasing j to make both
   maps closed immersions. Parallel arrows agree after pullback to T; the equality
   clause of descent equalizes them at a later j. Thus the category is cofiltered.
   One can impose any base lower bound, and retain k when both target k's agree.
5. Each source transition factors as a closed immersion followed by an affine
   projection. On affine scheme tests this is a closed subscheme of an affine
   scheme, hence affine by def-weil-closed-immersion. Base transitions are affine.
6. A compatible family of maps from a test space W to the T_j over all models gives
   a unique W to T, by the refinements of step 4 and
   lem-sfb-space-affine-limits-schematic-stages. Pairing this map with each W to Z
   gives W to X_k via alpha. Refinements with fixed k make this independent of the
   model, and refinements with larger k give compatibility. The fixed-base limit
   therefore gives a unique W to X. Conversely W to X gives all these components;
   the constructions are inverse and natural. The limiting arrow is f itself.
7. Reindex this diagram of arrows by lem-weil-pbc-cofiltered-limit-directed-reindex.
   The nonempty directed set, both limits, all affine transitions and all stage
   properties persist. Quasi-compactness supplies the stated etale scheme atlases;
   quasi-separatedness is the absolute affine-test criterion. -/
theorem exists_proper_noetherian_approximation
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (Over.mk (specULiftZIsTerminal.from T)))
    (hf : MapIsProper f) :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (Xs Ts : Iᵒᵖ ⥤ AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      (fs : Xs ⟶ Ts) (πX : (Functor.const Iᵒᵖ).obj X ⟶ Xs)
      (πT : (Functor.const Iᵒᵖ).obj
        (schemeSpace (Over.mk (specULiftZIsTerminal.from T))) ⟶ Ts),
      Nonempty (IsLimit (Cone.mk X πX)) ∧
      Nonempty (IsLimit
        (Cone.mk (schemeSpace (Over.mk (specULiftZIsTerminal.from T))) πT)) ∧
      (∀ (i j : Iᵒᵖ) (a : i ⟶ j), MapIsAffine (Xs.map a) ∧ MapIsAffine (Ts.map a)) ∧
      (∀ i : Iᵒᵖ, πX.app i ≫ fs.app i = f ≫ πT.app i) ∧
      ∀ i : Iᵒᵖ,
        MapIsProper (fs.app i) ∧
        MapIsLocallyOfFinitePresentation (fs.app i) ∧
        MapIsQuasiCompact (fs.app i).hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal (fs.app i).hom.hom) ∧
        MapIsLocallyOfFinitePresentation (baseSchemeProjection (Ts.obj i)) ∧
        MapIsQuasiCompact (baseSchemeProjection (Ts.obj i)).hom.hom ∧
        MapIsQuasiCompact (pullback.diagonal (baseSchemeProjection (Ts.obj i)).hom.hom) ∧
        (∃ (U : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
          (a : yoneda.obj U ⟶ (Xs.obj i).obj.obj),
          CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a) ∧
        IsAbsolutelyQuasiSeparated (Xs.obj i) ∧
        (∃ (V : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
          (b : yoneda.obj V ⟶ (Ts.obj i).obj.obj),
          CompactSpace V.left ∧ IsEtale b ∧ IsSurjective b) ∧
        IsAbsolutelyQuasiSeparated (Ts.obj i) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
