/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleWeilTransport
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RestrictionWeilGroup
public import Sheaf.Paper.RealSheavesSetup
public import Sheaf.Paper.CurveWeilMiddleExtension
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.ProEtale.Adic.DenseOpenUnit
import Sheaf.Paper.GaloisLisseRepresentations
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.RepresentationTheory.Rep.Basic
import Sheaf.Paper.LisseAdicFiberFunctors
import Sheaf.Paper.LisseModuleSheaves
import Sheaf.Paper.LisseTensorScalarExtension
import Sheaf.RepresentationTheory.LAdic
import Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import Sheaf.AlgebraicGeometry.NormalOpenLisseImage
import Sheaf.CategoryTheory.Galois.GaloisTransitive
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import Sheaf.Paper.EtaleWeilFundamentalRepresentation
import Sheaf.Paper.EtaleWeilSheafEquivalence
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.GroupTheory.WeilGroup

/-!
# Dense open immersions and fundamental groups

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-boundary,
lemma lem-wf-dense-open-pi1-surjective, clauses (1)--(5)
(blueprint: lem-wf-dense-open-pi1-surjective).

Normality is the stalkwise normal-domain condition, including at singular points.
The group models and every restriction map use the existing finite-etale fibre functor.
The Weil-group map is specified by its underlying pair, which determines it uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry

/-- Connected finite etale covers stay connected on a dense open of a connected normal
Noetherian scheme. Source: blueprint clause (1)
(blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step 0 uses rem-pc-regular-normal (2): the finitely many normal integral clopen
components of V reduce to one by connectedness and the geometric point. In Step (1a),
lem-fin-etale-normal-components makes a connected finite etale cover integral. Its image
is nonempty, open and closed, hence all of V. Its pullback to the nonempty open is a
nonempty open of an integral scheme and is therefore connected. -/
theorem Scheme.FiniteEtale.isConnected_pullback_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)
    (P : V.FiniteEtale) (hP : IsConnected P) :
    IsConnected ((Scheme.FiniteEtale.pullback j).obj P) := by
  sorry

/-- Surjectivity of the canonical map on fundamental groups at a geometric point of the open.
Source: blueprint clause (1) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (1a) is the preceding connected-cover assertion. Step (1b) uses
thm-galois-fundamental, lem-fet-galois-category and lem-galois-transitive. The continuous
image is compact and closed. A proper image lies in a proper open subgroup by
lem-wf-profinite-closed-subgroup-intersection-open. By cor-galois-open-subgroups its coset
set is a connected cover whose restriction is disconnected, contradicting Step (1a). -/
theorem Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U) :
    Function.Surjective (Scheme.FiniteEtale.fiberAutBaseChange j s) := by
  sorry

/-- The canonical map of Weil groups: its pair formula specifies the map induced by finite
etale pullback, its degree equality, its surjectivity on geometric kernels, and its
surjectivity on the whole Weil group. The fibre-product expressions below are exactly the
bodies of the recorded weilGroup and weilGroupDeg abbreviations; using them avoids
requiring geometric connectedness of the open as an extra hypothesis.
Source: blueprint clause (2) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: In Step (2), lem-sc-scheme-over-field-universally-open shows that the geometric
open is dense. Step (1) makes the geometric fundamental-group map surjective.
lem-weil-geometrically-connected-algebraic-closure checks geometric connectedness of both
schemes. Pullback preserves constant covers and geometric Frobenius, so the arithmetic
fundamental-group map induces (g,n) to (rho(g),n) on the fibre-product Weil groups of
def-wf-weil-group and def-wf-fundamental-representation. The exact sequence
lem-wf-weil-group-exact-sequence identifies the kernels with the geometric groups.
Given w of degree n, lift its degree in the source Weil group, then lift the quotient
of w by that image through the geometric surjection; their product lifts w. -/
theorem Scheme.FiniteEtale.weilGroup_dense_open_surjective
    {k₀ : Type u} [Field k₀] [Finite k₀]
    {U V : Scheme.{u}} (p : V ⟶ Spec (.of k₀)) (pU : U ⟶ Spec (.of k₀))
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [ConnectedSpace p.geometricFiber]
    (hV : ∀ x : p.geometricFiber,
      IsDomain (p.geometricFiber.presheaf.stalk x) ∧
        IsIntegrallyClosed (p.geometricFiber.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base) (hp : j ≫ p = pU)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ U) :
    ∃ ρ :
        (Scheme.FiniteEtale.constantCoverAction pU s (Aut (Scheme.FiniteEtale.fiber s))).weilGroup
          (Scheme.FiniteEtale.geometricFrobenius pU s) →*
        (Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroup
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j)),
      (∀ w, (ρ w).val = (Scheme.FiniteEtale.fiberAutBaseChange j s w.val.1, w.val.2)) ∧
      (∀ w,
        (Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j)) (ρ w) =
        (Scheme.FiniteEtale.constantCoverAction pU s
          (Aut (Scheme.FiniteEtale.fiber s))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius pU s) w) ∧
      (∀ w ∈
        ((Scheme.FiniteEtale.constantCoverAction p (s ≫ j)
          (Aut (Scheme.FiniteEtale.fiber (s ≫ j)))).weilGroupDeg
            (Scheme.FiniteEtale.geometricFrobenius p (s ≫ j))).ker,
        ∃ w' ∈
          ((Scheme.FiniteEtale.constantCoverAction pU s
            (Aut (Scheme.FiniteEtale.fiber s))).weilGroupDeg
              (Scheme.FiniteEtale.geometricFrobenius pU s)).ker,
          ρ w' = w) ∧
      Function.Surjective ρ := by
  sorry

/-- The finite-level adjunction unit of a lisse sheaf is invertible on a normal scheme.
Source: blueprint clause (3) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (3) evaluates on affine etale T over V and uses
lem-fin-etale-normal-components to decompose T into normal integral clopen components.
Every component meets the open. By cor-galois-lisse-representations sections are the
invariants of its geometric stalk. Step (1) says that restriction has the same group
image, hence the same invariants. Thus the unit is an isomorphism on the etale basis. -/
theorem Etale.isIso_lisse_unit_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf N] :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app N) := by
  sorry

/-- The algebraic l-adic adjunction unit of a lisse sheaf is invertible on a normal scheme.
Source: blueprint clause (3) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Apply the finite-level assertion to every quotient of a compatible finite-level
O_E-model (E finite over Q_l), as in def-weil-pbc-constructible-complexes. Naturality of
the units makes their inverses compatible with all transition maps. Ordinary direct
image preserves the inverse limit. Inverting l and extending coefficients to Qbar_l
preserves the two inverse identities. This is Step (3), last paragraph. -/
theorem ProEtale.isIso_lisse_unit_of_normal_dense_open
    {U V : Scheme.{u}} [ConnectedSpace V] [IsNoetherian V]
    (hV : ∀ x : V, IsDomain (V.presheaf.stalk x) ∧
      IsIntegrallyClosed (V.presheaf.stalk x))
    (j : U ⟶ V) [IsOpenImmersion j] (hj : DenseRange j.base)
    (l : ℕ) [Fact l.Prime] (N : ProEtale.AdicSheaf l V)
    (hN : ProEtale.IsAdicLisseSheaf N) :
    IsIso ((ProEtale.adicUpperStarLowerStarAdjunction l j).unit.app N) := by
  sorry

/-- Restriction between the chapter's curves is fully faithful on lisse Weil sheaves,
and preserves irreducibility among lisse subsheaves. Full faithfulness is expressed by
bijectivity of every Hom map between lisse objects, without choosing a new lisse category.
Source: blueprint clause (4) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (4) uses d-real-setup and lem-sc-smooth-normal to make the geometric curve
normal and integral. Its nonempty open is another such curve and is dense. Under
prop-wf-weil-sheaf-representation-equivalence, pullback is restriction of the generic
stalk representation along the surjection of Step (2). Surjectivity gives equality of
equivariant Hom spaces and of invariant subspaces, proving both assertions. -/
theorem WeilSheaf.dense_open_lisse_restriction
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [U.Over (Spec (.of D.k₀))] [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j]
    [j.IsOver (Spec (.of D.k₀))] [Nonempty U] :
    (∀ F : WeilSheaf D.k₀ D.l C, F.IsLisse →
      ((WeilSheaf.upperStar j).obj F).IsLisse) ∧
    (∀ (F G : WeilSheaf D.k₀ D.l C), F.IsLisse → G.IsLisse →
      Function.Bijective ((WeilSheaf.upperStar j).map : (F ⟶ G) → _)) ∧
    (∀ F : WeilSheaf D.k₀ D.l C, F.IsIrreducibleLisse →
      ((WeilSheaf.upperStar j).obj F).IsIrreducibleLisse) := by
  sorry

/-- The geometric version of restriction on curves, with algebraic l-adic coefficients.
The geometric morphism is the base change of the open immersion to the chosen algebraic
closure. Source: blueprint clause (4) (blueprint: lem-wf-dense-open-pi1-surjective).
Proof: As in Step (4), the geometric curves are normal integral and Step (1) gives the
surjection on their fundamental groups. Under cor-galois-lisse-representations the
Hom spaces are unchanged, and precisely the same subspaces are invariant. -/
theorem ProEtale.dense_open_geometric_lisse_restriction
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [U.Over (Spec (.of D.k₀))] [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j]
    [j.IsOver (Spec (.of D.k₀))] [Nonempty U] :
    (∀ F : ProEtale.AdicSheaf D.l (D.geometricCurve C),
      ProEtale.IsAdicLisseSheaf F →
      ProEtale.IsAdicLisseSheaf
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).obj F)) ∧
    (∀ (F G : ProEtale.AdicSheaf D.l (D.geometricCurve C)),
      ProEtale.IsAdicLisseSheaf F → ProEtale.IsAdicLisseSheaf G →
      Function.Bijective
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).map : (F ⟶ G) → _)) ∧
    (∀ F : ProEtale.AdicSheaf D.l (D.geometricCurve C),
      ProEtale.IsIrreducibleAdicLocalSystem F →
      ProEtale.IsIrreducibleAdicLocalSystem
        ((ProEtale.adicUpperStar D.l
          (pullback.map (U ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
            (C ↘ Spec (.of D.k₀))
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j (𝟙 _) (𝟙 _)
            ((Category.comp_id _).trans (comp_over j _).symm)
            (Category.comp_id _))).obj F)) := by
  sorry

/-- The ordinary middle extension from a nonempty open of a chapter curve is constructible
at every finite coefficient level. Source: blueprint clause (5)
(blueprint: lem-wf-dense-open-pi1-surjective).
Proof: Step (5) uses d-real-setup to get a nonempty smooth finite-type curve. Its connected
geometric base change surjects onto it, so it is connected; lem-sc-smooth-normal makes it
normal. rem-pc-regular-normal (2) then makes it integral. The open is normal and the
finite-level sheaf is finite locally constant. Apply lem-fin-normal-open-lisse-image;
its ordinary direct image is exactly the finite-level middle extension of
 def-wf-middle-extension. -/
theorem Scheme.isConstructible_middleExtension_of_curve_lisse
    (D : RealSheaves.Setup.{u, v})
    {U C : Scheme.{u}} [C.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C) (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F] :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F) := by
  sorry

end AlgebraicGeometry
