/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidModule
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Sheaf.Paper.IntegralResidueMatePasting

/-!
# Cartesian groupoid pushforward and the ordinary adjunction

Source: Stacks Project, Groupoids, Tags 03LJ and 09VH
(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction).

The functors below have the prescribed underlying module functors. Their descent
maps and both directions of their Hom equivalence are fixed by ordinary module operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical pullback comparison for a commuting groupoid-morphism square.
Source: Stacks, Tag 03LJ, canonical tensor pullback identifications
(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction). -/
@[irreducible] def groupoidMorphismPullbackComparison {U R U' R' : Scheme.{u}}
    (f₀ : U ⟶ U') (f₁ : R ⟶ R') (a : R ⟶ U) (a' : R' ⟶ U')
    (h : f₁ ≫ a' = a ≫ f₀) (M : U'.Modules) :
    (groupoidModulePullback a).obj ((groupoidModulePullback f₀).obj M) ≅
      (groupoidModulePullback f₁).obj ((groupoidModulePullback a').obj M) := by
  unfold groupoidModulePullback
  exact (Modules.tensorPullbackSectionComp a f₀).symm.app M ≪≫
    eqToIso (congrArg (fun k : R ⟶ U' ↦ (Modules.tensorPullback k).obj M) h.symm) ≪≫
    (Modules.tensorPullbackSectionComp f₁ a').app M

/-- Pull back the actual descent map, inserting the canonical square comparisons.
Source: Stacks, Tag 03LJ (blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction). -/
@[irreducible] def groupoidMorphismPullbackDescent {U R U' R' : Scheme.{u}}
    (f₀ : U ⟶ U') (f₁ : R ⟶ R') (s t : R ⟶ U) (s' t' : R' ⟶ U')
    (hs : f₁ ≫ s' = s ≫ f₀) (ht : f₁ ≫ t' = t ≫ f₀) (M : U'.Modules)
    (beta : (groupoidModulePullback t').obj M ≅ (groupoidModulePullback s').obj M) :
    (groupoidModulePullback t).obj ((groupoidModulePullback f₀).obj M) ⟶
      (groupoidModulePullback s).obj ((groupoidModulePullback f₀).obj M) :=
  (groupoidMorphismPullbackComparison f₀ f₁ t t' ht M).hom ≫
    (groupoidModulePullback f₁).map beta.hom ≫
    (groupoidMorphismPullbackComparison f₀ f₁ s s' hs M).inv

/-- The existing ordinary base-change map in the groupoid module coordinates.
This is defined for any commuting square; no invertibility is assumed.
Source: Stacks, Tag 09VH and Tag 08HY
(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction). -/
@[irreducible] def groupoidMorphismBaseChange {U R U' R' : Scheme.{u}}
    (f₀ : U ⟶ U') (f₁ : R ⟶ R') (a : R ⟶ U) (a' : R' ⟶ U')
    (h : f₁ ≫ a' = a ≫ f₀) (N : U.Modules) :
    (groupoidModulePullback a').obj ((Modules.pushforward f₀).obj N) ⟶
      (Modules.pushforward f₁).obj ((groupoidModulePullback a).obj N) := by
  unfold groupoidModulePullback
  exact Modules.moduleBaseChangeMap f₀ f₁ a' a h.symm N

/-- The section-normalized ordinary adjunction in the existing groupoid coordinates.
Source: Stacks, Tags 0096 and 09VH
(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction). -/
@[irreducible] def groupoidModuleOrdinaryAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    groupoidModulePullback f ⊣ Modules.pushforward f := by
  unfold groupoidModulePullback
  exact Modules.tensorPullbackSectionAdjunction f

/-- Cartesian groupoid pushforward restricts the ordinary module-sheaf adjunction.
Source: Stacks, Tags 03LJ and 09VH
(blueprint: lem-sfb-cartesian-groupoid-pushforward-adjunction).

Proof:
1. Inversion turns the Cartesian target square into the Cartesian source square.
   Pullback preserves quasi-coherence (lem-weil-pbc-module-pullback-quasi-coherent).
   Pull the identity, cocycle and equivariance equations back along f₀, f₂ and f₁;
   the groupoid-morphism equations give the descent equations and define F.
2. Use the canonical comparisons for every commuting square, given by the ordinary
   adjunction mate (def-weil-pbc-adjunction-mate, lem-pc-module-pullback-adjunction).
   Their pasting follows by inverseMate_pasting (new-integral-residue-mate-pasting)
   and associativity of tensor pullback. Identity squares give identity comparisons
   by the ordinary adjunction triangle identities. These comparisons are natural.
3. The transpose of b_a composed with a'-pullback of the transpose of h is a-pullback
   of h, under the canonical square comparison. This is the counit mate identity
   (lem-amb-mate-unit-counit), naturality and the ordinary transpose identities.
4. Qcqs pushforward preserves quasi-coherence (pqf-lem-pushforward-qcoh).
   Flat base change in degree zero (lem-pc-flat-base-change-cohom) makes b_s and b_t
   invertible. Define the direct-image descent map as b_t; f₁,*(gamma); b_s inverse.
   Naturality of the comparisons takes equivariant maps to equivariant maps.
5. The two projection squares on composable arrows are Cartesian by unique arrow
   lifting, using the target square and inversion. The arrow map is qcqs by base
   change (lem-weil-pbc-qcqs-morphism-permanence), and the primed projections are flat
   (lem-weil-pbc-flat-morphism-base-change). Degree-zero flat base change therefore
   makes their comparisons invertible on s-pullback and t-pullback of N.
6. Paste the identity square with the source and target squares. The two resulting
   identity comparisons identify the identity pullback of the direct-image descent
   with f₀,* of the identity pullback of gamma. Thus its identity law holds.
7. On composable arrows, paste each projection square and the composition square
   with the source and target squares. Naturality identifies the three transported
   descent maps with f₂,* of the corresponding pullbacks of gamma. The cocycle for
   gamma and cancellation of the invertible outer comparisons give the cocycle
   for the direct image. This constructs G on objects and underlying maps.
8. Multiply equivariance of an ordinary transpose by b_s and transpose under the
   f₁ adjunction. Step 3 and naturality (lem-sfb-adjunction-transpose-square) identify
   it with equivariance of the original map. This equivalence proves both ordinary
   transpose directions. Restrict the ordinary Hom bijections; naturality is inherited
   in both variables, and hence they specify the asserted adjunction. -/
theorem exists_cartesian_groupoid_pushforward_adjunction
    (S : Scheme.{u}) {U R U' R' : Scheme.{u}}
    (p : U ⟶ S) (q : R ⟶ S) (p' : U' ⟶ S) (q' : R' ⟶ S)
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (s' t' : R' ⟶ U') (e' : U' ⟶ R') (i' : R' ⟶ R') (c' : pullback s' t' ⟶ R')
    (_hsS : s ≫ p = q) (_htS : t ≫ p = q)
    (_hsS' : s' ≫ p' = q') (_htS' : t' ≫ p' = q')
    (hG : IsGroupoid s t e i c) (hG' : IsGroupoid s' t' e' i' c')
    (f₀ : U ⟶ U') (f₁ : R ⟶ R')
    (_hfS : f₀ ≫ p' = p) (_hfS' : f₁ ≫ q' = q)
    (hs : f₁ ≫ s' = s ≫ f₀) (ht : f₁ ≫ t' = t ≫ f₀)
    (_he : e ≫ f₁ = f₀ ≫ e') (_hi : i ≫ f₁ = f₁ ≫ i')
    (_hc : c ≫ f₁ =
      pullback.map s t s' t' f₁ f₁ f₀ hs.symm ht.symm ≫ c')
    [QuasiCompact f₀] [QuasiSeparated f₀] [Flat s'] [Flat t']
    (_hcart : IsPullback f₁ t t' f₀) :
    ∃ (F : GroupoidModule s' t' e' i' c' hG' ⥤ GroupoidModule s t e i c hG)
      (G : GroupoidModule s t e i c hG ⥤ GroupoidModule s' t' e' i' c' hG')
      (hF : F ⋙ GroupoidModule.forgetToModules =
        GroupoidModule.forgetToModules ⋙ groupoidModulePullback f₀)
      (hP : G ⋙ GroupoidModule.forgetToModules =
        GroupoidModule.forgetToModules ⋙ Modules.pushforward f₀),
      (∀ M : GroupoidModule s' t' e' i' c' hG',
        (groupoidModulePullback t).map
            (eqToHom (congrArg (fun H ↦ H.obj M) hF).symm) ≫
          (F.obj M).beta.hom ≫
          (groupoidModulePullback s).map (eqToHom (congrArg (fun H ↦ H.obj M) hF)) =
        groupoidMorphismPullbackDescent f₀ f₁ s t s' t' hs ht M.moduleObj M.beta) ∧
      (∀ N : GroupoidModule s t e i c hG,
        IsIso (groupoidMorphismBaseChange f₀ f₁ t t' ht N.moduleObj) ∧
        IsIso (groupoidMorphismBaseChange f₀ f₁ s s' hs N.moduleObj) ∧
        groupoidMorphismBaseChange f₀ f₁ t t' ht N.moduleObj ≫
            (Modules.pushforward f₁).map N.beta.hom =
          (groupoidModulePullback t').map
              (eqToHom (congrArg (fun H ↦ H.obj N) hP).symm) ≫
            (G.obj N).beta.hom ≫
            (groupoidModulePullback s').map (eqToHom (congrArg (fun H ↦ H.obj N) hP)) ≫
            groupoidMorphismBaseChange f₀ f₁ s s' hs N.moduleObj) ∧
      ∃ adj : F ⊣ G,
        ∀ (M : GroupoidModule s' t' e' i' c' hG') (N : GroupoidModule s t e i c hG),
          (∀ a : F.obj M ⟶ N,
            (adj.homEquiv M N a).val ≫ eqToHom (congrArg (fun H ↦ H.obj N) hP) =
              (groupoidModuleOrdinaryAdjunction f₀).homEquiv M.moduleObj N.moduleObj
                (eqToHom (congrArg (fun H ↦ H.obj M) hF).symm ≫ a.val)) ∧
          (∀ b : M ⟶ G.obj N,
            eqToHom (congrArg (fun H ↦ H.obj M) hF).symm ≫
                ((adj.homEquiv M N).symm b).val =
              ((groupoidModuleOrdinaryAdjunction f₀).homEquiv
                M.moduleObj N.moduleObj).symm
                  (b.val ≫ eqToHom (congrArg (fun H ↦ H.obj N) hP))) := by
  sorry

end AlgebraicGeometry.Scheme
