/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension

/-!
# Normalized proper/open calculus on strict pro-etale towers

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D, 0F7F, 07A7 and 09AE, and the explicit
strict-tower refinement in the blueprint (blueprint: def-cbc-strict-tower-proper-open-arrows).

The index `n : ℕ` denotes positive level `n+1`. All derived categories below localize
complexes of strict towers, rather than forming towers in separate derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- Canonical comparison of the two iterated inverse images around any commutative square.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def squareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    G B i ⋙ G B r ≅ G B p ⋙ G B k :=
  (gComp B r i).symm ≪≫ eqToIso (congrArg (G B) h.symm) ≪≫ gComp B k p

/-- The inverse cartesian open comparison is defined by precisely the open-unit transpose.
Source: Stacks, Tags 09AE and 07A7
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInvApp {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M : Derived B U) :
    (J B j').obj ((G B gU).obj M) ⟶ (G B g).obj ((J B j).obj M) :=
  ((jAdj B j').homEquiv _ _).symm
    ((G B gU).map ((jAdj B j).unit.app M) ≫
      (squareG B gU j' j g h).inv.app ((J B j).obj M))

/-- Naturality of the specified open-unit transpose. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: use naturality of the open unit, the pullback compositor and the adjunction
Hom equivalence. The transposes of both sides are the same naturality square. -/
theorem betaInvApp_naturality {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (M N : Derived B U) (f : M ⟶ N) :
    (G B gU ⋙ J B j').map f ≫ betaInvApp B gU j' j g h N =
      betaInvApp B gU j' j g h M ≫ (J B j ⋙ G B g).map f := by
  apply (jAdj B j').homEquiv_naturality_right_square
  exact ((Functor.whiskerRight (jAdj B j).unit (G B gU)) ≫
    Functor.whiskerLeft (J B j) (squareG B gU j' j g h).inv).naturality f

/-- The inverse comparison as a natural transformation with the specified transpose.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def betaInv {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g) :
    G B gU ⋙ J B j' ⟶ J B j ⋙ G B g where
  app := betaInvApp B gU j' j g h
  naturality := betaInvApp_naturality B gU j' j g h

/-- The unit-normalized comparison is invertible for a cartesian open square and
arbitrary B. Source: Stacks, Tag 09AE and blueprint, second proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: restriction commutes with direct image on the same pulled-back test object.
The two routes are left adjoint to these canonically identified right adjoints.
Their unique unit-preserving comparison is invertible and its inverse has exactly
the displayed transpose. The equalities descend from strict complexes. -/
theorem betaInv_isIso {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : IsIso (betaInv B gU j' j g h) := by
  sorry

/-- Cartesian open base change, oriented as G_g j_! → j'_! G_gU.
Source: Stacks, Tag 09AE (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def beta {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) : J B j ⋙ G B g ≅ G B gU ⋙ J B j' :=
  (@asIso _ _ _ _ (betaInv B gU j' j g h)
    (betaInv_isIso B gU j' j g h hsq)).symm

/-- Evaluation at finite constant coefficients gives exactly the dependency's
unit-normalized open base change. Source: Stacks, Tag 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: transpose inverse comparisons under the open adjunction. Evaluation
commutes with termwise G and J, and evaluates their units to the ordinary units.
The two transposes are identical. Exact localization and the adjunction Hom
bijection give equality of these particular comparisons. -/
theorem beta_evaluation [Finite B] {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) (M : Derived B U) (n : ℕ) :
    (ev B X' n).map ((beta B a j' j g h hsq).hom.app M) ≫
        (evalJ B j' n).hom.app ((G B a).obj M) ≫
        (moduleJ B j').mapDerivedCategory.map ((evalG B a n).hom.app M) =
      (evalG B g n).hom.app ((J B j).obj M) ≫
        (modulePullback B g).mapDerivedCategory.map ((evalJ B j n).hom.app M) ≫
        (singleBeta B a j' j g h hsq).hom.app ((ev B U n).obj M) := by
  sorry

/-- The map of a proper/open commutative square into its canonical fibre product.
Source: Stacks, Tag 0F7B and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable abbrev squareLift {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) := pullback.lift k r h

/-- The induced lift is open and closed; no cartesian or identity-left assumption.
Source: Stacks, Tags 01W6 and 01IQ, and blueprint, third proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: identify the fibre product with p⁻¹(S), an open in W. The map s identifies V
with k(V) inside this open. The base change q of p is separated and q s = r is
proper, so the proper-over-separated theorem makes s proper. A proper open immersion
is closed. This includes the empty open and gives the complementary open component. -/
theorem squareLift_clopen {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    IsOpenImmersion (squareLift k r p i h) ∧ IsClosedImmersion (squareLift k r p i h) := by
  have hopen : IsOpenImmersion (squareLift k r p i h) := by
    have : IsOpenImmersion (squareLift k r p i h ≫ pullback.fst p i) := by
      simpa only [squareLift, pullback.lift_fst] using (inferInstance : IsOpenImmersion k)
    exact IsOpenImmersion.of_comp _ (pullback.fst p i)
  have hproper : IsProper (squareLift k r p i h) := by
    have : IsProper (squareLift k r p i h ≫ pullback.snd p i) := by
      simpa only [squareLift, pullback.lift_snd] using (inferInstance : IsProper r)
    exact IsProper.of_comp _ (pullback.snd p i)
  exact ⟨hopen, IsClosedImmersion.of_isPreimmersion _
    ((squareLift k r p i h).isClosedMap.isClosed_range)⟩

/-- Open part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_open {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsOpenImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).1

/-- Closed part of the clopen factorization. Source: Stacks, Tags 01W6 and 01IQ
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable instance squareLift_closed {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : IsClosedImmersion (squareLift k r p i h) :=
  (squareLift_clopen k r p i h).2

/-- The open-extension unit is invertible. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: on an object lying over the open there is exactly one lift to it, so restriction
of the extension presheaf is the original module. This survives sheafification,
termwise extension to strict towers, and exact localization. -/
theorem jAdj_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (jAdj B j).unit := by
  let Uo : X.ProEt := Scheme.ProEt.mk j
  have : IsOpenImmersion Uo.hom := ‹IsOpenImmersion j›
  let A := coefficients B X
  let R₀ := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  let ae := SheafOfModules.extensionSheafAdjunction R₀ Uo
  have hsub (V : X.ProEt) : Subsingleton (V ⟶ Uo) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).1
    exact f.w.trans g.w.symm
  have hu (M) : IsIso (ae.unit.app M) :=
    SheafOfModules.extensionSheafAdjunction_unit_isIso R₀ Uo hsub M
  have : IsIso ae.unit := NatIso.isIso_of_isIso_app _
  let ff := ae.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  obtain ⟨q, ⟨hq⟩⟩ := Scheme.proEtale_ringed_open_comparison Uo A
  let rc := (sheafCompose (Scheme.ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (constantRingIso B j)
  let e := Scheme.proEtaleScalarEquivalence U rc
  let extAdj := Scheme.proEtaleRingExtensionAdjunction j A (coefficients B U)
    (constantRingIso B j)
  let ee := extAdj.leftAdjointUniq e.symm.toAdjunction
  let t := e.trans q
  let P := Scheme.proEtaleModuleInverseImage j A
  let E := Scheme.proEtaleRingExtension j A (coefficients B U) (constantRingIso B j)
  let hc : modulePullback B j ⋙ t.functor ≅ SheafOfModules.overFunctor R₀ Uo :=
    Functor.associator P E (e.functor ⋙ q.functor) ≪≫
      Functor.isoWhiskerLeft P
        ((Functor.associator E e.functor q.functor).symm ≪≫
          Functor.isoWhiskerRight
            (Functor.isoWhiskerRight ee e.functor ≪≫ e.counitIso) q.functor ≪≫
          Functor.leftUnitor q.functor) ≪≫ hq
  let hr : modulePullback B j ≅ SheafOfModules.overFunctor R₀ Uo ⋙ t.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ t.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight hc t.inverse
  let a := (t.toAdjunction.comp ae).ofNatIsoRight hr.symm
  let jf := (Functor.FullyFaithful.ofFullyFaithful (t.functor ⋙ _)).ofIso
    ((moduleJAdj B j).leftAdjointUniq a).symm
  have := jf.full
  have := jf.faithful
  have : IsIso (moduleJAdj B j).unit := inferInstance
  let towerAdj :=  (moduleJAdj B j).whiskerRight ℕᵒᵖ
  have ht (M) : IsIso (towerAdj.unit.app M) := by
    dsimp only [towerAdj, Adjunction.whiskerRight]
    infer_instance
  have : IsIso towerAdj.unit := NatIso.isIso_of_isIso_app _
  exact (jAdj B j).isIso_unit_of_iso
    ((Functor.mapDerivedCategoryCompIso (towerJ B j) (towerPullback B j)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso towerAdj.unit).symm ≪≫
      Functor.mapDerivedCategoryIdIso (Towers B U))

/-- The canonical map from open extension to direct image is the counit mate of the
inverse open unit. Source: Stacks, Tags 03DI and 09AE
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def openToR {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J B j ⟶ R B j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (J B j) (adj B j).unit ≫
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (@inv _ _ _ _ (jAdj B j).unit (jAdj_unit_isIso B j)) (R B j) ≫
          (Functor.leftUnitor _).hom

/-- For a clopen immersion the canonical open-to-direct-image comparison is invertible.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows).
Proof: over each pro-etale test object split sections into the product of sections on
the inverse image of the clopen image and on its complement. Both extension and direct
image give the first factor with zero second factor. The specified comparison is the
identity on the first factor. The same formula acts termwise on towers and complexes. -/
theorem openToR_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion j] : IsIso (openToR B j) := by
  sorry

/-- The intrinsic clopen component projection, with no arbitrary splitting choice.
Source: Stacks, Tag 09AE and blueprint, fourth proof step
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def pi {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
    [IsClosedImmersion s] : 𝟭 (Derived B X) ⟶ G B s ⋙ J B s :=
  (adj B s).unit ≫ Functor.whiskerLeft (G B s)
    (@inv _ _ _ _ (openToR B s) (openToR_isIso B s))

/-- The normalized non-cartesian open comparison uses beta and the intrinsic clopen
projection, followed by the open and pullback compositors. Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : J B i ⋙ G B p ⟶ G B r ⋙ J B k :=
  (beta B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (G B (pullback.snd p i))
    (pi B (squareLift k r p i h))) (J B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (G B (pullback.snd p i)) (G B (squareLift k r p i h))
      (J B (squareLift k r p i h))).inv (J B (pullback.fst p i)) ≫
  (Functor.associator (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    (J B (squareLift k r p i h)) (J B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
    ((jComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (jCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((gComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (G B) (pullback.lift_snd k r h))).hom) (J B k)

/-- The proper/open comparison is exactly the proper-adjunction mate of alpha.
Source: Stacks, Tags 0F7B and 07A7
(blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def gamma {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : R B r ⋙ J B i ⟶ J B k ⋙ R B p :=
  mateEquiv (adj B r) (adj B p) (alpha B k r p i h)

/-- The base-change arrow is the mate of the canonical pullback-square isomorphism.
Source: Stacks, Tag 07A7 (blueprint: def-cbc-strict-tower-proper-open-arrows). -/
noncomputable def exchange {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    R B p ⋙ G B i ⟶ G B k ⋙ R B r :=
  mateEquiv (adj B p) (adj B r) (squareG B k r p i h).hom


end AlgebraicGeometry.ProEtale.StrictTower
