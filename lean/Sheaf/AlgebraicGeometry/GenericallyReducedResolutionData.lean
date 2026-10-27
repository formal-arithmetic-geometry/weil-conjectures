/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Generically reduced embedded histories and local invariant calculus

Source: Bierstone--Milman--Temkin, Q-universal desingularization, Theorem/Addendum 6.1,
sections 6.1--6.3, pp. 12--15
(blueprint: def-per-generically-reduced-invariant-calculus-data).

This is the data interface, with no existence assertion. Unlike the reduced-input
`EmbeddedResolutionPair`, it admits embedded nilpotents. No reduction is taken at any stage.
Finite disjoint unions are included without connectedness or equidimensionality restrictions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GenericallyReducedResolution

/-- Reducedness only at generic points of irreducible components; the empty scheme is allowed.
Source: BMT section 6.1, with its convention of arbitrary finite-type varieties
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def GenericallyReduced (X : Scheme.{u}) : Prop :=
  ∀ x : X, x ∈ genericPoints X → _root_.IsReduced (X.presheaf.stalk x)

/-- A generically reduced finite-type rational closed subscheme in a smooth separated
finite-type ambient scheme. The universe lift changes only the size of the rational base.
Source: BMT Theorem/Addendum 6.1
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure Pair where
  X : Scheme.{u}
  P : Scheme.{u}
  base : P ⟶ Spec (.of (ULift.{u} ℚ))
  inclusion : X ⟶ P
  closed : IsClosedImmersion inclusion
  genericallyReduced : GenericallyReduced X
  finiteTypeIntrinsic : LocallyOfFiniteType (inclusion ≫ base)
  quasiCompactIntrinsic : QuasiCompact (inclusion ≫ base)
  smooth : Smooth base
  separated : IsSeparated base
  finiteType : LocallyOfFiniteType base
  quasiCompact : QuasiCompact base

/-- An ambient smooth comparison has a cartesian embedded subscheme, with no relative
 dimension condition. Source: BMT 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure AmbientSmoothMap (A B : Pair.{u}) where
  ambient : A.P ⟶ B.P
  intrinsic : A.X ⟶ B.X
  smooth : Smooth ambient
  cartesian : IsPullback intrinsic A.inclusion B.inclusion ambient

/-- Ordinary ambient blowups and actual scheme-theoretic strict transforms, with all
center ideals and their chronological order retained. No later-stage regularity is assumed.
Source: BMT Theorem/Addendum 6.1 and 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure History (A : Pair.{u}) (n : ℕ) where
  ambient : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  intrinsic : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  inclusion : intrinsic ⟶ ambient
  closed : ∀ j, IsClosedImmersion (inclusion.app (op j))
  initialAmbient : ambient.obj (op 0) ≅ A.P
  initialIntrinsic : intrinsic.obj (op 0) ≅ A.X
  initialInclusion : inclusion.app (op 0) ≫ initialAmbient.hom =
    initialIntrinsic.hom ≫ A.inclusion
  center : ∀ j : Fin n, (ambient.obj (op j.castSucc)).IdealSheafData
  centerToIntrinsic : ∀ j : Fin n, (center j).subscheme ⟶ intrinsic.obj (op j.castSucc)
  centerClosed : ∀ j, IsClosedImmersion (centerToIntrinsic j)
  centerInclusion : ∀ j, centerToIntrinsic j ≫ inclusion.app (op j.castSucc) =
    (center j).subschemeι
  ambientBlowup : ∀ j, ambient.obj (op j.succ) ≅ (center j).blowup
  ambientBlowupMap : ∀ j, (ambientBlowup j).hom ≫ (center j).blowupMap =
    ambient.map (homOfLE j.castSucc_le_succ).op
  strictTransform : ∀ j, intrinsic.obj (op j.succ) ≅
    (center j).strictTransform (inclusion.app (op j.castSucc))
  strictTransformMap : ∀ j, (strictTransform j).hom ≫ AlgebraicGeometry.strictTransformMap
    (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
      inclusion.app (op j.succ) ≫ (ambientBlowup j).hom
  strictTransformToSource : ∀ j,
    (strictTransform j).hom ≫ AlgebraicGeometry.strictTransformToSource
      (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
        intrinsic.map (homOfLE j.castSucc_le_succ).op

namespace History

/-- The final strict transform. Source: ILO VIII 2.3.11
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def X {A : Pair.{u}} {n : ℕ} (H : History A n) :
    Scheme.{u} := H.intrinsic.obj (op (Fin.last n))

/-- The final ambient scheme. Source: ILO VIII 2.3.11
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def P {A : Pair.{u}} {n : ℕ} (H : History A n) :
    Scheme.{u} := H.ambient.obj (op (Fin.last n))

/-- The final rational structure map, obtained from the recorded ordinary blowup maps.
Source: ILO VIII 2.3.11 (blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def base {A : Pair.{u}} {n : ℕ} (H : History A n) :
    H.P ⟶ Spec (.of (ULift.{u} ℚ)) :=
  H.ambient.map (homOfLE (Fin.zero_le (Fin.last n))).op ≫ H.initialAmbient.hom ≫ A.base

/-- A one-step extension identifies the whole earlier ambient and strict-transform
history, not merely its final scheme. The ordered center ideals are preserved.
Source: ILO VIII 2.3.1, 2.3.11 (blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure Extension {A : Pair.{u}} {n : ℕ}
    (H : History A n) (K : History A (n + 1)) where
  ambient : ∀ j : Fin (n + 1), H.ambient.obj (op j) ≅ K.ambient.obj (op j.castSucc)
  intrinsic : ∀ j : Fin (n + 1), H.intrinsic.obj (op j) ≅ K.intrinsic.obj (op j.castSucc)
  inclusion : ∀ j, H.inclusion.app (op j) ≫ (ambient j).hom =
    (intrinsic j).hom ≫ K.inclusion.app (op j.castSucc)
  ambientNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.ambient.map (homOfLE h).op ≫ (ambient j).hom =
      (ambient k).hom ≫ K.ambient.map
        (homOfLE (Fin.castSucc_le_castSucc_iff.mpr h)).op
  intrinsicNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.intrinsic.map (homOfLE h).op ≫ (intrinsic j).hom =
      (intrinsic k).hom ≫ K.intrinsic.map
        (homOfLE (Fin.castSucc_le_castSucc_iff.mpr h)).op
  initialAmbient : (ambient 0).hom ≫ K.initialAmbient.hom = H.initialAmbient.hom
  initialIntrinsic : (intrinsic 0).hom ≫ K.initialIntrinsic.hom = H.initialIntrinsic.hom
  centers : ∀ j : Fin n, H.center j = (K.center j.castSucc).comap (ambient j.castSucc).hom

/-- The new center viewed in the old final strict transform. Source: ILO VIII 2.3.11
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def Extension.centerMap {A : Pair.{u}} {n : ℕ}
    {H : History A n} {K : History A (n + 1)}
    (E : Extension H K) : (K.center (Fin.last n)).subscheme ⟶ H.X :=
  K.centerToIntrinsic (Fin.last n) ≫ (E.intrinsic (Fin.last n)).inv

/-- A stagewise smooth ambient pullback, deleting empty centers. The monotone surjection
`index` collapses exactly those transitions with unit pulled-back ideal. Every uncollapsed
transition preserves its actual ideal. Cartesian squares are over the initial schemes;
thus no arbitrary comparison map replaces the canonical base-change map.
Source: ILO VIII 2.3.4, 2.3.13; BMT 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure SmoothPullback {A B : Pair.{u}} {m n : ℕ}
    (f : AmbientSmoothMap A B)
    (H : History A m) (K : History B n) where
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  ambient : ∀ j, H.ambient.obj (op (index j)) ⟶ K.ambient.obj (op j)
  intrinsic : ∀ j, H.intrinsic.obj (op (index j)) ⟶ K.intrinsic.obj (op j)
  inclusion : ∀ j, H.inclusion.app (op (index j)) ≫ ambient j =
    intrinsic j ≫ K.inclusion.app (op j)
  ambientNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.ambient.map (homOfLE (index.monotone h)).op ≫ ambient j =
      ambient k ≫ K.ambient.map (homOfLE h).op
  intrinsicNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.intrinsic.map (homOfLE (index.monotone h)).op ≫ intrinsic j =
      intrinsic k ≫ K.intrinsic.map (homOfLE h).op
  cartesianAmbient : ∀ j, IsPullback (ambient j)
    (H.ambient.map (homOfLE (Fin.zero_le (index j))).op ≫ H.initialAmbient.hom)
    (K.ambient.map (homOfLE (Fin.zero_le j)).op ≫ K.initialAmbient.hom) f.ambient
  cartesianIntrinsic : ∀ j, IsPullback (intrinsic j)
    (H.intrinsic.map (homOfLE (Fin.zero_le (index j))).op ≫ H.initialIntrinsic.hom)
    (K.intrinsic.map (homOfLE (Fin.zero_le j)).op ≫ K.initialIntrinsic.hom) f.intrinsic
  centers : ∀ j : Fin n,
    (index j.castSucc = index j.succ ∧ (K.center j).comap (ambient j.castSucc) = ⊤) ∨
      ∃ (k : Fin m) (h : index j.castSucc = k.castSucc),
        index j.succ = k.succ ∧ Nonempty (H.center k).subscheme ∧
          H.center k = (K.center j).comap
            (eqToHom (congrArg (fun t ↦ H.ambient.obj (op t)) h.symm) ≫ ambient j.castSucc)

/-- The final intrinsic map of a smooth history comparison, including deletion of all
stages. Source: ILO VIII 2.3.4, 2.3.13
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def SmoothPullback.finalMap {A B : Pair.{u}} {m n : ℕ}
    {f : AmbientSmoothMap A B}
    {H : History A m} {K : History B n}
    (c : SmoothPullback f H K) : H.X ⟶ K.X :=
  eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) c.last.symm) ≫ c.intrinsic (Fin.last n)

/-- Intrinsic history identification keeps every earlier center ideal and its order,
even when its intrinsic blowup was an identity. No isomorphism of the ambient schemes
is required. Pulling these ideals along the recorded diagram retains all exceptional data.
Source: ILO VIII 2.3.11--2.3.13; BMT 6.1 Addendum (3)
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure IntrinsicComparison {A B : Pair.{u}} {n : ℕ}
    (e : A.X ≅ B.X) (H : History A n)
    (K : History B n) where
  iso : H.intrinsic ≅ K.intrinsic
  initial : (iso.app (op 0)).hom ≫ K.initialIntrinsic.hom = H.initialIntrinsic.hom ≫ e.hom
  centers : ∀ j : Fin n, (H.centerToIntrinsic j).ker =
    (K.centerToIntrinsic j).ker.comap (iso.app (op j.castSucc)).hom

end History

/-- A simultaneous assignment on finite histories. Values outside the generated admissible
class impose no conditions. Source: BMT 6.1--6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def ValueFamily (V : Type w) : Type (max (u + 1) w) :=
  ∀ {A : Pair.{u}} {n : ℕ} (H : History A n), H.X → V

/-- The reduced full positive maximum stratum, as an actual next center.
Source: BMT 6.1--6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def MaximumStep {V : Type w} [LinearOrder V] [OrderBot V] (ν : ValueFamily.{u} V)
    {A : Pair.{u}} {n : ℕ} {H : History A n} {K : History A (n + 1)}
    (E : History.Extension H K) : Prop :=
  ∃ a : V, IsGreatest (Set.range (ν H)) a ∧ ⊥ < a ∧
    IsReduced (K.center (Fin.last n)).subscheme ∧
      Set.range E.centerMap = {x | ν H x = a}

/-- An intrinsic smooth comparison of full histories. Earlier intrinsic ideal centers,
including those with identity intrinsic blowup, are pulled back in their original order.
Exactly the empty centers are deleted. Ambient embeddings need not be identified.
Source: BMT Addendum 6.1 and 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure IntrinsicSmoothComparison {A B : Pair.{u}} {m n : ℕ} (f : A.X ⟶ B.X)
    (H : History A m) (K : History B n) where
  smooth : Smooth f
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  map : ∀ j, H.intrinsic.obj (op (index j)) ⟶ K.intrinsic.obj (op j)
  initial : map 0 ≫ K.initialIntrinsic.hom =
    eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) first) ≫ H.initialIntrinsic.hom ≫ f
  naturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.intrinsic.map (homOfLE (index.monotone h)).op ≫ map j =
      map k ≫ K.intrinsic.map (homOfLE h).op
  cartesian : ∀ j, IsPullback (map j)
    (H.intrinsic.map (homOfLE (Fin.zero_le (index j))).op ≫ H.initialIntrinsic.hom)
    (K.intrinsic.map (homOfLE (Fin.zero_le j)).op ≫ K.initialIntrinsic.hom) f
  centers : ∀ j : Fin n,
    (index j.castSucc = index j.succ ∧
      (K.centerToIntrinsic j).ker.comap (map j.castSucc) = ⊤) ∨
    ∃ (k : Fin m) (h : index j.castSucc = k.castSucc), index j.succ = k.succ ∧
      Nonempty (H.center k).subscheme ∧
        (H.centerToIntrinsic k).ker = (K.centerToIntrinsic j).ker.comap
          (eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) h.symm) ≫ map j.castSucc)

/-- The final intrinsic comparison map, including when all centers disappear.
Source: BMT 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def IntrinsicSmoothComparison.finalMap {A B : Pair.{u}} {m n : ℕ} {f : A.X ⟶ B.X}
    {H : History A m} {K : History B n} (c : IntrinsicSmoothComparison f H K) :
    H.X ⟶ K.X :=
  eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) c.last.symm) ≫ c.map (Fin.last n)

/-- Prefixes of the maximum construction and their open and smooth pullbacks.
Open immersions are smooth. An isomorphism of intrinsic histories is a smooth comparison.
Source: BMT 6.1--6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
inductive Admissible {V : Type w} [LinearOrder V] [OrderBot V] (ν : ValueFamily.{u} V) :
    ∀ {A : Pair.{u}} {n : ℕ}, History A n → Prop
  | empty {A : Pair.{u}} (H : History A 0) : Admissible ν H
  | step {A : Pair.{u}} {n : ℕ} {H : History A n} {K : History A (n + 1)}
      (E : History.Extension H K) : Admissible ν H → MaximumStep ν E → Admissible ν K
  | ambient {A B : Pair.{u}} {m n : ℕ} {H : History A m} {K : History B n}
      (f : AmbientSmoothMap A B) (c : History.SmoothPullback f H K) :
        Admissible ν K → Admissible ν H
  | intrinsic {A B : Pair.{u}} {m n : ℕ} {H : History A m} {K : History B n}
      (f : A.X ⟶ B.X) (c : IntrinsicSmoothComparison f H K) :
        Admissible ν K → Admissible ν H

/-- A reduced stratum ideal on an open where that individual stratum is closed.
The stratum need not be the maximum; an empty stratum is represented by the unit ideal.
Source: BMT 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def StratumIdeal {V : Type w} {Y : Scheme.{u}} (ν : Y → V) (a : V)
    (U : Y.Opens) (I : U.toScheme.IdealSheafData) : Prop :=
  IsReduced I.subscheme ∧ ∀ x : U.toScheme, x ∈ I.support ↔ ν (U.ι x) = a

/-- Equality of every reduced locally closed stratum ideal under a smooth map that
preserves the value function. Quantification over opens includes nonmaximum strata and
unit ideals for empty inverse-image strata. No arbitrary chosen ideal replaces the reduced
structure. Source: BMT 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def StrataPullback {V : Type w} {Y Z : Scheme.{u}} (ν : Y → V) (μ : Z → V)
    (f : Y ⟶ Z) : Prop :=
  ∀ (U : Z.Opens) (W : Y.Opens) (g : W.toScheme ⟶ U.toScheme),
    g ≫ U.ι = W.ι ≫ f → Smooth g →
      ∀ (a : V) (I : U.toScheme.IdealSheafData), StratumIdeal μ a U I →
        StratumIdeal ν a W (I.comap g) ∧
          ((∀ x : W.toScheme, ν (W.ι x) ≠ a) → I.comap g = ⊤)

/-- The ideal of an individual stratum, viewed in an open of the ambient scheme.
This is the reduced induced structure of the image of that stratum, not the ideal of its
closure in the whole ambient scheme. Source: BMT Addendum 6.1 and 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def AmbientStratumIdeal {V : Type w} {X P : Scheme.{u}} (i : X ⟶ P) (ν : X → V)
    (a : V) (U : P.Opens) (I : U.toScheme.IdealSheafData) : Prop :=
  IsReduced I.subscheme ∧
    ∀ p : U.toScheme, p ∈ I.support ↔ ∃ x : X, i x = U.ι p ∧ ν x = a

/-- Smooth pullback of all individual reduced stratum ideals in ambient opens.
Source: BMT Addendum 6.1 and 6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
def AmbientStrataPullback {V : Type w} {X Y P Q : Scheme.{u}} (i : X ⟶ P) (j : Y ⟶ Q)
    (ν : X → V) (μ : Y → V) (f : P ⟶ Q) : Prop :=
  ∀ (U : Q.Opens) (W : P.Opens) (g : W.toScheme ⟶ U.toScheme),
    g ≫ U.ι = W.ι ≫ f → Smooth g →
      ∀ (a : V) (I : U.toScheme.IdealSheafData), AmbientStratumIdeal j μ a U I →
        AmbientStratumIdeal i ν a W (I.comap g) ∧
          ((¬ ∃ (p : W.toScheme) (x : X), i x = W.ι p ∧ ν x = a) → I.comap g = ⊤)

/-- The local calculus on generically reduced schemes. This structure records conditions,
not a proof that a calculus exists. Synchronization values live in one arbitrary linear
order with bottom; no well-foundedness or bound on dimension is assumed. The bottom locus
is the regular locus, choosing the version which stops before optional divisor cleanup.
Source: BMT Theorem/Addendum 6.1, 6.1--6.3
(blueprint: def-per-generically-reduced-invariant-calculus-data). -/
structure Calculus (V : Type w) [LinearOrder V] [OrderBot V] where
  value : ValueFamily.{u} V
  finiteImage : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → (Set.range (value H)).Finite
  closedUpper : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → ∀ a : V, IsClosed {x | a ≤ value H x}
  regularPoint : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → ∀ x : H.X,
      value H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)
  stageGeometry : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → Smooth H.base ∧ IsSeparated H.base ∧
      LocallyOfFiniteType H.base ∧ QuasiCompact H.base ∧ GenericallyReduced H.X ∧
        LocallyOfFiniteType (H.inclusion.app (op (Fin.last n)) ≫ H.base) ∧
          QuasiCompact (H.inclusion.app (op (Fin.last n)) ≫ H.base)
  maximumExists : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → ∀ a : V, IsGreatest (Set.range (value H)) a → ⊥ < a →
      ∃ (K : History A (n + 1)) (E : History.Extension H K), MaximumStep value E
  maximumGeometry : ∀ {A : Pair.{u}} {n : ℕ} {H : History A n}
    {K : History A (n + 1)} (E : History.Extension H K),
    Admissible value H → MaximumStep value E →
      Nonempty (K.center (Fin.last n)).subscheme ∧
      IsRegularScheme (K.center (Fin.last n)).subscheme ∧
      interior (Set.range E.centerMap) = ∅ ∧
      RingedSpace.IsCoherent H.P.toRingedSpace
        (((K.center (Fin.last n)).comap (E.ambient (Fin.last n)).hom).toModules) ∧
      RingedSpace.IsCoherent H.X.toRingedSpace E.centerMap.ker.toModules ∧
      ∀ z : (K.center (Fin.last n)).subscheme,
        ¬ IsRegularLocalRing (A.X.presheaf.stalk
          ((H.intrinsic.map (homOfLE (Fin.zero_le (Fin.last n))).op ≫
            H.initialIntrinsic.hom) (E.centerMap z)))
  bottomRegular : ∀ {A : Pair.{u}} {n : ℕ} (H : History A n),
    Admissible value H → (∀ x : H.X, value H x = ⊥) → IsRegularScheme H.X
  regularInput : ∀ {A : Pair.{u}} (H : History A 0),
    IsRegularScheme A.X → ∀ x : H.X, value H x = ⊥
  ambientPullbackExists : ∀ {A B : Pair.{u}} {n : ℕ} (f : AmbientSmoothMap A B)
    (K : History B n), Admissible value K →
      ∃ (m : ℕ) (H : History A m), Nonempty (History.SmoothPullback f H K)
  intrinsicPullbackExists : ∀ {A B : Pair.{u}} {n : ℕ} (f : A.X ⟶ B.X),
    Smooth f → ∀ K : History B n, Admissible value K →
      ∃ (m : ℕ) (H : History A m), Nonempty (IntrinsicSmoothComparison f H K)
  ambientValues : ∀ {A B : Pair.{u}} {m n : ℕ} {f : AmbientSmoothMap A B}
    {H : History A m} {K : History B n} (c : History.SmoothPullback f H K),
    Admissible value K → ∀ x : H.X, value H x = value K (c.finalMap x)
  ambientIdeals : ∀ {A B : Pair.{u}} {m n : ℕ} {f : AmbientSmoothMap A B}
    {H : History A m} {K : History B n} (c : History.SmoothPullback f H K),
    Admissible value K → StrataPullback (value H) (value K) c.finalMap
  ambientStratumIdeals : ∀ {A B : Pair.{u}} {m n : ℕ} {f : AmbientSmoothMap A B}
    {H : History A m} {K : History B n} (c : History.SmoothPullback f H K),
    Admissible value K → AmbientStrataPullback
      (H.inclusion.app (op (Fin.last m))) (K.inclusion.app (op (Fin.last n)))
      (value H) (value K)
      (eqToHom (congrArg (fun t ↦ H.ambient.obj (op t)) c.last.symm) ≫
        c.ambient (Fin.last n))
  intrinsicValues : ∀ {A B : Pair.{u}} {m n : ℕ} {f : A.X ⟶ B.X}
    {H : History A m} {K : History B n} (c : IntrinsicSmoothComparison f H K),
    Admissible value K → ∀ x : H.X, value H x = value K (c.finalMap x)
  intrinsicIdeals : ∀ {A B : Pair.{u}} {m n : ℕ} {f : A.X ⟶ B.X}
    {H : History A m} {K : History B n} (c : IntrinsicSmoothComparison f H K),
    Admissible value K → StrataPullback (value H) (value K) c.finalMap
  embeddingValues : ∀ {A B : Pair.{u}} {n : ℕ} {e : A.X ≅ B.X}
    {H : History A n} {K : History B n} (c : History.IntrinsicComparison e H K),
    Admissible value H → Admissible value K → ∀ x : H.X,
      value H x = value K ((c.iso.app (op (Fin.last n))).hom x)
  embeddingIdeals : ∀ {A B : Pair.{u}} {n : ℕ} {e : A.X ≅ B.X}
    {H : History A n} {K : History B n} (c : History.IntrinsicComparison e H K),
    Admissible value H → Admissible value K →
      StrataPullback (value H) (value K) (c.iso.app (op (Fin.last n))).hom
  termination : ∀ A : Pair.{u},
    ¬ ∃ (H : ∀ n : ℕ, History A n) (E : ∀ n : ℕ, History.Extension (H n) (H (n + 1))),
      ∀ n : ℕ, MaximumStep value (E n)

end AlgebraicGeometry.GenericallyReducedResolution
