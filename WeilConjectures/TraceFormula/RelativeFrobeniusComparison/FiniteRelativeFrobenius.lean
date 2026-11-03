/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceWeilComplex.TraceWeilComplex
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.RelativeFrobenius
import WeilConjectures.AlgebraicGeometry.AbsoluteFrobeniusNatural
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.TopInvariance
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!
# Relative Frobenius comparison using the recorded Weil-complex interface

Source: current blueprint, sk-i-relative-frob, clauses (1)--(4)
(blueprint: sk-i-relative-frob). All coefficient iterates, global operators and
stalk endomorphisms are those of Sheaf.Paper.TraceWeilComplex. Compact-support
comparisons are those of the supplied geometric operation package of sk-d-six.

## Main declarations

* `theta`, `pushed`, `compactComposition`, `fibreComplex`, `fibreComparison`:
  the canonical comparison and the objects/operators in the four clauses.
* `FourClauses`, `ModelFourClauses`: the full comparison statement.
* `relativeFrobenius_comparison`: comparison for arbitrary finite primary coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures WeilConjectures.TraceWeilComplex
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Lift the existing sheaf adjunction equivalence to module objects.
The lifted unit and counit are invertible after the conservative forgetful functor;
extension of scalars along the canonical coefficient isomorphism is an equivalence. -/
private theorem modulePullback_isEquivalence
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (r : X ⟶ Y)
    [IsUniversalHomeomorphism r] : (r)^*⟦Λ⟧.IsEquivalence := by
  have := ProEtale.isEquivalence_lowerStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  have := ProEtale.isEquivalence_upperStar_of_isUniversalHomeomorphism Ab.{u + 1} r
  have : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).unit :=
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).unit_isIso_of_L_fully_faithful
  have : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).counit :=
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).counit_isIso_of_R_fully_faithful
  let adj := (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} r).mapModAdjunction
    (condensedRingObj Λ Y)
  have : IsIso adj.unit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.unit.app M)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_unit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : IsIso adj.counit := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
    have : IsIso ((Mod.forget _).map (adj.counit.app N)) := by
      rw [Mod.forget_map, Adjunction.mapModAdjunction_counit_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  have : ((r)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  unfold upperStar
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.RelativeFrobeniusComparison

/-- Geometric maps have compactifications by the existing Nagata theorem.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob). -/
instance compactificationOver {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) :
    HasCompactification f.left := HasCompactification.of_over f

/-- Powers of finite endomorphisms remain finite.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob). -/
instance finitePower {s : Scheme.{u}} {X : Over s} (Phi : X ⟶ X)
    [IsFinite Phi.left] (m : ℕ) : IsFinite (frobeniusPower Phi m).left := by
  induction m with
  | zero => exact inferInstanceAs (IsFinite (𝟙 X.left))
  | succ m hm =>
      have := hm
      change IsFinite ((frobeniusPower Phi m).left ≫ Phi.left)
      infer_instance

/-- Powers of universal homeomorphisms remain universal homeomorphisms.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob). -/
instance universalHomeomorphismPower {s : Scheme.{u}} {X : Over s} (Phi : X ⟶ X)
    [IsUniversalHomeomorphism Phi.left] (m : ℕ) :
    IsUniversalHomeomorphism (frobeniusPower Phi m).left := by
  induction m with
  | zero => exact inferInstanceAs (IsUniversalHomeomorphism (𝟙 X.left))
  | succ m hm =>
      have := hm
      change IsUniversalHomeomorphism ((frobeniusPower Phi m).left ≫ Phi.left)
      infer_instance

/-- The commuting equation extends to powers.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob).
Proof. At zero both sides equal f. At a successor, expand frobeniusPower,
associate, use hf, the induction hypothesis and associativity. -/
theorem powerCommutation {s : Scheme.{u}} {X Y : Over s} (f : X ⟶ Y)
    (PhiX : X ⟶ X) (PhiY : Y ⟶ Y) (hf : PhiX ≫ f = f ≫ PhiY) (m : ℕ) :
    frobeniusPower PhiX m ≫ f = f ≫ frobeniusPower PhiY m := by
  induction m with
  | zero => simp [frobeniusPower]
  | succ m hm =>
      simp only [frobeniusPower, Category.assoc, hf]
      rw [← Category.assoc, hm, Category.assoc]

/-- Power addition with the order used by the pullback compositor.
Source: sk-i-relative-frob (1), iteration (blueprint: sk-i-relative-frob).
Proof. Induct on b, using the defining recursion and associativity; the zero
case is the right identity. The powers are of the same endomorphism. -/
theorem powerAdd {s : Scheme.{u}} {X : Over s} (Phi : X ⟶ X) (a b : ℕ) :
    frobeniusPower Phi (a + b) = frobeniusPower Phi a ≫ frobeniusPower Phi b := by
  induction b with
  | zero => simp [frobeniusPower]
  | succ b hb =>
      change frobeniusPower Phi (a + b) ≫ Phi =
        frobeniusPower Phi a ≫ (frobeniusPower Phi b ≫ Phi)
      rw [hb, Category.assoc]

/-- The fibre projection is compactifiable by ordinary base change.
Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob). -/
instance fibreProjectionCompactification {s : Scheme.{u}} {X Y : Over s}
    (f : X ⟶ Y) [HasCompactification f.left] (y : TraceOperations.base s ⟶ Y) :
    HasCompactification (pullback.snd f y).left := by
  have h := (IsPullback.of_hasPullback f y).map (Over.forget _)
  simp only [Over.forget_map] at h
  exact HasCompactification.of_isPullback h

/-- The fibre structure map is its second projection.
Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob).
Proof. Both are maps to the terminal object of Over s, so they agree by the
uniqueness part of the terminal universal property. -/
theorem fibreStructure {s : Scheme.{u}} {X Y : Over s} (f : X ⟶ Y)
    (y : TraceOperations.base s ⟶ Y) :
    pullback.snd f y = TraceOperations.structureMap (pullback f y) := by
  apply Over.OverMorphism.ext
  simpa [TraceOperations.base, TraceOperations.structureMap] using (pullback.snd f y).w

/-- The structure map of a fibre is compactifiable.
Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob). -/
instance fibreStructureCompactification {s : Scheme.{u}} {X Y : Over s}
    (f : X ⟶ Y) [HasCompactification f.left] (y : TraceOperations.base s ⟶ Y) :
    HasCompactification (pullback f y).hom := by
  have h := fibreStructure f y
  have : HasCompactification (TraceOperations.structureMap (pullback f y)).left :=
    HasCompactification.of_eq (congrArg Over.Hom.left h)
  exact inferInstanceAs (HasCompactification
    (TraceOperations.structureMap (pullback f y)).left)

/-- Finite-type geometry survives the specified geometric base change.
Source: sk-i-relative-frob, opening (blueprint: sk-i-relative-frob). -/
instance geometricFiberFiniteType (D : FiniteFieldDatum.{u})
    (X0 : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom] :
    LocallyOfFiniteType (D.geometricFiber X0).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd X0.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness survives geometric base change.
Source: sk-i-relative-frob, opening (blueprint: sk-i-relative-frob). -/
instance geometricFiberQuasiCompact (D : FiniteFieldDatum.{u})
    (X0 : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom] :
    QuasiCompact (D.geometricFiber X0).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd X0.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Separation survives geometric base change.
Source: sk-i-relative-frob, opening (blueprint: sk-i-relative-frob). -/
instance geometricFiberSeparated (D : FiniteFieldDatum.{u})
    (X0 : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom]
    [IsSeparated X0.hom] : IsSeparated (D.geometricFiber X0).hom :=
  inferInstanceAs (IsSeparated (pullback.snd X0.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Naturality of the recorded model Frobenius.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob).
Proof. The q-power absolute scheme Frobenius is natural in f0. Apply the
base-change functor Over.pullback to that equality; its functoriality gives
the stated equality of geometric base-change morphisms. -/
theorem modelCommutation (D : FiniteFieldDatum.{u})
    {X0 Y0 : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom]
    [LocallyOfFiniteType Y0.hom] [QuasiCompact Y0.hom] (f0 : X0 ⟶ Y0) :
    modelFrobenius D X0 ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f0 =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f0 ≫
        modelFrobenius D Y0 := by
  unfold modelFrobenius
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply Over.OverMorphism.ext
  exact (Scheme.comp_iterateFrobenius D.prime f0.left
    (D.model_characteristic Y0.hom) (D.model_characteristic X0.hom) D.a).symm

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k]
  (O : TraceOperations.Given Λ (Spec (.of k))) (P : TraceOperations.GeometricOperations O)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (PhiX : X ⟶ X) (PhiY : Y ⟶ Y)
  [IsFinite PhiX.left] [IsUniversalHomeomorphism PhiX.left]
  [IsFinite PhiY.left] [IsUniversalHomeomorphism PhiY.left]
  (hf : PhiX ≫ f = f ≫ PhiY)

/-- Equality transport for the supplied shriek functor, including its
compactifiability proof. Source: sk-i-relative-frob (1), (3), (4)
(blueprint: sk-i-relative-frob). -/
def shriekCongr {s : Scheme.{u}} (O' : TraceOperations.Given Λ s)
    {U V : Over s} {a b : U ⟶ V}
    [HasCompactification a.left] [HasCompactification b.left] (h : a = b) :
    O'.shriek a ≅ O'.shriek b := by
  subst b
  exact Iso.refl _

/-- Discharges membership of a finite-Tor constructible complex, or of its derived
pullback, in the given operation domain of the package, from `Given.ctf_mem` and
`Given.star_mem` (sk-d-six, opening: the package "uses the given operations wherever the
displayed composites are defined, and imposes the two final invertibility requirements on
the specified finite-Tor constructible inputs"). -/
macro "pkg_dom" : tactic => `(tactic| first
  | assumption
  | exact AlgebraicGeometry.ProEtale.TraceOperations.Given.ctf_mem _ _ _
  | exact AlgebraicGeometry.ProEtale.TraceOperations.Given.star_mem _ _
      (AlgebraicGeometry.ProEtale.TraceOperations.Given.ctf_mem _ _ _))

/-- The specified comparison: package base change, ordinary unit for relative
Frobenius, inverse package proper comparison, package composition and canonical
pullback composition. The comparisons are evaluated at `K`, `p_m^*K`, `r_m^*p_m^*K` and
`Rr_{m!}r_m^*p_m^*K`, which lie in the given operation domains since `K` does (`hK`, supplied
automatically for finite-Tor constructible inputs) by `Given.star_mem`, `Given.shriek_mem`.
Source: sk-i-relative-frob (1) (blueprint: sk-i-relative-frob); sk-d-six, opening. -/
def theta (m : ℕ) (K : TraceOperations.D Λ X.left)
    (hK : O.dom X K := by pkg_dom) :
    (TraceOperations.star Λ (frobeniusPower PhiY m).left).obj ((O.shriek f).obj K) ⟶
      (O.shriek f).obj ((TraceOperations.star Λ (frobeniusPower PhiX m).left).obj K) := by
  let g := frobeniusPower PhiY m
  let p := pullback.snd g f
  let f' := pullback.fst g f
  let r := relativeFrobenius f (frobeniusPower PhiX m) g
    (powerCommutation f PhiX PhiY hf m)
  haveI : HasCompactification (r ≫ f').left := by
    dsimp [r, f', g]
    rw [relativeFrobenius_left_fst_left]
    infer_instance
  let sq := (isPullback_left_pullback f g).flip
  let chosen : ChosenCartesianSquare p.left f'.left f.left g.left :=
    { w := sq.w
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hp : O.dom _ ((TraceOperations.star Λ p.left).obj K) := O.star_mem p hK
  have hr : O.dom _ ((TraceOperations.star Λ r.left).obj
      ((TraceOperations.star Λ p.left).obj K)) := O.star_mem r hp
  exact (P.comparisons.baseChange p f' f g chosen).hom.app ⟨K, hK, hp⟩ ≫
    (O.shriek f').map
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.left).unit.app
          ((TraceOperations.star Λ p.left).obj K) ≫
        (P.comparisons.proper r).inv.app
          ⟨(TraceOperations.star Λ r.left).obj ((TraceOperations.star Λ p.left).obj K), hr⟩) ≫
    (P.comparisons.composition r f').hom.app ⟨_, hr, O.shriek_mem r hr⟩ ≫
    (shriekCongr O (relativeFrobenius_fst f (frobeniusPower PhiX m) g
      (powerCommutation f PhiX PhiY hf m))).hom.app _ ≫
    (O.shriek f).map
      ((pullbackComposition Λ r p).inv.app K ≫
        (starCongr (Λ := Λ) (relativeFrobenius_snd f (frobeniusPower PhiX m) g
          (powerCommutation f PhiX PhiY hf m))).hom.app K)

omit [LocallyOfFiniteType Y.hom] in
/-- The specified comparison is invertible at every complex `K` of the given operation domain
(`hK`, supplied automatically for finite-Tor constructible inputs, sk-i-relative-frob (1) being
on `D^b_ctf`; sk-d-six, opening).
Source: sk-i-relative-frob (1), topological invariance (blueprint: sk-i-relative-frob).
Proof. The relative Frobenius is a universal homeomorphism. Its module pullback
is an equivalence, hence so is its derived pullback. The specified adjunction unit
is therefore invertible. Every other factor of theta is an isomorphism, and the
compact-support functors preserve these isomorphisms. -/
theorem theta_isIso (m : ℕ) (K : TraceOperations.D Λ X.left)
    (hK : O.dom X K := by pkg_dom) :
    IsIso (theta O P f PhiX PhiY hf m K hK) := by
  let g := frobeniusPower PhiY m
  let p := pullback.snd g f
  let r := relativeFrobenius f (frobeniusPower PhiX m) g
    (powerCommutation f PhiX PhiY hf m)
  have : (CondensedRing.upperStar Λ r.left).IsEquivalence :=
    CondensedRing.modulePullback_isEquivalence Λ r.left
  have : (TraceOperations.star Λ r.left).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ r.left).symm
  have : IsIso (CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.left).unit :=
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.left).unit_isIso_of_L_fully_faithful
  dsimp [theta]
  infer_instance

omit [LocallyOfFiniteType Y.hom]
  [IsUniversalHomeomorphism PhiX.left] [IsUniversalHomeomorphism PhiY.left] in
/-- Naturality of the specified relative Frobenius comparison, for morphisms between
complexes of the given operation domain (`hK`, `hN`, supplied automatically for finite-Tor
constructible inputs; sk-d-six, opening).
Source: sk-i-relative-frob (1), naturality (blueprint: sk-i-relative-frob).
Proof. Express theta as the composite of the package exchange, the ordinary
adjunction unit, inverse proper comparison, compact-support composition,
equality transport and pullback composition. Whiskering preserves natural
transformations on the full subcategory of the given operation domain, so naturality of
that composite is exactly this equation. -/
theorem theta_naturality (m : ℕ) (K N : TraceOperations.D Λ X.left) (v : K ⟶ N)
    (hK : O.dom X K := by pkg_dom) (hN : O.dom X N := by pkg_dom) :
    (TraceOperations.star Λ (frobeniusPower PhiY m).left).map ((O.shriek f).map v) ≫
        theta O P f PhiX PhiY hf m N hN =
      theta O P f PhiX PhiY hf m K hK ≫
        (O.shriek f).map ((TraceOperations.star Λ (frobeniusPower PhiX m).left).map v) := by
  let g := frobeniusPower PhiY m
  let p := pullback.snd g f
  let f' := pullback.fst g f
  let r := relativeFrobenius f (frobeniusPower PhiX m) g
    (powerCommutation f PhiX PhiY hf m)
  have : HasCompactification (r ≫ f').left := by
    dsimp [r, f', g]
    rw [relativeFrobenius_left_fst_left]
    infer_instance
  let sq := (isPullback_left_pullback f g).flip
  let chosen : ChosenCartesianSquare p.left f'.left f.left g.left :=
    { w := sq.w
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  -- The comparisons are natural transformations on the given operation domains; the
  -- inputs `K`, `p^*K`, `r^*p^*K` stay in them by `Given.star_mem`, `Given.shriek_mem`.
  let ι := (O.dom X).ι
  let Lp := (O.pullDom p).lift ι (fun K => ⟨K.2, O.star_mem p K.2⟩)
  let Lr := (O.dom _).lift (ι ⋙ TraceOperations.star Λ p.left ⋙ TraceOperations.star Λ r.left)
    (fun K => O.star_mem r (O.star_mem p K.2))
  let Lc := (O.compDom r).lift
    (ι ⋙ TraceOperations.star Λ p.left ⋙ TraceOperations.star Λ r.left)
    (fun K => ⟨O.star_mem r (O.star_mem p K.2), O.shriek_mem r (O.star_mem r (O.star_mem p K.2))⟩)
  let η := Functor.whiskerLeft (ι ⋙ TraceOperations.star Λ p.left)
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.left).unit ≫
    Functor.whiskerLeft Lr (P.comparisons.proper r).inv
  let t := Functor.whiskerLeft Lp (P.comparisons.baseChange p f' f g chosen).hom ≫
    Functor.whiskerRight η (O.shriek f') ≫
    Functor.whiskerLeft Lc
      ((P.comparisons.composition r f').hom ≫
        Functor.whiskerLeft (O.compDom r).ι
          (shriekCongr O (relativeFrobenius_fst f (frobeniusPower PhiX m) g
            (powerCommutation f PhiX PhiY hf m))).hom) ≫
    Functor.whiskerLeft ι (Functor.whiskerRight
      ((pullbackComposition Λ r p).inv ≫
        (starCongr (Λ := Λ) (relativeFrobenius_snd f (frobeniusPower PhiX m) g
          (powerCommutation f PhiX PhiY hf m))).hom) (O.shriek f))
  simpa only [t, η, theta, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc, ι, Lp, Lr, Lc,
    ObjectProperty.lift, ObjectProperty.lift_obj_obj, ObjectProperty.ι_map,
    ObjectProperty.ι_obj, ObjectProperty.homMk_hom]
    using t.naturality (X := (⟨K, hK⟩ : (O.dom X).FullSubcategory)) (Y := ⟨N, hN⟩)
      (ObjectProperty.homMk v)

/-- The pushforward Weil complex uses the recorded WeilComplex structure and its
coefficient is theta in degree one followed by Rf_! psi, with the canonical
power-one identification; `K` lies in the given operation domain (`hK`, supplied
automatically for finite-Tor constructible inputs). Source: sk-i-relative-frob (2)
(blueprint: sk-i-relative-frob). -/
def pushed (K : TraceOperations.D Λ X.left)
    (psi : (TraceOperations.star Λ PhiX.left).obj K ⟶ K)
    (hK : O.dom X K := by pkg_dom) : WeilComplex Λ Y where
  frobenius := PhiY
  complex := (O.shriek f).obj K
  coefficient :=
    (starCongr (Λ := Λ) (by simp [frobeniusPower] : PhiY = frobeniusPower PhiY 1)).hom.app
        ((O.shriek f).obj K) ≫
      theta O P f PhiX PhiY hf 1 K ≫
      (O.shriek f).map
        ((starCongr (Λ := Λ)
          (by simp [frobeniusPower] : frobeniusPower PhiX 1 = PhiX)).hom.app K ≫ psi)

/-- Properness needed by the recorded global operator on the pushed complex.
Source: sk-i-relative-frob (3) (blueprint: sk-i-relative-frob). -/
instance pushedPowerProper (K : TraceOperations.D Λ X.left)
    (psi : (TraceOperations.star Λ PhiX.left).obj K ⟶ K) (hK : O.dom X K) (m : ℕ) :
    IsProper (frobeniusPower (pushed O P f PhiX PhiY hf K psi hK).frobenius m).left := by
  change IsProper (frobeniusPower PhiY m).left
  infer_instance

/-- Canonical structure-map composition from P.comparisons, evaluated at `K` in the given
operation domain (`hK`, supplied automatically for finite-Tor constructible inputs), so that
`Rf_!K` is in it as well (`Given.shriek_mem`).
Source: sk-i-relative-frob (3) (blueprint: sk-i-relative-frob); sk-d-six, opening. -/
def compactComposition (K : TraceOperations.D Λ X.left)
    (hK : O.dom X K := by pkg_dom) :
    (TraceOperations.Comparisons.compactlySupported O Y).obj ((O.shriek f).obj K) ≅
      (TraceOperations.Comparisons.compactlySupported O X).obj K := by
  have e : f ≫ TraceOperations.structureMap Y = TraceOperations.structureMap X :=
    Over.OverMorphism.ext f.w
  haveI : HasCompactification (f ≫ TraceOperations.structureMap Y).left :=
    HasCompactification.of_eq (f := X.hom) (congrArg Over.Hom.left e).symm
  exact (P.comparisons.composition f (TraceOperations.structureMap Y)).app
      ⟨K, hK, O.shriek_mem f hK⟩ ≪≫
    (shriekCongr O e).app K

/-- The canonical restriction of PhiX^m to a PhiY^m-fixed fibre.
Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob). -/
def fibreFrobenius (m : ℕ) (y : TraceOperations.base (Spec (.of k)) ⟶ Y)
    (hy : y ≫ frobeniusPower PhiY m = y) : pullback f y ⟶ pullback f y :=
  pullback.lift (pullback.fst f y ≫ frobeniusPower PhiX m) (pullback.snd f y) (by
    rw [Category.assoc, powerCommutation f PhiX PhiY hf, ← Category.assoc,
      pullback.condition, Category.assoc, hy])

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [IsUniversalHomeomorphism PhiX.left] [IsFinite PhiY.left]
  [IsUniversalHomeomorphism PhiY.left] in
/-- The restricted Frobenius on a fixed fibre is finite.
Source: sk-i-relative-frob (4), finite fibre Frobenius
(blueprint: sk-i-relative-frob).
Proof. A rational point of a scheme over a field is a closed immersion. Its
base change is the fibre inclusion i. The defining pullback identity gives
Phi_fibre followed by i equal to i followed by PhiX^m, a composite of finite
maps. Cancellation of finiteness against i proves the assertion. -/
instance fibreFrobeniusFinite (m : ℕ) (y : TraceOperations.base (Spec (.of k)) ⟶ Y)
    (hy : y ≫ frobeniusPower PhiY m = y) :
    IsFinite (fibreFrobenius f PhiX PhiY hf m y hy).left := by
  have : IsClosedImmersion y.left :=
    isClosedImmersion_of_comp_eq_id Y.hom y.left y.w
  have hyfinite : IsFinite y.left := inferInstance
  have sq := ((IsPullback.of_hasPullback f y).map (Over.forget _)).flip
  simp only [Over.forget_map] at sq
  have : IsFinite (pullback.fst f y).left :=
    MorphismProperty.of_isPullback sq hyfinite
  have : IsFinite ((fibreFrobenius f PhiX PhiY hf m y hy).left ≫
      (pullback.fst f y).left) := by
    rw [← Over.comp_left]
    simp only [fibreFrobenius, pullback.lift_fst, Over.comp_left]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst f y).left

/-- The fibre carries a WeilComplex in the recorded interface, with the restricted
m-th coefficient. Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob). -/
def fibreComplex (K : TraceOperations.D Λ X.left)
    (psi : (TraceOperations.star Λ PhiX.left).obj K ⟶ K) (m : ℕ)
    (y : TraceOperations.base (Spec (.of k)) ⟶ Y)
    (hy : y ≫ frobeniusPower PhiY m = y) : WeilComplex Λ (pullback f y) where
  frobenius := fibreFrobenius f PhiX PhiY hf m y hy
  complex := (TraceOperations.star Λ (pullback.fst f y).left).obj K
  coefficient :=
    (pullbackComposition Λ (fibreFrobenius f PhiX PhiY hf m y hy)
      (pullback.fst f y)).inv.app K ≫
    (starCongr (Λ := Λ) (pullback.lift_fst _ _ _)).hom.app K ≫
    (pullbackComposition Λ (pullback.fst f y) (frobeniusPower PhiX m)).hom.app K ≫
    (TraceOperations.star Λ (pullback.fst f y).left).map
      ((WeilComplex.mk PhiX K psi).iterate m)

/-- Compact-support base change at a fixed point, using the package exchange, evaluated at
`K` in the given operation domain (`hK`, supplied automatically for finite-Tor constructible
inputs), so that its pullback to the fibre is in it as well (`Given.star_mem`).
Source: sk-i-relative-frob (4) (blueprint: sk-i-relative-frob); sk-d-six, opening. -/
def fibreComparison (y : TraceOperations.base (Spec (.of k)) ⟶ Y)
    (K : TraceOperations.D Λ X.left) (hK : O.dom X K := by pkg_dom) :
    (TraceOperations.star Λ y.left).obj ((O.shriek f).obj K) ≅
      (TraceOperations.Comparisons.compactlySupported O (pullback f y)).obj
        ((TraceOperations.star Λ (pullback.fst f y).left).obj K) := by
  let sq := (IsPullback.of_hasPullback f y).map (Over.forget _)
  exact (P.comparisons.baseChange (pullback.fst f y) (pullback.snd f y) f y
    { w := sq.w
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }).app ⟨K, hK, O.star_mem _ hK⟩ ≪≫
    (shriekCongr O (fibreStructure f y)).app _

/-- The four clauses, expressed using the recorded coefficient recursion and
operators, together with the geometric fibre model in clause (4).
Source: sk-i-relative-frob (1)--(4) (blueprint: sk-i-relative-frob). -/
def FourClauses (q : ℕ) : Prop :=
  (∀ m : ℕ, 1 ≤ m →
    IsFinite (relativeFrobenius f (frobeniusPower PhiX m) (frobeniusPower PhiY m)
      (powerCommutation f PhiX PhiY hf m)).left ∧
    IsUniversalHomeomorphism
      (relativeFrobenius f (frobeniusPower PhiX m) (frobeniusPower PhiY m)
        (powerCommutation f PhiX PhiY hf m)).left ∧
    relativeFrobenius f (frobeniusPower PhiX m) (frobeniusPower PhiY m)
        (powerCommutation f PhiX PhiY hf m) ≫ pullback.snd (frobeniusPower PhiY m) f =
      frobeniusPower PhiX m ∧
    relativeFrobenius f (frobeniusPower PhiX m) (frobeniusPower PhiY m)
        (powerCommutation f PhiX PhiY hf m) ≫ pullback.fst (frobeniusPower PhiY m) f = f) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ (K : ConstantModelConstructibleFiniteTor Λ X.left),
    IsIso (theta O P f PhiX PhiY hf m K.obj) ∧
    ∀ (N : ConstantModelConstructibleFiniteTor Λ X.left) (v : K.obj ⟶ N.obj),
      (TraceOperations.star Λ (frobeniusPower PhiY m).left).map ((O.shriek f).map v) ≫
          theta O P f PhiX PhiY hf m N.obj =
        theta O P f PhiX PhiY hf m K.obj ≫
          (O.shriek f).map ((TraceOperations.star Λ (frobeniusPower PhiX m).left).map v)) ∧
  (∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → ∀ (K : ConstantModelConstructibleFiniteTor Λ X.left),
    theta O P f PhiX PhiY hf (a + b) K.obj =
      (starCongr (Λ := Λ) (powerAdd PhiY a b)).hom.app ((O.shriek f).obj K.obj) ≫
      (pullbackComposition Λ (frobeniusPower PhiY a) (frobeniusPower PhiY b)).hom.app
        ((O.shriek f).obj K.obj) ≫
      (TraceOperations.star Λ (frobeniusPower PhiY a).left).map
        (theta O P f PhiX PhiY hf b K.obj) ≫
      theta O P f PhiX PhiY hf a
        ((TraceOperations.star Λ (frobeniusPower PhiX b).left).obj K.obj) ≫
      (O.shriek f).map
        ((pullbackComposition Λ (frobeniusPower PhiX a) (frobeniusPower PhiX b)).inv.app
          K.obj ≫ (starCongr (Λ := Λ) (powerAdd PhiX a b)).inv.app K.obj)) ∧
  (∀ (K : ConstantModelConstructibleFiniteTor Λ X.left)
    (psi : (TraceOperations.star Λ PhiX.left).obj K.obj ⟶ K.obj),
    (∃ L : ConstantModelConstructibleFiniteTor Λ Y.left,
      L.obj = (pushed O P f PhiX PhiY hf K.obj psi).complex) ∧
    ∀ (m : ℕ), 1 ≤ m →
      (pushed O P f PhiX PhiY hf K.obj psi).iterate m =
        theta O P f PhiX PhiY hf m K.obj ≫
          (O.shriek f).map ((WeilComplex.mk PhiX K.obj psi).iterate m) ∧
      (pushed O P f PhiX PhiY hf K.obj psi).globalOperator O P m ≫
          (compactComposition O P f K.obj).hom =
        (compactComposition O P f K.obj).hom ≫
          (WeilComplex.mk PhiX K.obj psi).globalOperator O P m ∧
      ∀ (y : TraceOperations.base (Spec (.of k)) ⟶ Y)
        (hy : y ≫ frobeniusPower PhiY m = y),
      (∃ hProper : IsProper
          (frobeniusPower (fibreFrobenius f PhiX PhiY hf m y hy) 1).left,
        ((pushed O P f PhiX PhiY hf K.obj psi).stalkEndomorphism m y hy ≫
              (fibreComparison O P f y K.obj).hom =
            (fibreComparison O P f y K.obj).hom ≫
              @WeilComplex.globalOperator Λ _ _ (Spec (.of k)) O P (pullback f y)
                inferInstance (fibreComplex f PhiX PhiY hf K.obj psi m y hy) 1 hProper)) ∧
      ∃ (k' : Type u) (_ : Field k') (_ : Finite k') (_ : Algebra k' k)
        (Z0 : Scheme.{u}) (aZ0 : Z0 ⟶ Spec (.of k')) (pZ : (pullback f y).left ⟶ Z0),
        Nat.card k' = q ^ m ∧ LocallyOfFiniteType aZ0 ∧
        IsPullback pZ (pullback f y).hom aZ0
          (Spec.map (CommRingCat.ofHom (algebraMap k' k))) ∧
        ∃ FZ : Z0 ⟶ Z0, FZ.IsFrobenius (q ^ m) ∧
          (fibreFrobenius f PhiX PhiY hf m y hy).left ≫ pZ = pZ ≫ FZ)

/-- Specialization of the four clauses to the recorded model Frobenii. Their
finiteness and universal-homeomorphism properties are supplied by the recorded
sk-d-weil theorem, not imposed as hypotheses on the comparison.
Source: sk-i-relative-frob (blueprint: sk-i-relative-frob). -/
def ModelFourClauses (D : FiniteFieldDatum.{u})
    (O' : TraceOperations.Given Λ (Spec (.of D.k)))
    (P' : TraceOperations.GeometricOperations O')
    {X0 Y0 : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom] [IsSeparated X0.hom]
    [LocallyOfFiniteType Y0.hom] [QuasiCompact Y0.hom] [IsSeparated Y0.hom]
    (f0 : X0 ⟶ Y0) : Prop := by
  haveI := (modelFrobenius_finite_universalHomeomorphism D X0).1
  haveI := (modelFrobenius_finite_universalHomeomorphism D X0).2
  haveI := (modelFrobenius_finite_universalHomeomorphism D Y0).1
  haveI := (modelFrobenius_finite_universalHomeomorphism D Y0).2
  exact FourClauses O' P' (X := D.geometricFiber X0) (Y := D.geometricFiber Y0)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f0)
    (modelFrobenius D X0) (modelFrobenius D Y0) (modelCommutation D f0) D.q

-- STATEMENT-DISPUTED: the arbitrary package only requires vertical exchange pasting.
-- The iteration clause also needs normalization for identity base changes and
-- compatibility with ordinary units; see report.md for the sign-twist test.

/-- **Relative Frobenius comparison**, all four clauses for arbitrary finite
commutative ell-primary coefficients and arbitrary coefficient morphisms.
Source: sk-i-relative-frob, statement and proof (blueprint: sk-i-relative-frob).

Proof. The relative q^m-power Frobenius is integral, radicial and surjective;
finite type makes it finite, and these properties survive geometric base
change. The two projection identities are the identities of its pullback
lift. The first theta arrow is the package compact-support base change.
Topological invariance for finite-Tor classical objects makes the ordinary
adjunction unit of r_m invertible. Proper comparison and shriek composition,
followed by canonical pullback composition, give exactly the displayed theta.
Naturality of these arrows proves naturality of theta. Pasting the cartesian
squares for two powers and composing their ordinary units gives theta's
iteration identity, with the recorded pullback compositor. Induction on the
recorded WeilComplex.iterate recursion proves the coefficient identity;
compact-support constructibility supplies ctf membership of Rf_!K. For the
global identity, paste the structure-map comparison with theta: compact
pullback along PhiY^m becomes that along p_m, then along r_m, hence that along
PhiX^m. Postcompose with compact cohomology of the coefficient. At a fixed
point, base change takes r_m and its ordinary unit to the fibre Frobenius
and its unit; the same pasting calculation identifies the recorded stalk
endomorphism with the recorded degree-one fibre global operator. Finally the
fixed point descends to the field of q^m elements, and its fibre model has
q^m-power Frobenius equal after base change to the restriction of PhiX^m.
No invertibility of the input coefficient and no quotient-ring presentation
of the finite ring are used. -/
theorem relativeFrobenius_comparison (D : FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0)
    {X0 Y0 : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X0.hom] [QuasiCompact X0.hom] [IsSeparated X0.hom]
    [LocallyOfFiniteType Y0.hom] [QuasiCompact Y0.hom] [IsSeparated Y0.hom]
    (f0 : X0 ⟶ Y0) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    let Λ := Profinite.continuousMapRingObjOfUniverse.{u, u} A
    letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
    letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A
    ∀ (O' : TraceOperations.Given Λ (Spec (.of D.k)))
      (P' : TraceOperations.finiteGeometricOperationPackage ell A hA (Spec (.of D.k)) O'),
      ModelFourClauses D O' P' f0 := by
  sorry

end WeilConjectures.RelativeFrobeniusComparison
