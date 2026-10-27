/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.Paper.ModuleObjects
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.LatticeSubquotientFiltration
import all Sheaf.SixFunctors.IntegralModelsGenerators
import all Sheaf.Paper.ContinuousConstructibleIntegralTransport
import all Sheaf.Paper.CoefficientHeartLisseRestriction
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Reduction of a proper direct-image bound to integral lattices on strata

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-heart-bound/
sk-lem-proper-heart-bound-reduction.md and its proof
(blueprint: det-proper-heart-bound-reduction).

The auxiliary predicates only spell out this node's hypotheses and conclusion. All modules,
locally closed extensions, scalar extensions and higher direct images use existing definitions.
The bound is tested in nonnegative degrees; negative right derived functors are zero by the
node's convention, so this includes every integer c, including negative c.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Preserve shared coefficient constructions when elaborating filtration proofs.
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [-instance] WeilConjectures.SixFunctors.integralModel_coefficientMonObj

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

/-- The assertion `R^q p_* M = 0` for every integer q > c. Nonnegative q use Mathlib's
right derived functors; the negative ones are zero by convention and impose no condition.
In particular, c < 0 still tests degree zero.
Source: blueprint sk-lem-proper-heart-bound-reduction, definition of R^q p_*
(blueprint: det-proper-heart-bound-reduction). -/
def ProperHeartHigherVanishing
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ)
    (M : pulledBackModuleObjects Λ X) : Prop :=
  ∀ q : ℕ, c < (q : ℤ) → IsZero (((CondensedRing.lowerStar Λ p).rightDerived q).obj M)

/-- Ordinary localization of an integral coefficient module, along the actual pulled-back
inclusion O_F → F of condensed coefficient rings. This is F_X ⊗_{O_F,X} M.
Source: blueprint sk-lem-proper-heart-bound-reduction, notation N[1/ell]
(blueprint: det-proper-heart-bound-reduction). -/
def properHeartRationalization (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) :=
  Mod.extendScalars (coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ F)) X)

/-- This node's reduction assertion, before supplying the standing geometric hypotheses.
Its premise tests all locally closed immersions, every finite F containing E (also F = E),
and every pro-etale locally finite free integral lattice, in all three coefficient categories.
Its conclusion tests every constructible module over E or the finite-subextension-valued
condensed algebraic closure. Source: blueprint sk-lem-proper-heart-bound-reduction, all clauses
(blueprint: det-proper-heart-bound-reduction). -/
def ProperHeartBoundReductionAssertions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (X Y : Scheme.{u}) [IsNoetherian X]
    (p : X ⟶ Y) (c : ℤ) : Prop :=
  (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F →
    ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L₀ : pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ F) S),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F) L₀ →
      ProperHeartHigherVanishing (Profinite.padicIntegersRingObj ℓ F) p c
        ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
          a ha).obj L₀) ∧
      ProperHeartHigherVanishing (Profinite.continuousMapRingObj F) p c
        ((properHeartRationalization ℓ F X).obj
          ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
            a ha).obj L₀)) ∧
      ProperHeartHigherVanishing (Profinite.padicAlgClRingObj ℓ) p c
        ((Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X)).obj
          ((properHeartRationalization ℓ F X).obj
            ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
              a ha).obj L₀)))) →
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)],
    (Λ = Profinite.padicSubfieldCondensedRing ℓ E ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) →
    ∀ M : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ProperHeartHigherVanishing (coefficientHeartRingObj Λ) p c M.obj

open WeilConjectures.SixFunctors

private abbrev heart_modules
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The stratum condition, kept named so coefficient changes do not expand extension by zero. -/
@[irreducible] private def heart_lisse_extensions
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty (heart_modules A X)) : Prop :=
  ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
    (L : heart_modules A S), IsLisseCoefficientModule A L →
      P ((coefficientHeartLocallyClosedExtension A a ha).obj L)

private theorem heart_filtration_mem
    {A : Type*} [Category A] [Abelian A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderExtensions]
    (M : A) (m : ℕ) (T : Fin (m + 1) → Subobject M)
    (hbot : T 0 = ⊥) (htop : T (Fin.last m) = ⊤)
    (h : ∀ a : Fin m, T a.castSucc ≤ T a.succ)
    (hquot : ∀ a : Fin m, P (cokernel (Subobject.ofLE _ _ (h a)))) : P M := by
  have step (a : Fin m) (ha : P (T a.castSucc : A)) : P (T a.succ : A) := by
    let f := Subobject.ofLE _ _ (h a)
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    exact P.prop_X₂_of_shortExact hS ha (hquot a)
  have hall : ∀ a : Fin (m + 1), P (T a : A) := by
    apply Fin.induction
    · rw [hbot]
      exact P.prop_of_isZero ((isZero_zero A).of_iso Subobject.botCoeIsoZero)
    · intro a ha
      exact step a ha
  have hz := hall (Fin.last m)
  rw [htop] at hz
  exact P.prop_of_iso (asIso (⊤ : Subobject M).arrow) hz

private theorem heart_lisse_of_filtration
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty (heart_modules B X))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    (hP : ∀ (T : Scheme.{u}) (b : T ⟶ X) (hb : IsImmersion b)
      (M : heart_modules A T),
      CondensedRing.LocallyFree (condensedRingObj A T) M →
      P ((Mod.extendScalars (coefficientMap c X)).obj
        ((coefficientHeartLocallyClosedExtension A b hb).obj M)))
    {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
    (hfil : LatticeSubquotientFiltrationData A B c a)
    (L : heart_modules B S) (hL : IsLisseCoefficientModule B L) :
    P ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L) := by
  obtain ⟨R, _, M, hM, F, h0, hlast, hle, hq⟩ := hfil L hL
  apply heart_filtration_mem P _ R.n F h0 hlast hle
  intro b
  have : IsImmersion (R.immersion b) := R.isImmersion b
  have : TopologicalSpace.NoetherianSpace (R.domain b) :=
    (R.immersion b ≫ a).isEmbedding.isInducing.noetherianSpace
  have hf : CondensedRing.LocallyFree (condensedRingObj A (R.domain b)) (M b) := by
    obtain ⟨C, hC⟩ := (hM b).1
    exact ⟨C, fun t ↦ (CondensedRing.freeAt_iff_standard A (C.f t) (M b)).mpr (hC t)⟩
  obtain ⟨e⟩ := hq b
  exact P.prop_of_iso e.symm (hP (R.domain b) (R.immersion b ≫ a) inferInstance (M b) hf)

private theorem heart_vanishing_iso_raw
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ)
    {M N : (heart_modules Λ X)} (e : M ≅ N)
    (hM : ProperHeartHigherVanishing Λ p c M) : ProperHeartHigherVanishing Λ p c N := by
  intro q hq
  exact (hM q hq).of_iso (((CondensedRing.lowerStar Λ p).rightDerived q).mapIso e).symm

private theorem heart_vanishing_zero_raw
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ)
    (M : (heart_modules Λ X)) (hM : IsZero M) :
    ProperHeartHigherVanishing Λ p c M := by
  intro q _
  exact ((CondensedRing.lowerStar Λ p).rightDerived q).map_isZero hM

private theorem heart_vanishing_extensions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ) :
    ObjectProperty.IsClosedUnderExtensions (ProperHeartHigherVanishing Λ p c) := by
  constructor
  intro S hS h1 h3 q hq
  obtain ⟨δ, _, hδ⟩ := ShortComplex.ShortExact.exists_rightDerived_full_long_exact
    (CondensedRing.lowerStar Λ p) hS
  exact (hδ q).1.isZero_of_both_isZero (h1 q hq) (h3 q hq)

private theorem heart_vanishing_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms (ProperHeartHigherVanishing Λ p c) :=
  ⟨fun e h ↦ heart_vanishing_iso_raw Λ p c e h⟩

private theorem heart_vanishing_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (p : X ⟶ Y) (c : ℤ) :
    ObjectProperty.ContainsZero (ProperHeartHigherVanishing Λ p c) :=
  ⟨0, isZero_zero _, heart_vanishing_zero_raw Λ p c _ (isZero_zero _)⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem heart_lisse_transport
    {A B A' B' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    [MonObj A'] [IsCommMonObj A'] [MonObj B'] [IsCommMonObj B']
    (c : A ⟶ B) [IsMonHom c] (c' : A' ⟶ B') [IsMonHom c']
    (a : A ⟶ A') [IsMonHom a] [IsIso a]
    (b : B ⟶ B') [IsMonHom b] [IsIso b] (w : a ≫ c' = c ≫ b)
    (X : Scheme.{u}) [IsNoetherian X]
    (P : ObjectProperty ((heart_modules B X)))
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    [P.ContainsZero]
    (hP : ∀ (T : Scheme.{u}) (d : T ⟶ X) (hd : IsImmersion d)
      (M : (heart_modules A T)),
      CondensedRing.LocallyFree (condensedRingObj A T) M →
      P ((Mod.extendScalars (coefficientMap c X)).obj
        ((coefficientHeartLocallyClosedExtension A d hd).obj M)))
    {S : Scheme.{u}} (d : S ⟶ X) [IsImmersion d]
    (hfil : LatticeSubquotientFiltrationData A' B' c' d)
    (L : (heart_modules B S)) (hL : IsLisseCoefficientModule B L) :
    P ((coefficientHeartLocallyClosedExtension B d inferInstance).obj L) := by
  let F : (heart_modules B' X) ⥤ (heart_modules B X) :=
    Mod.comap (coefficientMap b X)
  let P' := P.inverseImage F
  let L' := (Mod.comap (coefficientMap (inv b) S)).obj L
  have hLF : CondensedRing.LocallyFree (condensedRingObj B S) L := by
    obtain ⟨C, hC⟩ := hL
    exact ⟨C, fun t ↦ (CondensedRing.freeAt_iff_standard B (C.f t) L).mpr (hC t)⟩
  have hL' : IsLisseCoefficientModule B' L' :=
    lisse_of_raw_free B' S L'
      (CondensedRing.locallyFree_comap (coefficientMap (inv b) S) hLF)
  have hg (T : Scheme.{u}) (f : T ⟶ X) (hf : IsImmersion f)
      (M : (heart_modules A' T))
      (hM : CondensedRing.LocallyFree (condensedRingObj A' T) M) :
      P' ((Mod.extendScalars (coefficientMap c' X)).obj
        ((coefficientHeartLocallyClosedExtension A' f hf).obj M)) := by
    let := hf
    let N := (Mod.comap (coefficientMap a T)).obj M
    have hN := CondensedRing.locallyFree_comap (coefficientMap a T) hM
    have square : coefficientMap a X ≫ coefficientMap c' X =
        coefficientMap c X ≫ coefficientMap b X := by
      simpa only [coefficientMap, ← Functor.map_comp] using
        congrArg ((upperStarFromPoint X).map) w
    let e := (CondensedRing.scalarTransportIso (coefficientMap c X)
      (coefficientMap c' X) (coefficientMap a X) (coefficientMap b X) square).app
        ((coefficientHeartLocallyClosedExtension A' f hf).obj M)
    exact P.prop_of_iso
      (e.symm ≪≫ (Mod.extendScalars (coefficientMap c X)).mapIso
        ((integralModel_comap_extension a f).app M)).symm
      (hP T f hf N hN)
  have h := heart_lisse_of_filtration A' B' c' X P' hg d hfil L' hL'
  let e : (Mod.comap (coefficientMap b S)).obj L' ≅ L :=
    ((Mod.comapComp (coefficientMap b S) (coefficientMap (inv b) S)).symm ≪≫
      Mod.comapCongr (by
        simp only [coefficientMap, ← Functor.map_comp, IsIso.hom_inv_id]
        exact (upperStarFromPoint S).map_id B) ≪≫ Mod.comapId _).app L
  exact P.prop_of_iso
    ((integralModel_comap_extension b d).app L' ≪≫
      (coefficientHeartLocallyClosedExtension B d inferInstance).mapIso e) h

set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] LatticeSubquotientFiltrationData in
private theorem heart_lisse_small
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP k p] (hℓp : ℓ ≠ p) (X : Scheme.{u})
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (P : ObjectProperty ((heart_modules (Profinite.continuousMapRingObj E.1) X)))
    [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero]
    (hP : ∀ (T : Scheme.{u}) (d : T ⟶ X) (hd : IsImmersion d)
      (M : (heart_modules (Profinite.padicIntegersRingObj ℓ E.1) T)),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) M →
      P ((properHeartRationalization ℓ E X).obj
        ((coefficientHeartLocallyClosedExtension
          (Profinite.padicIntegersRingObj ℓ E.1) d hd).obj M)))
    : heart_lisse_extensions (Profinite.continuousMapRingObj E.1) X P := by
  rw [heart_lisse_extensions]
  intro S d hd L hL
  let := hd
  let E' := ULift.{u} E.1
  have hm := integralModel_liftIntegers.{u} ℓ E
  let O' := Padic.coefficientExtensionIntegers ℓ E'
  let eO : PadicAlgCl.integers ℓ E.1 ≃+* O' :=
    { toFun := fun x ↦ ⟨ULift.up x.val, (hm _).mpr (by
        exact_mod_cast x.property)⟩
      invFun := fun x ↦ ⟨x.val.down, by
        have h := (hm x.val).mp x.property
        exact_mod_cast h⟩
      left_inv := fun x ↦ rfl
      right_inv := fun x ↦ by cases x; rfl
      map_mul' := fun x y ↦ rfl
      map_add' := fun x y ↦ rfl }
  let eF : E.1 ≃+* E' := ULift.ringEquiv.symm
  let aO := integralModel_coefficientIso eO
    ((continuous_uliftUp.comp continuous_subtype_val).subtype_mk _)
    ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)
  let aF := integralModel_coefficientIso eF
    continuous_uliftUp continuous_uliftDown
  let forget := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let A' := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} O')
  let B' := coefficientHeartRingObj (Profinite.continuousMapRingSheafOfUniverse.{u, u} E')
  let c' : A' ⟶ B' := forget.map
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} O'.subtype continuous_subtype_val)
  have : IsCommMonObj A' := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} O')
    (fun U (a b : ULift.{u + 1} C(U.unop, O')) ↦ mul_comm a b)
  have : IsCommMonObj B' := Sheaf.isCommMonObj_sheafCompose_obj _
    (Profinite.continuousMapRingSheafOfUniverse.{u, u} E')
    (fun U (a b : ULift.{u + 1} C(U.unop, E')) ↦ mul_comm a b)
  have : IsMonHom c' := Sheaf.isMonHom_sheafCompose_map _
    (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} O'.subtype continuous_subtype_val)
  have : IsMonHom (forget.map aO.hom) := Sheaf.isMonHom_sheafCompose_map _ aO.hom
  have : IsMonHom (forget.map aF.hom) := Sheaf.isMonHom_sheafCompose_map _ aF.hom
  have hf :=
    integralModel_lattice_small k p ℓ hℓp X E d
  apply heart_lisse_transport
    (A := Profinite.padicIntegersRingObj ℓ E.1)
    (B := Profinite.continuousMapRingObj E.1) (A' := A') (B' := B')
    (AlgebraicGeometry.ProEtale.padicIntegersRingObjToContinuousMapRingObj ℓ E)
    c' (forget.map aO.hom) (forget.map aF.hom) ?_ X P ?_ d hf L hL
  · dsimp only [aO, aF]
    ext T f
    delta integralModel_coefficientIso
    rfl
  · intro T b hb N hN
    exact hP T b hb N (lisse_of_raw_free _ T N hN)

private theorem heart_constructible_mem
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (r : ℕ) [Fact r.Prime] [CharP k r] (hrℓ : r ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsNoetherian X]
    (P : ObjectProperty ((heart_modules (coefficientHeartRingObj Λ) X)))
    [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero]
    (hP : heart_lisse_extensions (coefficientHeartRingObj Λ) X P)
    (M : ConstantModelConstructible (coefficientHeartRingObj Λ) X) : P M.obj := by
  rw [heart_lisse_extensions] at hP
  have hheart := coefficientHeart ℓ Λ hΛ k r hrℓ X
  obtain ⟨n, T, h0, htop, hle, hq⟩ := hheart.2.2.2.2.2.2.2.2.2.2.1 M
  apply heart_filtration_mem P M.obj n T h0 htop hle
  intro a
  obtain ⟨S, j, hj, L, hL, ⟨e⟩⟩ := hq a
  exact P.prop_of_iso e.symm (hP S j hj L hL)

private theorem heart_lisse_scalar
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] (S : Scheme.{u})
    (M : (heart_modules A S)) (hM : IsLisseCoefficientModule A M) :
    IsLisseCoefficientModule B ((Mod.extendScalars (coefficientMap c S)).obj M) := by
  have hfree : CondensedRing.LocallyFree (condensedRingObj A S) M := by
    obtain ⟨C, hC⟩ := hM
    exact ⟨C, fun t ↦ (CondensedRing.freeAt_iff_standard A (C.f t) M).mpr (hC t)⟩
  exact lisse_of_raw_free B S _
    (integralModel_locallyFree_scalar c S M hfree)

private noncomputable def heart_extension_scalar
    {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (c : A ⟶ B) [IsMonHom c] {S X : Scheme.{u}} [IsNoetherian X]
    (a : S ⟶ X) [IsImmersion a] (L : (heart_modules A S)) :
    (Mod.extendScalars (coefficientMap c X)).obj
        ((coefficientHeartLocallyClosedExtension A a inferInstance).obj L) ≅
      (coefficientHeartLocallyClosedExtension B a inferInstance).obj
        ((Mod.extendScalars (coefficientMap c S)).obj L) := by
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  simpa only [coefficientHeartLocallyClosedExtension,
    integralLowerShriek] using
    integralModel_extension_scalar c a.toImage a.imageι L

set_option backward.isDefEq.respectTransparency.types false in
private theorem heart_algCl_lisse
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (r : ℕ) [Fact r.Prime] [CharP k r] (hrℓ : r ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsNoetherian X]
    (P : ObjectProperty ((heart_modules (Profinite.padicAlgClRingObj ℓ) X)))
    [P.IsClosedUnderExtensions] [P.IsClosedUnderIsomorphisms]
    [P.ContainsZero]
    (hP : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F →
      ∀ (T : Scheme.{u}) (b : T ⟶ X) (hb : IsImmersion b)
        (M : (heart_modules (Profinite.padicIntegersRingObj ℓ F) T)),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F) M →
      P ((Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X)).obj
          ((properHeartRationalization ℓ F X).obj
            ((coefficientHeartLocallyClosedExtension
              (Profinite.padicIntegersRingObj ℓ F) b hb).obj M))))
    : heart_lisse_extensions (Profinite.padicAlgClRingObj ℓ) X P := by
  rw [heart_lisse_extensions]
  intro S a ha L hL
  have : IsImmersion a := ha
  have : TopologicalSpace.NoetherianSpace S := a.isEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian a
  obtain ⟨F0, L0, hL0, ⟨e0⟩⟩ := (coefficient_finite_descent_lisse S ℓ).1 L hL
  obtain ⟨F, hEF, hF0F⟩ := exists_ge_ge E F0
  let t := Profinite.padicSubfieldRingObjMap ℓ hF0F
  let s := Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F
  let L1 := (Mod.extendScalars (coefficientMap t S)).obj L0
  have hL1 := heart_lisse_scalar t S L0 hL0
  let e1 : (Mod.extendScalars (coefficientMap s S)).obj L1 ≅ L :=
    ((Mod.extendScalarsComp (coefficientMap t S) (coefficientMap s S)).symm ≪≫
      Mod.extendScalarsIsoOfEq (by
        rw [coefficientMap, coefficientMap, ← Functor.map_comp,
          Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl])).app L0 ≪≫ e0
  let G := Mod.extendScalars (coefficientMap s X)
  have : PreservesFiniteLimits G :=
    CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl ℓ X F
  let P' := P.inverseImage G
  have h := heart_lisse_small k r ℓ (Ne.symm hrℓ) X F P'
    (hP F hEF)
  rw [heart_lisse_extensions] at h
  have h := h S a inferInstance L1 hL1
  exact P.prop_of_iso (heart_extension_scalar s a L1 ≪≫
    (coefficientHeartLocallyClosedExtension
      (Profinite.padicAlgClRingObj ℓ) a inferInstance).mapIso e1) h

private theorem heart_prop_cases
    {A : Type*} {D : A → Prop} (Q : ∀ a, D a → Prop)
    {a b x : A} (ha : D a) (hb : D b) (hx : D x)
    (h : x = a ∨ x = b) (qa : Q a ha) (qb : Q b hb) : Q x hx := by
  rcases h with rfl | rfl
  · exact qa
  · exact qb

-- Keep the family of object properties abstract while changing coefficient presentations.
attribute [local irreducible] Mod.extendScalars properHeartRationalization
  coefficientHeartLocallyClosedExtension in
set_option backward.isDefEq.respectTransparency.types false in
private theorem heart_family_reduction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (r : ℕ) [Fact r.Prime] [CharP k r] (hrℓ : r ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsNoetherian X]
    (P : ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ], ObjectProperty (heart_modules Λ X))
    (hext : ∀ Λ [MonObj Λ] [IsCommMonObj Λ], (P Λ).IsClosedUnderExtensions)
    (hiso : ∀ Λ [MonObj Λ] [IsCommMonObj Λ], (P Λ).IsClosedUnderIsomorphisms)
    (hzero : ∀ Λ [MonObj Λ] [IsCommMonObj Λ], (P Λ).ContainsZero)
    (hfinite : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F →
    ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L₀ : pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ F) S),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F) L₀ →
      P (Profinite.continuousMapRingObj F)
        ((properHeartRationalization ℓ F X).obj
          ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
            a ha).obj L₀)))
    (halgCl : ∀ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F →
    ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L₀ : pulledBackModuleObjects (Profinite.padicIntegersRingObj ℓ F) S),
      IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ F) L₀ →
      P (Profinite.padicAlgClRingObj ℓ)
        ((Mod.extendScalars
          (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) X)).obj
          ((properHeartRationalization ℓ F X).obj
            ((coefficientHeartLocallyClosedExtension (Profinite.padicIntegersRingObj ℓ F)
              a ha).obj L₀))))
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : Λ = Profinite.padicSubfieldCondensedRing ℓ E ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    : heart_lisse_extensions (coefficientHeartRingObj Λ) X (P (coefficientHeartRingObj Λ)) := by
  apply heart_prop_cases
    (D := fun A : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} ↦
      IsCommMonObj (coefficientHeartRingObj A))
    (Q := fun A hA ↦ let _ := hA;
      heart_lisse_extensions (coefficientHeartRingObj A) X (P (coefficientHeartRingObj A)))
    (a := Profinite.padicSubfieldCondensedRing ℓ E)
    (b := Profinite.padicAlgClCondensedRing ℓ)
    inferInstance inferInstance inferInstance hΛ
  · dsimp only
    have : (P (Profinite.continuousMapRingObj E)).IsClosedUnderExtensions := hext _
    have : (P (Profinite.continuousMapRingObj E)).IsClosedUnderIsomorphisms := hiso _
    have : (P (Profinite.continuousMapRingObj E)).ContainsZero := hzero _
    exact heart_lisse_small k r ℓ (Ne.symm hrℓ) X E _ (hfinite E le_rfl)
  · dsimp only
    have : (P (Profinite.padicAlgClRingObj ℓ)).IsClosedUnderExtensions := hext _
    have : (P (Profinite.padicAlgClRingObj ℓ)).IsClosedUnderIsomorphisms := hiso _
    have : (P (Profinite.padicAlgClRingObj ℓ)).ContainsZero := hzero _
    exact heart_algCl_lisse ℓ E k r hrℓ X _ halgCl


attribute [local irreducible] Mod.extendScalars
  properHeartRationalization ProperHeartHigherVanishing
  coefficientHeartLocallyClosedExtension in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A uniform proper direct-image bound for integral lattices extended from strata, their
localizations, and their algebraic-closure scalar extensions implies the same bound for
every constructible E- or Qbar_l-module. The Noetherian instance in the assertion is derived
from finite type over k, without imposing any additional geometric hypothesis.

Source: blueprint sk-lem-proper-heart-bound-reduction.md and its proof, Extensions, Strata,
Lattices (blueprint: det-proper-heart-bound-reduction).

Proof:
1. Fix a nonnegative degree q greater than c. The full right-derived long exact sequence
makes vanishing of R^q p_* closed under extensions. Induct on a finite subobject filtration,
using the short exact sequence of each successive cokernel.
2. Finite type over k makes X Noetherian. Clause (11) of coefficientHeart gives a finite
filtration of a constructible module by locally closed extensions of lisse modules.
3. For finite coefficients, lattice-subquotient filtration gives another finite filtration,
whose quotients are rationalized extensions of integral lisse lattices. The proved
coefficient transport helpers in IntegralModelsGenerators identify the universe-lifted
spectral-norm presentation with the original coefficient rings. Apply the premise to the
quotients and then the filtration induction.
4. For algebraic-closure coefficients, descend the lisse module to F0, enlarge to the finite
common upper bound F of F0 and E, and extend the descended module to F. It stays lisse, and ordinary
scalar transitivity identifies its algebraic-closure extension with the original module.
5. Apply step 3 to vanishing after scalar extension F to Qbar_l. This property is closed
under extensions by exactness of scalar extension. Ordinary scalar compatibility with
locally closed extension identifies the result, and step 2 finishes the proof. -/
theorem properHeartBoundReduction (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (r : ℕ) [Fact r.Prime] [CharP k r] (_hrℓ : r ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (c : ℤ) :
    @ProperHeartBoundReductionAssertions ℓ _ E X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
      p c := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  intro htest Λ _ hΛ M
  let P : ObjectProperty (heart_modules (coefficientHeartRingObj Λ) X) :=
    ProperHeartHigherVanishing (coefficientHeartRingObj Λ) p c
  have : P.IsClosedUnderExtensions := heart_vanishing_extensions _ p c
  have : P.IsClosedUnderIsomorphisms := heart_vanishing_iso _ p c
  have : P.ContainsZero := heart_vanishing_zero _ p c
  apply heart_constructible_mem ℓ Λ ?_ k r _hrℓ X P ?_ M
  · rcases hΛ with h | h
    · exact Or.inl ⟨E.1, inferInstance, h⟩
    · exact Or.inr h
  · exact heart_family_reduction ℓ E k r _hrℓ X
      (fun A _ _ ↦ ProperHeartHigherVanishing A p c)
      (fun A _ _ ↦ heart_vanishing_extensions A p c)
      (fun A _ _ ↦ heart_vanishing_iso A p c)
      (fun A _ _ ↦ heart_vanishing_zero A p c)
      (fun F hEF T b hb N hN ↦ (htest F hEF T b hb N hN).2.1)
      (fun F hEF T b hb N hN ↦ (htest F hEF T b hb N hN).2.2) Λ hΛ

end AlgebraicGeometry.ProEtale
