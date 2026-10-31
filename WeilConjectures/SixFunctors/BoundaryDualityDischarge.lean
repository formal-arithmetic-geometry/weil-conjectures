/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BoundaryDualityInput
import WeilConjectures.SixFunctors.BoundaryNormalizedModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleIhom
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleDevissageSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleBound
public import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# Discharge of the finite-stage boundary duality input

Source: current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`cor-weil-boundary-duality-discharge.proof.md`,
node `cor-weil-boundary-duality-discharge` (blueprint: cor-weil-boundary-duality-discharge).

The proof follows the finite-stage small-site duality and its comparison transport: finite-type
locally closed pieces are separated and finite type, duality preserves the finite-Tor constructible
subcategory, and the normalized tensor-Hom transposes identify the canonical boundary exchange
with the double-dual comparison. The pro-etale comparison transports these maps and identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

section Formal
universe i b c e v w
open CategoryTheory.MonoidalCategory MonoidalClosed Opposite
open BoundaryDualityInput
variable {I : Type i} {B : I → I → Type b}
  {P : I → Type c} [∀ T, Category.{v} (P T)] [∀ T, MonoidalCategory (P T)]
  [∀ T, SymmetricCategory (P T)] [∀ T, MonoidalClosed (P T)]
  {E : I → Type e} [∀ T, Category.{w} (E T)] [∀ T, MonoidalCategory (E T)]

private theorem model_delta (o : Operations B P E) (ctf : ∀ T, P T → Prop)
    (m : NormalizedModel o ctf) (T : I) (K : P T) :
    o.delta T K = toIhomIhom (o.omega T) K := by
  unfold Operations.delta
  rw [m.evaluation]
  rfl

private theorem model_exchange (o : Operations B P E) (ctf : ∀ T, P T → Prop)
    (m : NormalizedModel o ctf) {Z T : I} (f : B Z T) (L : P T) (hL : ctf T L) :
    o.exchange f (m.theta f) L (m.tau f _ _ (m.preserves T L hL)) =
      BoundaryBidualTranspose.beta (o.omega T) (o.omega Z)
        (o.star f) (o.exceptional f) (m.theta f) (ctf T) (m.preserves T)
        (fun M N hM _ ↦ m.tau f M N hM) L hL := by
  unfold Operations.exchange Operations.transpose BoundaryBidualTranspose.beta
    BoundaryBidualTranspose.boundaryPairing
  rw [m.symmetry, m.evaluation]
  rfl

private theorem model_alpha (o : Operations B P E) (ctf : ∀ T, P T → Prop)
    (m : NormalizedModel o ctf) {Z T : I} (f : B Z T) (K : P T) (hK : ctf T K) :
    BoundaryBidualTranspose.alpha (o.omega T) (o.omega Z)
        (o.star f) (o.exceptional f) (m.theta f) (ctf T) (m.preserves T)
        (fun M N hM _ ↦ m.tau f M N hM) K hK =
      o.transpose Z _ _
        ((o.symmetry Z _ _).hom ≫ m.tau f K ((o.dual T).obj (op K)) hK ≫
          (o.exceptional f).map ((o.symmetry T _ _).hom ≫ o.evaluation T K) ≫
          (m.theta f).hom) := by
  unfold BoundaryBidualTranspose.alpha BoundaryBidualTranspose.exceptionalPairing
    Operations.transpose
  rw [m.symmetry, m.symmetry, m.evaluation, m.symmetry]
  rfl

private theorem formal_opposite_currying
    {Z T : I} (ωT : P T) (ωZ : P Z) (s G : P T ⥤ P Z)
    (h : G.obj ωT ≅ ωZ) (ST : P T → Prop)
    (hDT : ∀ K, ST K → ST ((ihom K).obj ωT))
    (q : ∀ M N, ST M → ST N → (s.obj M ⊗ G.obj N ⟶ G.obj (M ⊗ N)))
    (hq : ∀ M M' N N' hM hM' hN hN' (a : M ⟶ M') (b : N ⟶ N'),
      (s.map a ⊗ₘ G.map b) ≫ q M' N' hM' hN' = q M N hM hN ≫ G.map (a ⊗ₘ b))
    (L : P T) (hL : ST L) :
    (BoundaryBidualTranspose.bidualComposite ωT ωZ
      s G h ST hDT
      q L hL ⊗ₘ
        𝟙 (s.obj ((ihom L).obj ωT))) ≫
      (β_ ((ihom (s.obj ((ihom L).obj ωT))).obj ωZ)
        (s.obj ((ihom L).obj ωT))).hom ≫
      (ihom.ev (s.obj ((ihom L).obj ωT))).app ωZ =
    (β_ (G.obj L) (s.obj ((ihom L).obj ωT))).hom ≫
      BoundaryBidualTranspose.boundaryPairing ωT ωZ
        s G h ST hDT
        q L hL := by
  have heval :
      ((ihom L).obj ωT ◁ toIhomIhom ωT L) ≫
        (ihom.ev ((ihom L).obj ωT)).app ωT =
      (β_ ((ihom L).obj ωT) L).hom ≫ (ihom.ev L).app ωT := by
    rw [← uncurry_eq, uncurry_toIhomIhom]
  have hnat := hq ((ihom L).obj ωT) ((ihom L).obj ωT)
    L ((ihom ((ihom L).obj ωT)).obj ωT)
    (hDT L hL) (hDT L hL) hL (hDT _ (hDT L hL)) (𝟙 _) (toIhomIhom ωT L)
  rw [s.map_id, id_tensorHom] at hnat
  unfold BoundaryBidualTranspose.bidualComposite
  rw [tensorHom_id, comp_whiskerRight_assoc,
    BraidedCategory.braiding_naturality_left_assoc, ← uncurry_eq,
    BoundaryBidualTranspose.alpha, uncurry_curry]
  simp only [BoundaryBidualTranspose.exceptionalPairing,
    SymmetricCategory.symmetry_assoc]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  unfold BoundaryBidualTranspose.boundaryPairing
  rw [← Category.assoc _ (q _ _ _ _) _, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map _) (G.map _) _, ← G.map_comp, id_tensorHom, heval]

private theorem assertions_of_normalized_model
    (o : Operations B P E) (ctf : ∀ T, P T → Prop) (m : NormalizedModel o ctf)
    (hc : ∀ T, ObjectProperty.IsClosedUnderIsomorphisms (ctf T)) :
    Nonempty (Assertions B P E o ctf) := by
  let a {Z T : I} (f : B Z T) (K : P T) (hK : ctf T K) :=
    BoundaryBidualTranspose.alpha (o.omega T) (o.omega Z)
      (o.star f) (o.exceptional f) (m.theta f) (ctf T) (m.preserves T)
      (fun M N hM _ ↦ m.tau f M N hM) K hK
  have ha {Z T : I} (f : B Z T) K hK : IsIso (a f K hK) := m.alpha_iso f K hK
  have identities {Z T : I} (f : B Z T) := by
    letI := hc T
    exact BoundaryBidualTranspose.bidual_transpose (o.omega T) (o.omega Z)
      (o.star f) (o.exceptional f) (m.theta f) (ctf T) (m.preserves T)
      (fun M N hM _ ↦ m.tau f M N hM) (⊤ : ObjectProperty (P Z))
      (fun _ _ ↦ trivial) (fun _ _ ↦ trivial) (fun _ _ ↦ trivial)
      (m.tau_natural f) (formal_opposite_currying (o.omega T) (o.omega Z)
        (o.star f) (o.exceptional f)
        (m.theta f) (ctf T) (m.preserves T) (fun M N hM _ ↦ m.tau f M N hM)
        (m.tau_natural f))
  refine ⟨{
    preserves := m.preserves
    theta := m.theta
    theta_normalization := m.theta_normalization
    tau := m.tau
    tau_normalization := m.tau_normalization
    exchange_isIso := ?_
    alpha := fun f K hK ↦ @asIso _ _ _ _ (a f K hK) (ha f K hK)
    alpha_normalization := ?_
    compatibility := ?_ }⟩
  · intro Z T f L hL
    rw [model_exchange o ctf m f L hL]
    exact ((identities f).2.2.1 L hL (m.alpha_iso f _ (m.preserves T L hL))
      (m.delta_iso T L hL)
      (m.delta_iso Z _ (m.star_preserves f _ (m.preserves T L hL)))).2
  · intro Z T f K hK
    exact model_alpha o ctf m f K hK
  · intro Z T f K hK
    rw [model_delta o ctf m, model_exchange o ctf m, model_delta o ctf m]
    exact (identities f).2.1 K hK
end Formal

private theorem ctf_closed_under_iso
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (BoundaryDualityInput.ctf l E n X) := by
  constructor
  intro K L e hK
  let F := (sfIntrinsicDerivedEquivalence X
    (Padic.coefficientExtensionRing l E (n + 1))).functor
  change WeilConjectures.finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
    (F.obj L)
  change WeilConjectures.finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
    (F.obj K) at hK
  refine ⟨?_, ?_⟩
  · exact (Scheme.finiteTorsionConstructible D l hl E (n + 1) (Nat.succ_pos n) X).prop_of_iso
      (F.mapIso e) hK.1
  · obtain ⟨a, b, hab, ht⟩ := hK.2
    refine ⟨a, b, hab, ?_⟩
    intro M P he f hf hP N i hi
    exact ht M P (he.map (fun j ↦ j ≪≫ (F.mapIso e).symm)) f hf hP N i hi

attribute [local instance] DerivedCategory.symmetricCategory

/--
The finite-stage boundary duality input holds for every separated finite-type scheme over the
fixed algebraic closure of a finite field and every positive finite coefficient level. Its second
clause is the canonical evaluation-defined boundary exchange, including its evaluation and
double-dual compatibility.

Source: current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`cor-weil-boundary-duality-discharge.proof.md`,
node `cor-weil-boundary-duality-discharge` (blueprint: cor-weil-boundary-duality-discharge).

Proof: Obtain the normalized geometric model, before boundary exchange, from
boundary_normalized_models. Finite-Tor constructibility is invariant under isomorphism:
transport the constructibility predicate and the chosen representative of each Tor interval.
The normalized evaluation identifies the specified delta with toIhomIhom; the normalized
symmetry identifies the specified exchange and alpha with the formal beta and alpha.
Apply bidual_transpose. The opposite-currying calculation from tau naturality expresses beta
as the dual of the
bidual composite followed by delta. Preservation, alpha invertibility and biduality make
both factors invertible. Its second transpose identity gives exactly the required
compatibility. Keep theta and tau with their normalization equations unchanged.
-/
theorem boundary_duality_input
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ)
    (Y : Scheme.{u})
    (aY : Y ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    BoundaryDualityInput D l hl E n Y aY := by
  classical
  obtain ⟨o, ho, ⟨m⟩⟩ :=
    BoundaryDualityInput.boundary_normalized_models D l hl E n Y aY
  exact ⟨o, ho, assertions_of_normalized_model o _ m
    (fun T ↦ ctf_closed_under_iso D l hl E n T.scheme)⟩

end AlgebraicGeometry.ProEtale
