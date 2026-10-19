/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.FiniteQuotientStrictLocalInvariants
import Sheaf.AlgebraicGeometry.TameAdmissibleSchemeQuotient

/-!
# The very tame local Kummer quotient

Source: Illusie--Laszlo--Orgogozo, Exposé VI, Proposition 3.5(b), §3.4,
proof 3.7(b) and the opening of 3.7(c), printed pp.74--76
(blueprint: lem-per-very-tame-local-kummer-quotient).

Multiplicative notation writes the zero of a sharp monoid as `1`.
The invariant log sheaf is characterized on every étale test object, before
asserting that it has an fs chart. The quotient-ring isomorphism is pinned
to the inclusion of invariants, rather than an unspecified abstract isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Evaluation of the given pairing, in multiplicative notation.
Source: ILO VI §3.4 (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerCharacter {A : Type u} [CommRing A] {H : Type v} [Group H]
    {Q : Type u} [CommMonoid Q]
    (χ : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup Q)) →+
        Additive (rootsOfUnity (Nat.card H) A))
    (h : H) (q : Algebra.GrothendieckGroup Q) : rootsOfUnity (Nat.card H) A :=
  (χ (TensorProduct.tmul ℤ (Additive.ofMul (Abelianization.of h))
    (Additive.ofMul q))).toMul

/-- The common character kernel in the actual group completion.
Source: ILO VI 3.7(b), P' (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerLattice {A : Type u} [CommRing A] {H : Type v} [Group H]
    {Q : Type u} [CommMonoid Q]
    (χ : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup Q)) →+
        Additive (rootsOfUnity (Nat.card H) A)) : Subgroup (Algebra.GrothendieckGroup Q) where
  carrier := {q | ∀ h : H, localKummerCharacter χ h q = 1}
  one_mem' := by simp [localKummerCharacter]
  mul_mem' := by
    intro a b ha hb h
    change (χ (TensorProduct.tmul ℤ _ (Additive.ofMul (a * b)))).toMul = 1
    change (χ (TensorProduct.tmul ℤ _ (Additive.ofMul a + Additive.ofMul b))).toMul = 1
    rw [TensorProduct.tmul_add, map_add]
    change localKummerCharacter χ h a * localKummerCharacter χ h b = 1
    rw [ha h, hb h, one_mul]
  inv_mem' := by
    intro a ha h
    change (χ (TensorProduct.tmul ℤ _ (Additive.ofMul a⁻¹))).toMul = 1
    change (χ (TensorProduct.tmul ℤ _ (-Additive.ofMul a))).toMul = 1
    rw [TensorProduct.tmul_neg, map_neg]
    change (localKummerCharacter χ h a)⁻¹ = 1
    rw [ha h, inv_one]

/-- The invariant sharp submonoid P = Q ∩ L, formed by inverse image.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerMonoid {A : Type u} [CommRing A] {H : Type v} [Group H]
    {Q : Type u} [CommMonoid Q]
    (χ : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup Q)) →+
        Additive (rootsOfUnity (Nat.card H) A)) : Submonoid Q :=
  (localKummerLattice χ).toSubmonoid.comap Algebra.GrothendieckGroup.of

/-- The fixed subring of the prescribed ring maps. The action laws are supplied
by the log action when this construction is used below.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerInvariantRing {A : Type u} [CommRing A] {H : Type v}
    (σ : H → A →+* A) : Subring A :=
  ⨅ h : H, (σ h).eqLocus (RingHom.id A)

/-- The ideal of the sharp chart's closed stratum; this includes Q = {1}.
Source: ILO VI 3.7(b)--(c) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerStratumIdeal {A : Type u} [CommRing A] {Q : Type u} [CommMonoid Q]
    (a : Q →* A) : Ideal A :=
  Ideal.span {x | ∃ q : Q, q ≠ 1 ∧ a q = x}

/-- The identity étale object, used for a chart on Spec A.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
abbrev localKummerTop (A : Type u) [CommRing A] : (Spec (.of A)).Etale :=
  Scheme.Etale.mk (𝟙 (Spec (.of A)))

/-- The ring-valued chart obtained from the log chart and Γ(Spec A) = A.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def localKummerRingChart {A : Type u} [CommRing A]
    (M : EtaleLogStructure (Spec (.of A))) {Q : Type u} [CommMonoid Q]
    (a : Q →* M.monoidSheaf.obj.obj (op (localKummerTop A))) : Q →* A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom.toMonoidHom.comp
    ((M.alpha.app (op (localKummerTop A))).hom.comp a)

/-- The affine fs source with its given log structure; no associated log structure
or replacement chart is chosen.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
abbrev localKummerSource (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : EtaleLogStructure (Spec (.of A))) (hM : M.IsFineSaturated) :
    FineSaturatedLogScheme.{u} :=
  ⟨Spec (.of A), inferInstance, M, hM⟩

/-- The very tame local quotient has the specified invariant fs chart and the
same closed stratum. The canonical group-completion map has image L. The final
ring isomorphism commutes with the two quotient maps, specifying B/J → A/I.

Source: ILO VI Proposition 3.5(b), §3.4, proof 3.7(b), and the opening of 3.7(c),
printed pp.74--76 (blueprint: lem-per-very-tame-local-kummer-quotient).

Proof:
1. Apply lem-per-tame-admissible-scheme-quotient to Spec A and then
lem-per-finite-quotient-strict-local-invariants: B = A^H is the strict local
quotient and the invariant direct-image stalk is the actual invariant log stalk.
2. Retain the given diagonal chart. At the closed point the log stalk is
Q times A-units, and the nonunit ideal is the displayed stratum ideal I.
3. The character kernel L has finite index, contains n Q^gp, and P = L ∩ Q
is sharp and saturated. For finite generation, reduce coefficients of a finite
set of Q-generators modulo n, retaining only the residues in L. For l = u/v
in L, both v^n and l v^n = u v^(n-1) lie in P, proving P^gp = L.
4. If u a(q) is invariant, reduction modulo the maximal ideal shows χ_q(h) = 1:
the residue action is trivial and reduction is injective on nth roots, since n
is a unit. Then u is invariant too. Thus the closed invariant stalk is P times
B-units, including all possible unit twists.
5. Apply lem-per-tame-diagonal-standard-closed-immersion. Its target-chart
assertion identifies the chart of the actual invariant sheaf at all nearby
geometric points, and its surjective comparison B ⊗ Z[Q] → A expresses every
element of A as a B-linear sum of chart monomials.
6. Reynolds averaging is the identity modulo I, so B → A/I is surjective.
Expand coefficients of elements of I using Step 5 before averaging. A nontrivial
character averages to zero (a nontrivial nth root differs from 1 by a unit),
and a trivial character retains precisely the nonidentity P-monomials.
Consequently B ∩ I = J and the canonical B/J → A/I is an isomorphism.
7. For data before strict localization, the target neighbourhood supplied by
the same comparison theorem represents this very chart; see the neighbourhood
statement below. No regularity or logarithmic dimension formula is used.
-/
theorem veryTame_local_kummer_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsStrictlyHenselianLocalRing A]
    (M : EtaleLogStructure (Spec (.of A))) (hM : M.IsFineSaturated)
    (H : Type v) [Group H] [Finite H]
    (action : FSLogGroupAction H (localKummerSource A M hM))
    (σ : H → A →+* A)
    (hσ : ∀ (h : H) (r : A), σ h r = (Scheme.ΓSpecIso (.of A)).hom
      ((action.baseAction h).hom.appTop ((Scheme.ΓSpecIso (.of A)).inv r)))
    (hresidue : ∀ (h : H) (r : A),
      IsLocalRing.residue A (σ h r) = IsLocalRing.residue A r)
    (hn : IsUnit (Nat.card H : A))
    (ζ : A) (hζ : IsPrimitiveRoot ζ (Nat.card H))
    (hζfixed : ∀ h : H, σ h ζ = ζ)
    (Q : Type u) [CommMonoid Q] (hQ : IsFineSaturatedMonoid Q)
    (hsharp : ∀ q : Q, IsUnit q → q = 1)
    (a : Q →* M.monoidSheaf.obj.obj (op (localKummerTop A)))
    (ha : M.IsChart (localKummerTop A) a)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of A))
    (hx : (Scheme.SpecToEquivOfField Ω (Spec (.of A)) x).1 =
      IsLocalRing.closedPoint A)
    (hchar : Function.Bijective (fun q : Q ↦ Associates.mk
      (M.toEtalePrelogStructure.germ x (localKummerTop A) (Over.homMk x) (a q))))
    (χ : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup Q)) →+
        Additive (rootsOfUnity (Nat.card H) A))
    (heigen : ∀ (h : H) (q : Q),
      ∃ z : (M.monoidSheaf.obj.obj (op (localKummerTop A)))ˣ,
        (Scheme.ΓSpecIso (.of A)).hom (M.alpha.app (op (localKummerTop A)) z.val) =
          (localKummerCharacter χ h (Algebra.GrothendieckGroup.of q)).val.val ∧
        (action.logMap h).sectionMap (localKummerTop A) (localKummerTop A)
          (action.baseAction h).hom (by
            change (action.baseAction h).hom ≫ 𝟙 _ = 𝟙 _ ≫ (action.logMap h).base
            simpa only [Category.comp_id, Category.id_comp] using (action.base_eq h).symm)
          (a q) = z.val * a q)
    (hstratum : ∀ (h : H) (r : A),
      σ h r - r ∈ localKummerStratumIdeal (localKummerRingChart M a))
    (hfinite : Module.Finite (localKummerInvariantRing σ) A) :
    IsFineSaturatedMonoid (localKummerMonoid χ) ∧
      (∀ p : localKummerMonoid χ, IsUnit p → p = 1) ∧
      (Algebra.GrothendieckGroup.lift
        (Algebra.GrothendieckGroup.of.comp (localKummerMonoid χ).subtype)).range =
          localKummerLattice χ ∧
      (localKummerLattice χ).FiniteIndex ∧
      (∀ g : Algebra.GrothendieckGroup Q, g ^ Nat.card H ∈ localKummerLattice χ) ∧
      ∃ (b : localKummerMonoid χ →* localKummerInvariantRing σ),
        (∀ p, (b p).val = localKummerRingChart M a p.val) ∧
        (∃ (N : EtaleLogStructure (Spec (.of (localKummerInvariantRing σ))))
          (d : FSLogGroupAction.InvariantDirectImage action
            (Spec.map (CommRingCat.ofHom (localKummerInvariantRing σ).subtype)) N)
          (c : localKummerMonoid χ →* N.monoidSheaf.obj.obj
            (op (localKummerTop (localKummerInvariantRing σ)))),
          N.IsChart (localKummerTop (localKummerInvariantRing σ)) c ∧
          (∀ p, localKummerRingChart N c p = b p) ∧
          (∀ p, d.pullbackMap (localKummerTop (localKummerInvariantRing σ)) (c p) =
            M.monoidSheaf.obj.map
              (MorphismProperty.Over.homMk
                (logInvariantTest
                  (Spec.map (CommRingCat.ofHom (localKummerInvariantRing σ).subtype))
                  (localKummerTop (localKummerInvariantRing σ))).hom
                (Category.comp_id _)).op (a p.val)) ∧
          Function.Bijective (fun p : localKummerMonoid χ ↦ Associates.mk
            (N.toEtalePrelogStructure.germ
              (x ≫ Spec.map (CommRingCat.ofHom (localKummerInvariantRing σ).subtype))
              (localKummerTop (localKummerInvariantRing σ))
              (Over.homMk
                (x ≫ Spec.map (CommRingCat.ofHom (localKummerInvariantRing σ).subtype)))
              (c p)))) ∧
        ∃ e : (localKummerInvariantRing σ ⧸ localKummerStratumIdeal b) ≃+*
          (A ⧸ localKummerStratumIdeal (localKummerRingChart M a)),
          ∀ r : localKummerInvariantRing σ,
            e (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r.val := by
  sorry

/-- The chart of the local quotient is represented on a pointed étale
neighbourhood of an original finite quotient. The maps `σ` and `τ` are the
canonical stabilizer maps on ring and log stalks: their equations prescribe
their value on every pointed-neighbourhood germ. The final equation says that
the target chart pulls back to the specified chart `a` on the strict local
source, including its unit factors, rather than merely having the same characteristic.

Source: ILO VI Proposition 3.5(b), proof 3.7(b), diagrams (3.b)--(3.c), pp.74--76
(blueprint: lem-per-very-tame-local-kummer-quotient).

Proof:
1. Apply lem-per-finite-quotient-strict-local-invariants to identify the strict
local quotient ring with the stabilizer invariants and the target log stalk
with the invariant source log stalk, respecting structural maps and units.
2. Apply the local quotient assertion above to the specified sharp chart and
pairing. Its common kernel is L and its sharp fs chart monoid is P = L ∩ Q.
3. Apply lem-per-tame-diagonal-standard-closed-immersion to the original finite
quotient. All its assumptions are the displayed finite-quotient, stabilizer,
diagonal-chart, invertible-order, and trivial-stratum assumptions. Its target
chart assertion gives a pointed étale quotient neighbourhood and a chart with
the specified invariant germs. This is an assertion on all geometric stalks
of that neighbourhood, not only the distinguished one.
4. The invariant-stalk calculation, including the reduction of possible unit
twists, identifies P with the closed characteristic. The canonical pullback
of a target section is the germ of `d.pullbackMap` at the displayed fibre-product
point, so the equality in the conclusion is precisely the prescribed descent.
-/
theorem veryTame_local_kummer_quotient_etale_neighbourhood
    (X : FineSaturatedLogScheme.{u}) (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (G : Type w) [Group G] [Finite G] (action : FSLogGroupAction G X)
    (f : X.scheme ⟶ Y) (hf : IsAdmissibleFiniteSchemeQuotient action.baseAction f)
    (N : EtaleLogStructure Y) (d : FSLogGroupAction.InvariantDirectImage action f N)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme)
    (H : Subgroup G)
    (hH : ∀ g : G, g ∈ H ↔ x ≫ (action.baseAction g).hom = x)
    (σ : H → strictLocalRing X.scheme x →+* strictLocalRing X.scheme x)
    (τ : H → X.logStructure.toEtalePrelogStructure.stalk x →*
      X.logStructure.toEtalePrelogStructure.stalk x)
    (hσ : ∀ (h : H) (U V : X.scheme.Etale)
      (p : (Scheme.pointSmallEtale x).fiber.obj U)
      (q : (Scheme.pointSmallEtale x).fiber.obj V) (k : V.left ⟶ U.left)
      (_hk : k ≫ U.hom = V.hom ≫ (action.logMap h.val).base),
      q.left ≫ k = p.left → ∀ r : Γ(U.left, ⊤),
        σ h (strictLocalGerm X.scheme x U p r) =
          strictLocalGerm X.scheme x V q (k.appTop r))
    (hτ : ∀ (h : H) (U V : X.scheme.Etale)
      (p : (Scheme.pointSmallEtale x).fiber.obj U)
      (q : (Scheme.pointSmallEtale x).fiber.obj V) (k : V.left ⟶ U.left)
      (hk : k ≫ U.hom = V.hom ≫ (action.logMap h.val).base),
      q.left ≫ k = p.left → ∀ s : X.logStructure.monoidSheaf.obj.obj (op U),
        τ h (X.logStructure.toEtalePrelogStructure.germ x U p s) =
          X.logStructure.toEtalePrelogStructure.germ x V q
            ((action.logMap h.val).sectionMap U V k hk s))
    (hn : IsUnit (Nat.card H : strictLocalRing X.scheme x))
    (ζ : strictLocalRing X.scheme x) (hζ : IsPrimitiveRoot ζ (Nat.card H))
    (hζfixed : ∀ h : H, σ h ζ = ζ)
    (Q : Type u) [CommMonoid Q] (hQ : IsFineSaturatedMonoid Q)
    (hsharp : ∀ q : Q, IsUnit q → q = 1)
    (a : Q →* X.logStructure.toEtalePrelogStructure.stalk x)
    (ha : X.logStructure.IsStalkChart x a)
    (hchar : Function.Bijective (fun q : Q ↦ Associates.mk (a q)))
    (χ : TensorProduct ℤ (Additive (Abelianization H))
      (Additive (Algebra.GrothendieckGroup Q)) →+
        Additive (rootsOfUnity (Nat.card H) (strictLocalRing X.scheme x)))
    (heigen : ∀ (h : H) (q : Q), τ h (a q) =
      X.logStructure.unitsIn x
        (localKummerCharacter χ h (Algebra.GrothendieckGroup.of q)).val * a q)
    (hstratum : ∀ (h : H) (r : strictLocalRing X.scheme x), σ h r - r ∈
      localKummerStratumIdeal ((X.logStructure.toEtalePrelogStructure.stalkAlpha x).comp a))
    (hfinite : Module.Finite (localKummerInvariantRing σ) (strictLocalRing X.scheme x)) :
    ∃ (W : Y.Etale) (w : (Scheme.pointSmallEtale (x ≫ f)).fiber.obj W)
      (b : localKummerMonoid χ →* N.monoidSheaf.obj.obj (op W)),
      N.IsChart W b ∧
      Function.Bijective (fun p : localKummerMonoid χ ↦ Associates.mk
        (N.toEtalePrelogStructure.germ (x ≫ f) W w (b p))) ∧
      ∀ p : localKummerMonoid χ,
        X.logStructure.toEtalePrelogStructure.germ x (logInvariantTest f W)
          (Over.homMk (pullback.lift w.left x (Over.w w)) (by simp))
          (d.pullbackMap W (b p)) = a p.val := by
  sorry

end AlgebraicGeometry
