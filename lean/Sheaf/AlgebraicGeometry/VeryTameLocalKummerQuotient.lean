/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.Index

/-!
# The invariant chart of a diagonal tame local action

Source: ILO, Exposé VI, 3.4, Proposition 3.5(b), proof 3.7(b) and the beginning
of 3.7(c), printed pp. 74--76 (blueprint: lem-per-very-tame-local-kummer-quotient).

Multiplicative notation is used for the chart monoids: `1` denotes their zero.
The character pairing is curried; a homomorphism from `H` to an abelian group
factors uniquely through its abelianization, giving the stated tensor pairing.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.VeryTameLocalKummer

/-- The prescribed fs log structure on the affine spectrum.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
noncomputable def affineLogScheme (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : EtaleLogStructure (Spec (.of A))) (hM : M.IsFineSaturated) :
    FineSaturatedLogScheme.{u} :=
  ⟨Spec (.of A), inferInstance, M, hM⟩

/-- The fixed ring, using the existing equalizer subrings.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def fixedRing {A : Type u} [CommRing A] {H : Type v} (σ : H → A ≃+* A) : Subring A :=
  ⨅ h : H, RingHom.eqLocus (σ h).toRingHom (RingHom.id A)

/-- The invariant lattice is the kernel of the given character pairing.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
noncomputable def lattice {A Q : Type u} [CommRing A] [CommMonoid Q] {H : Type v} [Group H]
    (χ : Algebra.GrothendieckGroup Q →* (H →* rootsOfUnity (Nat.card H) A)) :
    Subgroup (Algebra.GrothendieckGroup Q) := χ.ker

/-- The monoid `P = L ∩ Q`, taken using the canonical group-completion map.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
noncomputable def invariantMonoid {A Q : Type u} [CommRing A] [CommMonoid Q] {H : Type v} [Group H]
    (χ : Algebra.GrothendieckGroup Q →* (H →* rootsOfUnity (Nat.card H) A)) :
    Submonoid Q :=
  (lattice χ).toSubmonoid.comap Algebra.GrothendieckGroup.of

/-- The structural image of a global chart, in the original affine coordinate ring.
Source: ILO VI 3.7(b) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
noncomputable def chartRingMap {A Q : Type u} [CommRing A] [CommMonoid Q]
    (M : EtaleLogStructure (Spec (.of A)))
    (a : Q →* M.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))) : Q →* A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom.toMonoidHom.comp
    ((M.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))).hom.comp a)

/-- The ideal of the closed logarithmic stratum of a sharp chart.
Source: ILO VI 3.7(b)--(c) (blueprint: lem-per-very-tame-local-kummer-quotient). -/
def chartIdeal {A Q : Type u} [CommRing A] [CommMonoid Q] (a : Q →* A) : Ideal A :=
  Ideal.span {x | ∃ q : Q, q ≠ 1 ∧ a q = x}

/-- Exactly the specified diagonal strictly local data. The ring automorphisms `σ` are
pinned to pullback by the given log action; the eigenidentity is in log sections and
includes its unit factor, rather than merely its structural image in the ring.
Source: ILO VI 3.4 and 3.7(b)
(blueprint: lem-per-very-tame-local-kummer-quotient). -/
structure Data (A Q : Type u) [CommRing A] [IsNoetherianRing A]
    [IsStrictlyHenselianLocalRing A] [CommMonoid Q] (H : Type v) [Group H] [Finite H]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] where
  logStructure : EtaleLogStructure (Spec (.of A))
  fs : logStructure.IsFineSaturated
  action : FSLogGroupAction H (affineLogScheme A logStructure fs)
  a : Q →* logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A)))))
  chart : logStructure.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of A)))) a
  fineSaturated : IsFineSaturatedMonoid Q
  sharp : ∀ q : Q, IsUnit q → q = 1
  point : Spec (.of Ω) ⟶ Spec (.of A)
  closed : IsClosed ({point default} : Set (Spec (.of A)))
  characteristic : Function.Bijective (fun q : Q ↦ Associates.mk
    (logStructure.toEtalePrelogStructure.germ point (Scheme.Etale.mk (𝟙 _))
      (Over.homMk point) (a q)))
  σ : H → A ≃+* A
  ringAction : ∀ (h : H) (r : A), σ h r =
    (Scheme.ΓSpecIso (.of A)).hom
      ((action.logMap h).base.appTop ((Scheme.ΓSpecIso (.of A)).inv r))
  residue : ∀ (h : H) (r : A), IsLocalRing.residue A (σ h r) = IsLocalRing.residue A r
  orderUnit : IsUnit (Nat.card H : A)
  root : A
  primitive : IsPrimitiveRoot root (Nat.card H)
  rootFixed : ∀ h : H, σ h root = root
  χ : Algebra.GrothendieckGroup Q →* (H →* rootsOfUnity (Nat.card H) A)
  diagonal : ∀ (h : H) (q : Q),
    ∃ z : (logStructure.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))))ˣ,
      logStructure.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of A))))) z.val =
        (Scheme.ΓSpecIso (.of A)).inv
          (((χ (Algebra.GrothendieckGroup.of q) h : Aˣ) : A)) ∧
      (action.logMap h).sectionMap (Scheme.Etale.mk (𝟙 _)) (Scheme.Etale.mk (𝟙 _))
        (action.logMap h).base
        (by exact (Category.comp_id _).trans (Category.id_comp _).symm) (a q) = z.val * a q
  stratum : ∀ (h : H) (r : A), σ h r - r ∈ chartIdeal (chartRingMap logStructure a)
  finite : Module.Finite (fixedRing σ) A

/-- The invariant lattice, its chart on the actual invariant log sheaf, and its stratum.
Source: ILO VI Proposition 3.5(b), proof 3.7(b), and opening of 3.7(c), pp. 74--76
(blueprint: lem-per-very-tame-local-kummer-quotient).

Proof plan:
1. Apply lem-per-tame-admissible-scheme-quotient to Spec A and use
lem-per-finite-quotient-strict-local-invariants to identify the quotient strict ring
with B and the invariant log stalk with the H-fixed stalk, including its units.
2. Retain the given sharp chart and character pairing; the closed log stalk is
Q times A-units, and its nonunit ideal is exactly chartIdeal a.
3. The character kernel L has finite index and contains all n-th powers. Generate
P by n-th powers of generators of Q and the finitely many residues modulo nQ
that lie in L. Saturation is checked in P's group completion, sharpness in Q.
For l = u/v in L, both v^n and l*v^n belong to P, so P's group image is L.
4. Write a fixed log element as z*a(q). Reducing h(z)*chi(q,h)=z modulo the
maximal ideal shows chi(q,h)=1: reduction on n-th roots of unity is injective,
since (zeta-1)*(1+...+zeta^(n-1))=0 and the second factor reduces to the unit n.
Thus fixed log elements are exactly P times B-units, including all unit twists.
5. Apply lem-per-tame-diagonal-standard-closed-immersion: its surjective map
B tensor Z[Q] over Z[P] to A gives finite B-linear monomial expressions.
6. Its target-chart assertion identifies the associated P-chart with the invariant
log sheaf on an actual quotient neighbourhood, not just at the closed stalk.
7. The Reynolds operator is the identity modulo I, giving B -> A/I surjective.
8. Expand coefficients in I into B-monomials before averaging. Nontrivial character
monomials average to zero: chi(h)-1 is a unit by step 4. The remaining monomials
are precisely the nonidentity elements of P. Hence B intersect I = J, and the
canonical B/J -> A/I is an isomorphism. No regularity or dimension formula is used.
-/
theorem invariant_chart_and_stratum
    {A Q : Type u} [CommRing A] [IsNoetherianRing A] [IsStrictlyHenselianLocalRing A]
    [CommMonoid Q] {H : Type v} [Group H] [Finite H]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (d : Data A Q H Ω) :
    IsFineSaturatedMonoid (invariantMonoid d.χ) ∧
    (∀ p : invariantMonoid d.χ, IsUnit p → p = 1) ∧
    MonoidHom.mrange (Algebra.GrothendieckGroup.lift
      (Algebra.GrothendieckGroup.of.comp (invariantMonoid d.χ).subtype)) =
        (lattice d.χ).toSubmonoid ∧
    (lattice d.χ).FiniteIndex ∧
    (∀ g : Algebra.GrothendieckGroup Q, g ^ Nat.card H ∈ lattice d.χ) ∧
    ∃ b : invariantMonoid d.χ →* fixedRing d.σ,
      (fixedRing d.σ).subtype.toMonoidHom.comp b =
        (chartRingMap d.logStructure d.a).comp (invariantMonoid d.χ).subtype ∧
      (∃ e : (fixedRing d.σ ⧸ chartIdeal b) ≃+*
          (A ⧸ chartIdeal (chartRingMap d.logStructure d.a)),
        ∀ r : fixedRing d.σ, e (Ideal.Quotient.mk (chartIdeal b) r) =
          Ideal.Quotient.mk (chartIdeal (chartRingMap d.logStructure d.a)) (r : A)) ∧
      ∃ (N : EtaleLogStructure (Spec (.of (fixedRing d.σ))))
        (i : d.action.InvariantDirectImage
          (Spec.map (CommRingCat.ofHom (fixedRing d.σ).subtype)) N)
        (c : invariantMonoid d.χ →*
          N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 _)))),
        N.IsChart (Scheme.Etale.mk (𝟙 _)) c ∧ chartRingMap N c = b ∧
        (∀ (j : Scheme.Etale.mk (𝟙 (Spec (.of A))) ⟶
            logInvariantTest (Spec.map (CommRingCat.ofHom (fixedRing d.σ).subtype))
              (Scheme.Etale.mk (𝟙 _))),
          j.left ≫ pullback.snd (𝟙 _) (Spec.map
            (CommRingCat.ofHom (fixedRing d.σ).subtype)) = 𝟙 _ →
          (d.logStructure.monoidSheaf.obj.map j.op).hom.comp
            ((i.pullbackMap (Scheme.Etale.mk (𝟙 _))).comp c) =
              d.a.comp (invariantMonoid d.χ).subtype) ∧
        Function.Bijective (fun p : invariantMonoid d.χ ↦ Associates.mk
          (N.toEtalePrelogStructure.germ
            (d.point ≫ Spec.map (CommRingCat.ofHom (fixedRing d.σ).subtype))
            (Scheme.Etale.mk (𝟙 _))
            (Over.homMk (d.point ≫ Spec.map
              (CommRingCat.ofHom (fixedRing d.σ).subtype))) (c p))) := by
  sorry

/-- The same diagonal data at an original geometric point before strict localization.
The actions on the ring and log stalk are specified on every pointed relative test
by their actual pullbacks. Thus neither action can be replaced by an unrelated map.
The local-ring structure is the intrinsic one on the strict local ring.
Source: ILO VI 3.5(b), 3.7(b)
(blueprint: lem-per-very-tame-local-kummer-quotient). -/
structure StalkData {X : FineSaturatedLogScheme.{u}} {H : Type v} [Group H] [Finite H]
    (action : FSLogGroupAction H X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme) (Q : Type u) [CommMonoid Q] where
  stabilizer : ∀ h : H, t ≫ (action.logMap h).base = t
  localRing : IsLocalRing (strictLocalRing X.scheme t)
  a : Q →* X.logStructure.toEtalePrelogStructure.stalk t
  chart : X.logStructure.IsStalkChart t a
  fineSaturated : IsFineSaturatedMonoid Q
  sharp : ∀ q : Q, IsUnit q → q = 1
  characteristic : Function.Bijective (fun q : Q ↦ Associates.mk (a q))
  σ : H → strictLocalRing X.scheme t ≃+* strictLocalRing X.scheme t
  τ : H → X.logStructure.toEtalePrelogStructure.stalk t ≃*
    X.logStructure.toEtalePrelogStructure.stalk t
  pullback : ∀ (h : H) (W V : X.scheme.Etale) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ (action.logMap h).base)
    (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (z : (Scheme.pointSmallEtale t).fiber.obj V), z.left ≫ k = w.left →
    (∀ r : Γ(W.left, ⊤),
      σ h (strictLocalGerm X.scheme t W w r) =
        strictLocalGerm X.scheme t V z (k.appTop r)) ∧
    ∀ m : X.logStructure.monoidSheaf.obj.obj (op W),
      τ h (X.logStructure.toEtalePrelogStructure.germ t W w m) =
        X.logStructure.toEtalePrelogStructure.germ t V z
          ((action.logMap h).sectionMap W V k hk m)
  residue : ∀ (h : H) (r : strictLocalRing X.scheme t),
    @IsLocalRing.residue _ _ localRing (σ h r) = @IsLocalRing.residue _ _ localRing r
  orderUnit : IsUnit (Nat.card H : strictLocalRing X.scheme t)
  root : strictLocalRing X.scheme t
  primitive : IsPrimitiveRoot root (Nat.card H)
  rootFixed : ∀ h : H, σ h root = root
  χ : Algebra.GrothendieckGroup Q →*
    (H →* rootsOfUnity (Nat.card H) (strictLocalRing X.scheme t))
  diagonal : ∀ (h : H) (q : Q), τ h (a q) =
    X.logStructure.unitsIn t (χ (Algebra.GrothendieckGroup.of q) h :
      (strictLocalRing X.scheme t)ˣ) * a q
  stratum : ∀ (h : H) (r : strictLocalRing X.scheme t), σ h r - r ∈
    chartIdeal ((X.logStructure.toEtalePrelogStructure.stalkAlpha t).comp a)
  finite : Module.Finite (fixedRing σ) (strictLocalRing X.scheme t)

/-- The invariant chart spreads to a pointed étale neighbourhood of the original
quotient point, preserving its specified diagonal-chart germ after pullback to X.
The neighbourhood carries the actual invariant log sheaf, without a prior fs assumption.
Source: ILO VI Proposition 3.5(b), proof 3.7(b), diagrams (3.b)--(3.c), pp. 74--76
(blueprint: lem-per-very-tame-local-kummer-quotient).

Proof plan: apply the strict-local reduction and invariant-stalk identification of
lem-per-finite-quotient-strict-local-invariants. The preceding lattice and unit-twist
argument identifies the invariant stalk with P times the fixed units. Apply the
pointed source-and-target neighbourhood assertion of
lem-per-tame-diagonal-standard-closed-immersion: its target chart is a chart of the
actual invariant direct image, and its comparison restricts to the specified a on P.
Its target neighbourhood is the required W, and the invariant-stalk calculation
identifies P with the closed characteristic. In particular this does not infer that
a quotient of an arbitrary chosen source étale neighbourhood is itself étale.
-/
theorem invariant_chart_on_pointed_etale_neighbourhood
    {X : FineSaturatedLogScheme.{u}} {G : Type v} [Group G] [Finite G]
    (action : FSLogGroupAction G X) {Y : Scheme.{u}} (f : X.scheme ⟶ Y)
    (_hquot : IsAdmissibleFiniteSchemeQuotient action.baseAction f)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
    (H : Subgroup G) (inertia : FSLogGroupAction H X)
    (_hrestriction : ∀ h : H, inertia.logMap h = action.logMap h.val)
    (_hstabilizer : ∀ g : G, t ≫ (action.logMap g).base = t ↔ g ∈ H)
    {Q : Type u} [CommMonoid Q] (d : StalkData inertia t Q) :
    ∃ (N : EtaleLogStructure Y) (i : action.InvariantDirectImage f N)
      (W : Y.Etale) (w : (Scheme.pointSmallEtale (t ≫ f)).fiber.obj W)
      (b : invariantMonoid d.χ →* N.monoidSheaf.obj.obj (op W)),
      N.IsChart W b ∧
      Function.Bijective (fun p : invariantMonoid d.χ ↦ Associates.mk
        (N.toEtalePrelogStructure.germ (t ≫ f) W w (b p))) ∧
      ∀ (z : (Scheme.pointSmallEtale t).fiber.obj (logInvariantTest f W)),
        z.left ≫ pullback.fst W.hom f = w.left →
        ∀ p : invariantMonoid d.χ,
          X.logStructure.toEtalePrelogStructure.germ t (logInvariantTest f W) z
            (i.pullbackMap W (b p)) = d.a p.val := by
  sorry

end AlgebraicGeometry.VeryTameLocalKummer
