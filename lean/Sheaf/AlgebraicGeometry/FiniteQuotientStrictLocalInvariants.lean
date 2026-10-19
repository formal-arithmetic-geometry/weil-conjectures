/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.FSLogGroupAction
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.FinitePushforwardSetStalk
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.AlgebraicGeometry.StrictHenselization
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.FiniteInjectiveNoetherianDescent
import Sheaf.TraceFormula.FiniteBaseStrictLocalization
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

/-!
# Strict local invariants of a finite scheme quotient

Source: ILO, Exposé VI, paragraph after Proposition 3.5 and proof 3.7(b), pp.74--75;
Stacks Tags 04GH and 0BRH (blueprint: lem-per-finite-quotient-strict-local-invariants).

The invariant direct image is characterized on all étale sections. Its target is a
prelog sheaf, without an fs hypothesis. All stalk maps are characterized on germs;
the fixed-point predicates use the graphs of the given action on those same germs.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteQuotientStrictLocal

/-- Relative-test presentation of a prelog pullback map, with naturality in both
étale test objects. Source: ILO VI 1.1 and the paragraph after 3.5
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
structure PullbackData {X Y : Scheme.{u}} (M : EtalePrelogStructure X)
    (N : EtalePrelogStructure Y) (q : X ⟶ Y) where
  sectionMap : ∀ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (_hk : k ≫ W.hom = V.hom ≫ q),
    N.monoidSheaf.obj.obj (op W) →* M.monoidSheaf.obj.obj (op V)
  naturality : ∀ (W₁ W₂ : Y.Etale) (V₁ V₂ : X.Etale)
    (a : W₁ ⟶ W₂) (c : V₁ ⟶ V₂) (k₁ : V₁.left ⟶ W₁.left)
    (k₂ : V₂.left ⟶ W₂.left)
    (h₁ : k₁ ≫ W₁.hom = V₁.hom ≫ q) (h₂ : k₂ ≫ W₂.hom = V₂.hom ≫ q),
    c.left ≫ k₂ = k₁ ≫ a.left →
      (M.monoidSheaf.obj.map c.op).hom.comp (sectionMap W₂ V₂ k₂ h₂) =
        (sectionMap W₁ V₁ k₁ h₁).comp (N.monoidSheaf.obj.map a.op).hom
  compatibility : ∀ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ q) (s : N.monoidSheaf.obj.obj (op W)),
    M.alpha.app (op V) (sectionMap W V k hk s) = k.appTop (N.alpha.app (op W) s)

/-- Forget only the fs packaging of the source and target of a given log morphism.
Source: ILO VI 1.1 (blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def ofLogHom {X Y : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X Y) :
    PullbackData X.logStructure.toEtalePrelogStructure
      Y.logStructure.toEtalePrelogStructure f.base where
  sectionMap := f.sectionMap
  naturality := f.naturality
  compatibility := f.compatibility

/-- Graph of pullback on log germs, with source and target geometric points explicit.
Source: ILO VI 1.2 and 3.7(b)
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def LogGermImage {X Y : Scheme.{u}} {M : EtalePrelogStructure X}
    {N : EtalePrelogStructure Y} {q : X ⟶ Y} (d : PullbackData M N q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (m : N.stalk y) (n : M.stalk x) : Prop :=
  ∃ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ q)
    (w : (Scheme.pointSmallEtale y).fiber.obj W)
    (z : (Scheme.pointSmallEtale x).fiber.obj V),
    z.left ≫ k = w.left ∧ ∃ s : N.monoidSheaf.obj.obj (op W),
      N.germ y W w s = m ∧ M.germ x V z (d.sectionMap W V k hk s) = n

/-- Graph of the canonical ring pullback on germs. Source: ILO VI 3.7(b)
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def RingGermImage {X Y : Scheme.{u}} (q : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (b : strictLocalRing Y y) (a : strictLocalRing X x) : Prop :=
  ∃ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (_hk : k ≫ W.hom = V.hom ≫ q)
    (w : (Scheme.pointSmallEtale y).fiber.obj W)
    (z : (Scheme.pointSmallEtale x).fiber.obj V),
    z.left ≫ k = w.left ∧ ∃ s : Γ(W.left, ⊤),
      strictLocalGerm Y y W w s = b ∧ strictLocalGerm X x V z (k.appTop s) = a

/-- Canonical ring pullback specified on every pointed relative test diagram.
Source: ILO VI 3.7(b) (blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def IsRingPullback {X Y : Scheme.{u}} (q : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (r : strictLocalRing Y (x ≫ q) →+* strictLocalRing X x) : Prop :=
  ∀ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (_hk : k ≫ W.hom = V.hom ≫ q)
    (w : (Scheme.pointSmallEtale (x ≫ q)).fiber.obj W)
    (z : (Scheme.pointSmallEtale x).fiber.obj V), z.left ≫ k = w.left →
    ∀ s : Γ(W.left, ⊤), r (strictLocalGerm Y (x ≫ q) W w s) =
      strictLocalGerm X x V z (k.appTop s)

/-- Canonical log pullback specified on every pointed relative test diagram.
Source: ILO VI 3.7(b) (blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def IsLogPullback {X Y : Scheme.{u}} {M : EtalePrelogStructure X}
    {N : EtalePrelogStructure Y} {q : X ⟶ Y} (d : PullbackData M N q)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (e : N.stalk (x ≫ q) →* M.stalk x) : Prop :=
  ∀ (W : Y.Etale) (V : X.Etale) (k : V.left ⟶ W.left)
    (hk : k ≫ W.hom = V.hom ≫ q)
    (w : (Scheme.pointSmallEtale (x ≫ q)).fiber.obj W)
    (z : (Scheme.pointSmallEtale x).fiber.obj V), z.left ≫ k = w.left →
    ∀ s : N.monoidSheaf.obj.obj (op W), e (N.germ (x ≫ q) W w s) =
      M.germ x V z (d.sectionMap W V k hk s)

/-- Fixed log germs for the geometric stabilizer, not the ordinary-point stabilizer.
Source: ILO VI 3.3 and 3.7(b)
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def IsFixedLog {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) (m : X.logStructure.toEtalePrelogStructure.stalk x) :
    Prop :=
  ∀ g : G, x ≫ (a.baseAction g).hom = x → LogGermImage (ofLogHom (a.logMap g)) x x m m

/-- Fixed ring germs for exactly the same geometric stabilizer.
Source: ILO VI 3.3 and 3.7(b)
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def IsFixedRing {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X.scheme) (b : strictLocalRing X.scheme x) : Prop :=
  ∀ g : G, x ≫ (a.baseAction g).hom = x → RingGermImage (a.logMap g).base x x b b

/-- Invariant sections of the actual pulled-back étale test object. Quantified lifts
are unique by the two pullback projections. Source: ILO VI, paragraph after 3.5
(blueprint: lem-per-finite-quotient-strict-local-invariants). -/
def IsInvariantSection {G : Type v} [Group G] {X : FineSaturatedLogScheme.{u}}
    (a : FSLogGroupAction G X) {Y : Scheme.{u}} (q : X.scheme ⟶ Y) (W : Y.Etale)
    (s : X.logStructure.monoidSheaf.obj.obj (op (q.Etale.obj W))) : Prop :=
  ∀ (g : G) (k : (q.Etale.obj W).left ⟶ (q.Etale.obj W).left)
    (hk : k ≫ (q.Etale.obj W).hom = (q.Etale.obj W).hom ≫ (a.logMap g).base),
    k ≫ pullback.fst W.hom q = pullback.fst W.hom q →
      (a.logMap g).sectionMap (q.Etale.obj W) (q.Etale.obj W) k hk s = s

/-- The strict local description of a finite group quotient, including its invariant
log sheaf, structural maps and units. The existential prelog sheaf is characterized
on every étale test object by the injective inclusion with precisely invariant image;
this specifies `(q_* M)^G` as a sheaf with its prescribed structural map.

Source: ILO VI, paragraph after Proposition 3.5 and 3.7(b), pp.74--75; Stacks
04GH and 0BRH (blueprint: lem-per-finite-quotient-strict-local-invariants).

Proof:
1. On an affine quotient open Spec D its inverse image is Spec R, with R finite
   over D and D = R^G. R is Noetherian because X is Noetherian. Eakin--Nagata
   descent makes D Noetherian; hence Y is locally Noetherian.
2. Surjectivity descends quasi-compactness from X to Y, so Y is Noetherian.
   Empty X forces empty Y; assertions about geometric points are then vacuous.
3. At a geometric y, flat strict-local base change gives C = B tensor_D R,
   canonically a finite product of the strict local rings at the geometric lifts.
   Each factor is a finite B-algebra, and the decomposition is G-equivariant.
4. Tensor the exact difference-kernel sequence 0 -> D -> R -> direct_sum_G R
   with flat B. Its kernel identifies B with C^G, without division by |G|.
5. The lifts form one nonempty orbit: an empty set would make C zero, and two orbits
   would give a nontrivial invariant idempotent in the nonzero local ring B.
6. Evaluation at x identifies C^G with A^H. The inverse sends an H-fixed a
   to the tuple with component g(a) at gx; H-invariance makes it well-defined.
7. Invariant sections form a sheaf, with structural map into the invariant ring
   sheaf O_Y. Stalks commute with finite limits, and finite pushforward stalks
   are products over the geometric lifts. The formulas preserve multiplication.
8. The same evaluation and tuple inverse identify the log stalk with M_x^H.
   Structural maps commute with evaluation; all canonical maps have the germ
   characterizations written below.
9. Inverses of invariant units are invariant. The equivariant log unit axiom
   identifies log units with ring units, proving both unit restrictions. -/
theorem finiteQuotient_strictLocal_invariants
    (X : FineSaturatedLogScheme.{u}) [IsNoetherian X.scheme]
    (Y : Scheme.{u}) (G : Type v) [Group G] [Finite G] (a : FSLogGroupAction G X)
    (q : X.scheme ⟶ Y) [IsFinite q] [Surjective q]
    (hinvariant : ∀ g : G, (a.baseAction g).hom ≫ q = q)
    (htopology : Topology.IsQuotientMap q)
    (horbits : ∀ x z : X.scheme, q x = q z ↔ ∃ g : G, (a.baseAction g).hom x = z)
    (hsheaf : ∀ U : Y.Opens, Function.Injective (q.app U).hom ∧
      ∀ s : Γ(X.scheme, q ⁻¹ᵁ U), s ∈ Set.range (q.app U).hom ↔
        ∀ (g : G) (V : X.scheme.Opens) (hV : V ≤ q ⁻¹ᵁ U)
          (hVg : V ≤ (a.baseAction g).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
          ((a.baseAction g).hom.appLE (q ⁻¹ᵁ U) V hVg).hom s =
            (X.scheme.presheaf.map (homOfLE hV).op).hom s) :
    IsNoetherian Y ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      ∃ x : Spec (.of Ω) ⟶ X.scheme, x ≫ q = y) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x z : Spec (.of Ω) ⟶ X.scheme),
      x ≫ q = z ≫ q ↔ ∃ g : G, x ≫ (a.baseAction g).hom = z) ∧
    ∃ (N : EtalePrelogStructure Y) (d : PullbackData X.logStructure.toEtalePrelogStructure N q),
      (∀ W : Y.Etale,
        Function.Injective (d.sectionMap W (q.Etale.obj W)
          (pullback.fst W.hom q) pullback.condition) ∧
        ∀ s : X.logStructure.monoidSheaf.obj.obj (op (q.Etale.obj W)),
          s ∈ Set.range (d.sectionMap W (q.Etale.obj W)
            (pullback.fst W.hom q) pullback.condition) ↔ IsInvariantSection a q W s) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.scheme),
        ∃ (r : strictLocalRing Y (x ≫ q) →+* strictLocalRing X.scheme x)
          (e : N.stalk (x ≫ q) →* X.logStructure.toEtalePrelogStructure.stalk x),
          IsRingPullback q x r ∧ IsLogPullback d x e ∧
          Function.Injective r ∧ r.Finite ∧
          (∀ b : strictLocalRing X.scheme x, b ∈ Set.range r ↔ IsFixedRing a x b) ∧
          Function.Injective e ∧
          (∀ m : X.logStructure.toEtalePrelogStructure.stalk x,
            m ∈ Set.range e ↔ IsFixedLog a x m) ∧
          (∀ m : N.stalk (x ≫ q),
            X.logStructure.toEtalePrelogStructure.stalkAlpha x (e m) =
              r (N.stalkAlpha (x ≫ q) m)) ∧
          (∀ b : strictLocalRing Y (x ≫ q), IsUnit (r b) ↔ IsUnit b) ∧
          (∀ m : N.stalk (x ≫ q), IsUnit (e m) ↔ IsUnit m) ∧
          Function.Bijective (Units.map (N.stalkAlpha (x ≫ q))) := by
  sorry

end AlgebraicGeometry.FiniteQuotientStrictLocal
