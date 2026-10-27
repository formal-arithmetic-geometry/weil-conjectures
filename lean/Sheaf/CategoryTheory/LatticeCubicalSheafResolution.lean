/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Cubical translation resolution of internal condensed modules

Source: the current blueprint, direct-image stability proof, paragraph (3), and the
agent-written internalization in the DAG
(blueprint: lem-sfb-lattice-cubical-sheaf-resolution).

All maps are defined by finite integral columns and coproduct universal properties.
No preservation of infinite coproducts by sections is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Profinite.CondensedAction IntegralLatticeCubical
namespace Profinite.LatticeCubical
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

/-- Use the existing coproduct instance directly, avoiding a search through Grothendieck
structures. Source: DAG coproduct clause
(blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
instance (priority := 2000) coproducts : HasColimitsOfSize.{0, 0} (Modules R) :=
  InternalAbelianSheafModule.comparison_internalColimits
    (coherentTopology Profinite.{u}) R.X

/-- The chosen cell coproducts use the existing small-colimit data directly.
Source: DAG proof step 3 (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
instance (priority := 3000) cellCoproduct {B : Type} (F : B → Modules R) :
    HasCoproduct F :=
  (coproducts R).has_colimits_of_shape (Discrete B) |>.has_colimit (Discrete.functor F)

/-- Realization of a column-finite integral matrix in internal modules.
Source: DAG proof step 3 (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def matrix {B C : Type} (A : B → C →₀ ℤ) (Q : Modules R) :
    (∐ fun _ : B ↦ Q) ⟶ ∐ fun _ : C ↦ Q :=
  Limits.Sigma.desc fun b ↦ (A b).sum fun c n ↦ n • Limits.Sigma.ι (fun _ : C ↦ Q) c

/-- The cubical term, zero outside the rank range because the cell index is empty.
Source: DAG displayed coproduct (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def term (r : ℕ) (a : ℤ) (Q : Modules R) : Modules R :=
  ∐ fun _ : (Fin r → ℤ) × Directions r a ↦ Q

/-- Maps between coefficients act on each copy of the module.
Source: DAG naturality clause (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def termMap (r : ℕ) (a : ℤ) {Q Q' : Modules R} (f : Q ⟶ Q') :
    term R r a Q ⟶ term R r a Q' :=
  Limits.Sigma.desc fun c : (Fin r → ℤ) × Directions r a ↦
    f ≫ Limits.Sigma.ι (fun _ : (Fin r → ℤ) × Directions r a ↦ Q') c

/-- Realize an integral linear map using its finite columns on the standard free basis.
Source: DAG proof steps 3--5 (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def realize (r : ℕ) (a b : ℤ) (A : Chains r a →ₗ[ℤ] Chains r b) (Q : Modules R) :
    term R r a Q ⟶ term R r b Q :=
  matrix R (fun c ↦ A (Finsupp.single c 1)) Q

/-- The signed cubical boundary is the actual integral boundary with coefficients in Q.
Source: DAG displayed boundary (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def differential (r : ℕ) (a : ℤ) (Q : Modules R) :
    term R r a Q ⟶ term R r (a - 1) Q :=
  realize R r a (a - 1) (boundary r a) Q

/-- Incoming boundary with the canonical degree transport already used integrally.
Source: DAG contraction formula (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def incoming (r : ℕ) (a : ℤ) (Q : Modules R) :
    term R r (a + 1) Q ⟶ term R r a Q :=
  realize R r (a + 1) a (incomingBoundary r a) Q

/-- Augmentation is the identity on every vertex summand.
Source: DAG displayed augmentation (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def augmentationMap (r : ℕ) (Q : Modules R) : term R r 0 Q ⟶ Q :=
  Limits.Sigma.desc fun _ : (Fin r → ℤ) × Directions r 0 ↦ 𝟙 Q

/-- Section is the origin vertex injection; it uses no existence choice.
Source: DAG proof step 5 (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def sectionMapQ (r : ℕ) (Q : Modules R) : Q ⟶ term R r 0 Q :=
  Limits.Sigma.ι (fun _ : (Fin r → ℤ) × Directions r 0 ↦ Q) (0, ⟨∅, rfl⟩)

/-- Translation is the realized permutation of the lattice basis.
Source: DAG translation formula (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def translation (r : ℕ) (a : ℤ) (w : Fin r → ℤ) (Q : Modules R) :
    term R r a Q ⟶ term R r a Q :=
  realize R r a a (translate r a w) Q

/-- The internal/section equivalence induces the action equivalence without changing
any section; this is Mathlib's generic induced action equivalence, not new action data.
Source: DAG first paragraph (blueprint: lem-sfb-lattice-cubical-sheaf-resolution). -/
def sectionActions (r : ℕ) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) R.X).mapAction (Multiplicative (Fin r → ℤ))

/-- The action category and normalized invariants have the categorical properties
needed for the cubical resolution. Invariants are the actual limit on BD-diagrams.
Source: current blueprint paragraph (3), DAG proof steps 1--2
(blueprint: lem-sfb-lattice-cubical-sheaf-resolution).

Proof plan: apply the section-module equivalence pointwise. Kernels and cokernels
are the underlying ones with their uniquely induced actions, so the comparison is
exact and keeps sections. Use the discrete condensed-action comparison and
lem-sfb-condensed-action-injective-infrastructure for the Grothendieck property,
then lem-sp-grothendieck-enough-injectives. A map from a constant diagram is exactly
a cone, giving the invariant-inclusion transpose. Constant diagrams are exact
pointwise; the adjunction and lem-weil-pbc-right-adjoint-preserves-limits give
left exactness of invariants, and addition follows after composing with inclusion. -/
theorem categorical (r : ℕ) :
    IsGrothendieckAbelian.{u + 1} (Action (Modules R) (Multiplicative (Fin r → ℤ))) ∧
    EnoughInjectives (Action (Modules R) (Multiplicative (Fin r → ℤ))) ∧
    exactFunctor _ _ (sectionActions R r).functor ∧
    (∀ P : Action (Modules R) (Multiplicative (Fin r → ℤ)),
      ((sectionActions R r).functor.obj P).V.val.presheaf = P.V.X.obj) ∧
    (∀ (P P' : Action (Modules R) (Multiplicative (Fin r → ℤ))) (f : P ⟶ P'),
      Nonempty (CreatesLimit (parallelPair f 0)
        (Action.forget (Modules R) (Multiplicative (Fin r → ℤ)))) ∧
      Nonempty (CreatesColimit (parallelPair f 0)
        (Action.forget (Modules R) (Multiplicative (Fin r → ℤ))))) ∧
    exactFunctor _ _ (Functor.const (SingleObj (Multiplicative (Fin r → ℤ)))
      (C := Modules R)) ∧
    (lim (J := SingleObj (Multiplicative (Fin r → ℤ))) (C := Modules R)).Additive ∧
    PreservesFiniteLimits
      (lim (J := SingleObj (Multiplicative (Fin r → ℤ))) (C := Modules R)) ∧
    ∃ adj : Functor.const (SingleObj (Multiplicative (Fin r → ℤ))) (C := Modules R) ⊣
        lim (J := SingleObj (Multiplicative (Fin r → ℤ))) (C := Modules R),
      ∀ (Q : Modules R) (P : SingleObj (Multiplicative (Fin r → ℤ)) ⥤ Modules R)
        (f : Q ⟶ limit P),
        ((adj.homEquiv Q P).symm f).app PUnit.unit = f ≫ limit.π P PUnit.unit := by
  sorry

/-- The relative-tensor comparison is fixed by every coproduct injection and the
right unitor, and respects differential, augmentation, translation and coefficients.
Source: current blueprint paragraph (3), DAG proof steps 7--8
(blueprint: lem-sfb-lattice-cubical-sheaf-resolution).

Proof plan: the internal-module Hom adjunction of def-sfb-modobj-internal-hom makes
Q tensor - a left adjoint. Apply lem-weil-pbc-left-adjoint-preserves-colimits to the
cell coproduct, then the coproduct of right unitors. This gives the specified
injection formula. By lem-sfb-preserving-colimits-additive the functor respects
finite integer sums. Check boundary, augmentation and translation after each
coproduct injection; naturality follows from the same check. This uses the actual
relative tensor, via def-sfb-modobj-relative-tensor and the internal-section tensor
comparison lem-pe-internal-section-tensor-comparison, never pointwise tensor alone. -/
theorem tensorComparison (r : ℕ) :
    ∃ e : ∀ (Q : Modules R) (a : ℤ),
      Q ⊗ term R r a (𝟙_ (Modules R)) ≅ term R r a Q,
      (∀ (Q : Modules R) (a : ℤ) (c : (Fin r → ℤ) × Directions r a),
        (ρ_ Q).inv ≫ Q ◁ Limits.Sigma.ι
            (fun _ : (Fin r → ℤ) × Directions r a ↦ 𝟙_ (Modules R)) c ≫
          (e Q a).hom = Limits.Sigma.ι
            (fun _ : (Fin r → ℤ) × Directions r a ↦ Q) c) ∧
      (∀ (Q : Modules R) (a : ℤ),
        Q ◁ differential R r a (𝟙_ (Modules R)) ≫ (e Q (a - 1)).hom =
          (e Q a).hom ≫ differential R r a Q) ∧
      (∀ Q : Modules R,
        Q ◁ augmentationMap R r (𝟙_ (Modules R)) ≫ (ρ_ Q).hom =
          (e Q 0).hom ≫ augmentationMap R r Q) ∧
      (∀ (Q : Modules R) (a : ℤ) (w : Fin r → ℤ),
        Q ◁ translation R r a w (𝟙_ (Modules R)) ≫ (e Q a).hom =
          (e Q a).hom ≫ translation R r a w Q) ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q') (a : ℤ),
        f ▷ term R r a (𝟙_ (Modules R)) ≫ (e Q' a).hom =
          (e Q a).hom ≫ termMap R r a f) := by
  sorry

/-- Internal cubical boundaries, translations and contraction, natural in coefficients.
The integral homotopy is existential because the source specifies existence, rather
than a distinguished contraction. Its realization is fixed on every finite column.
Source: current blueprint paragraph (3), DAG proof steps 3--6 and 8
(blueprint: lem-sfb-lattice-cubical-sheaf-resolution).

Proof plan: realize finite columns by the coproduct universal property. Finite sums
and composition commute with realization, so all integral identities of
lem-sfb-integral-lattice-cubical-contraction remain true. Translations are permutation
matrices, yielding the action and equivariance. Realize the same integral homotopy
for every Q; maps between coefficients commute with each integer multiple of identity.
For a cycle z, the contraction identity gives d h z = z, splitting the map onto cycles;
the augmentation is split by the origin injection. Empty direction sets give zero
terms, including the negative degrees and those above r. At rank zero the single
vertex coproduct identifies canonically with Q, and the augmentation and section
become identity. No equivariance of the homotopy or section is claimed. -/
theorem resolution (r : ℕ) :
    ∃ h : (a : ℤ) → Chains r a →ₗ[ℤ] Chains r (a + 1),
      (∀ (a : ℤ) (_ : 0 ≤ a) (x : Chains r a),
        incomingBoundary r a (h a x) +
          LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
            (h (a - 1) (boundary r a x)) = x - originProjection r a x) ∧
      (∀ (Q : Modules R) (a : ℤ),
        differential R r a Q ≫ differential R r (a - 1) Q = 0) ∧
      (∀ Q : Modules R, differential R r 1 Q ≫ augmentationMap R r Q = 0) ∧
      (∀ (Q : Modules R) (a : ℤ), a < 0 ∨ (r : ℤ) < a → IsZero (term R r a Q)) ∧
      (∀ (Q : Modules R) (a : ℤ),
        ∃ ρ : Multiplicative (Fin r → ℤ) →* End (term R r a Q),
          ∀ w : Fin r → ℤ, ρ (Multiplicative.ofAdd w) = translation R r a w Q) ∧
      (∀ (Q : Modules R) (a : ℤ) (w : Fin r → ℤ),
        translation R r a w Q ≫ differential R r a Q =
          differential R r a Q ≫ translation R r (a - 1) w Q) ∧
      (∀ (Q : Modules R) (w : Fin r → ℤ),
        translation R r 0 w Q ≫ augmentationMap R r Q = augmentationMap R r Q) ∧
      (∀ Q : Modules R, sectionMapQ R r Q ≫ augmentationMap R r Q = 𝟙 Q) ∧
      (∀ (Q : Modules R) (a : ℤ), 0 ≤ a →
        realize R r a (a + 1) (h a) Q ≫ incoming R r a Q +
          differential R r a Q ≫ realize R r (a - 1) a
            ((LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)).toLinearMap.comp
              (h (a - 1))) Q =
        𝟙 (term R r a Q) - realize R r a a (originProjection r a) Q) ∧
      (∀ Q : Modules R,
        realize R r 0 0 (originProjection r 0) Q =
          augmentationMap R r Q ≫ sectionMapQ R r Q) ∧
      (∀ (Q : Modules R) (a : ℤ), a ≠ 0 →
        realize R r a a (originProjection r a) Q = 0) ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q') (a : ℤ),
        realize R r a (a + 1) (h a) Q ≫ termMap R r (a + 1) f =
          termMap R r a f ≫ realize R r a (a + 1) (h a) Q') ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q'),
        f ≫ sectionMapQ R r Q' = sectionMapQ R r Q ≫ termMap R r 0 f) ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q') (a : ℤ),
        termMap R r a f ≫ differential R r a Q' =
          differential R r a Q ≫ termMap R r (a - 1) f) ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q'),
        termMap R r 0 f ≫ augmentationMap R r Q' = augmentationMap R r Q ≫ f) ∧
      (∀ {Q Q' : Modules R} (f : Q ⟶ Q') (a : ℤ) (w : Fin r → ℤ),
        termMap R r a f ≫ translation R r a w Q' =
          translation R r a w Q ≫ termMap R r a f) ∧
      (∀ (Q : Modules R) (a : ℤ), 0 < a →
        ∃ hd : incoming R r a Q ≫ differential R r a Q = 0,
          (ShortComplex.mk (incoming R r a Q) (differential R r a Q) hd).Exact ∧
          ∃ t : kernel (differential R r a Q) ⟶ term R r (a + 1) Q,
            t ≫ incoming R r a Q = kernel.ι (differential R r a Q)) ∧
      (∀ Q : Modules R,
        ∃ hd : differential R r 1 Q ≫ augmentationMap R r Q = 0,
          (ShortComplex.mk (differential R r 1 Q) (augmentationMap R r Q) hd).Exact ∧
          ∃ t : kernel (augmentationMap R r Q) ⟶ term R r 1 Q,
            t ≫ differential R r 1 Q = kernel.ι (augmentationMap R r Q)) ∧
      (r = 0 → (∀ a : ℤ, h a = 0) ∧
        ∀ Q : Modules R, augmentationMap R r Q ≫ sectionMapQ R r Q = 𝟙 (term R r 0 Q)) := by
  sorry

end Profinite.LatticeCubical
