/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Marked formal objects and versal rings of stacks

Source: Stacks Project, stacks-geometry.tex, Tag 0DQV (definition-versal-ring-at-x),
Tag 0DQY; artin.tex, definition-versal-formal-object; formal-defos.tex, Tags 06HR
and 06HS (definition-versal and remark-versal-object)
(blueprint: def-sfb-stack-versal-ring).

The definitions are extracted unchanged from StackVersalFiniteResidueExtension.
They retain the stack's existing total category and all marked arrows. Level n
means C/m^(n+1). A later common level in versality retains the exact prescribed
restriction isomorphism without choosing pullbacks or a cleavage.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.StackVersal

variable {R : Type u} [CommRing R]

/-- The affine R-scheme associated to an R-algebra.
Source: Stacks, Tag 0DQY, affine test schemes
(blueprint: def-sfb-stack-versal-ring). -/
abbrev affine (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The actual contravariant scheme map of an algebra homomorphism.
Source: Stacks, Tag 0DQY, affine test maps
(blueprint: def-sfb-stack-versal-ring). -/
def affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : affine (R := R) B ⟶ affine (R := R) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact f.commutes r)

/-- Objects of the existing stack fibre, with all automorphisms retained.
Source: Stacks, Tag 0DQY, the fibre over an affine scheme
(blueprint: def-sfb-stack-versal-ring). -/
abbrev Object (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (A : Type u) [CommRing A] [Algebra R A] := Functor.Fiber F.p (affine (R := R) A)

/-- An arrow over the specified ring map, hence a pullback identification in a fibred
in groupoids category. Source: Stacks, Tag 0DQY and Tag 003T
(blueprint: def-sfb-stack-versal-ring). -/
abbrev Arrow {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (y : Object F B) (x : Object F A) :=
  {a : y.val ⟶ x.val // F.p.IsHomLift (affineMap f) a}

/-- A complete Noetherian local R-algebra with its specified residue-field isomorphism.
Source: Stacks, Tags 0DQY and 06H5
(blueprint: def-sfb-stack-versal-ring). -/
structure CompleteLocalAlgebra (R k : Type u) [CommRing R] [Field k] [Algebra R k] where
  ring : CommAlgCat.{u} R
  localRing : IsLocalRing ring
  noetherian : IsNoetherianRing ring
  complete : IsAdicComplete (IsLocalRing.maximalIdeal ring) ring
  residueEquiv : IsLocalRing.ResidueField ring ≃ₐ[R] k

attribute [instance] CompleteLocalAlgebra.localRing CompleteLocalAlgebra.noetherian
  CompleteLocalAlgebra.complete

variable {k : Type u} [Field k] [Algebra R k]

/-- The positive-level infinitesimal quotient C / m^(n+1).
Source: Stacks, Tag 0DQY, marked formal object
(blueprint: def-sfb-stack-versal-ring). -/
abbrev Level (C : CompleteLocalAlgebra R k) (n : ℕ) :=
  C.ring ⧸ IsLocalRing.maximalIdeal C.ring ^ (n + 1)

/-- The canonical reduction from a higher positive level.
Source: Stacks, Tags 0DQY and 06H3
(blueprint: def-sfb-stack-versal-ring). -/
def reduction (C : CompleteLocalAlgebra R k) {m n : ℕ} (h : n ≤ m) :
    Level C m →ₐ[R] Level C n :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The specified residue map at each level, constructed from the quotient factor map.
Source: Stacks, Tag 0DQY
(blueprint: def-sfb-stack-versal-ring). -/
def levelResidue (C : CompleteLocalAlgebra R k) (n : ℕ) : Level C n →ₐ[R] k :=
  C.residueEquiv.toAlgHom.comp
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_self (Nat.succ_ne_zero n)))

/-- A local residue-preserving map to an Artinian test ring with residue field k.
Source: Stacks, Tag 0DQY, the local maps in the versality test
(blueprint: def-sfb-stack-versal-ring). -/
def IsMarkedMap (C : CompleteLocalAlgebra R k)
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra R A]
    (e : IsLocalRing.ResidueField A ≃ₐ[R] k) (f : C.ring →ₐ[R] A) : Prop :=
  IsLocalHom f ∧ ∀ c : C.ring,
    e (IsLocalRing.residue A (f c)) = C.residueEquiv (IsLocalRing.residue C.ring c)

/-- A finite truncation through which a map to a test ring factors.
Source: Stacks, Tag 0DQY, definition of evaluation
(blueprint: def-sfb-stack-versal-ring). -/
def KillsLevel (C : CompleteLocalAlgebra R k) {A : Type u}
    [CommRing A] [Algebra R A] (f : C.ring →ₐ[R] A) (n : ℕ) : Prop :=
  ∀ c ∈ IsLocalRing.maximalIdeal C.ring ^ (n + 1), f c = 0

/-- The induced map from a truncation, using the actual quotient universal property.
Source: Stacks, Tag 0DQY, evaluation of a formal object
(blueprint: def-sfb-stack-versal-ring). -/
def evaluationMap (C : CompleteLocalAlgebra R k) {A : Type u}
    [CommRing A] [Algebra R A] (f : C.ring →ₐ[R] A) (n : ℕ) (h : KillsLevel C f n) :
    Level C n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ f h

/-- The marked compatible tower of the node, expressed by arrows in the stack's
existing total category. All transition and marking identities are specified.
Source: Stacks, Tag 0DQY and Formal Deformation Theory, Tag 06H3
(blueprint: def-sfb-stack-versal-ring). -/
structure FormalObject (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (x : Object F k) (C : CompleteLocalAlgebra R k) where
  obj : ∀ n : ℕ, Object F (Level C n)
  transition : ∀ {m n : ℕ} (h : n ≤ m), Arrow (reduction C h) (obj n) (obj m)
  transition_id : ∀ n, (transition (le_refl n)).val = 𝟙 (obj n).val
  transition_comp : ∀ {l m n : ℕ} (h : n ≤ m) (h' : m ≤ l),
    (transition h).val ≫ (transition h').val = (transition (h.trans h')).val
  mark : ∀ n : ℕ, Arrow (levelResidue C n) x (obj n)
  mark_transition : ∀ {m n : ℕ} (h : n ≤ m),
    (mark n).val ≫ (transition h).val = (mark m).val

/-- Versality with the prescribed isomorphism retained. A test object y over A maps
cartesianly to a finite truncation of eta; b identifies y with the restriction of y'.
The final equality says that the lifted identification restricts to this exact one.
A later level N is permitted because every local map to an Artinian ring kills a
positive maximal-ideal power. This is independent of the finite level used to evaluate.
Source: Stacks, Tag 0DQY, and Formal Deformation Theory, Tags 06HR and 06HS
(blueprint: def-sfb-stack-versal-ring). -/
def FormalObject.IsVersal {F : BasedCategory.{v, w} (Over (Spec (.of R)))}
    {x : Object F k} {C : CompleteLocalAlgebra R k} (eta : FormalObject F x C) : Prop :=
  ∀ (A' A : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra R A']
    [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A]
    (e' : IsLocalRing.ResidueField A' ≃ₐ[R] k)
    (e : IsLocalRing.ResidueField A ≃ₐ[R] k) (q : A' →ₐ[R] A),
    IsLocalHom q → Function.Surjective q →
    (∀ a' : A', e (IsLocalRing.residue A (q a')) = e' (IsLocalRing.residue A' a')) →
    ∀ (f : C.ring →ₐ[R] A), IsMarkedMap C e f →
    ∀ (n : ℕ) (hf : KillsLevel C f n) (y' : Object F A') (y : Object F A)
      (s' : Arrow (e'.toAlgHom.comp (Ideal.Quotient.mkₐ R _)) x y')
      (s : Arrow (e.toAlgHom.comp (Ideal.Quotient.mkₐ R _)) x y)
      (b : Arrow q y y') (a : Arrow (evaluationMap C f n hf) y (eta.obj n)),
      s.val ≫ b.val = s'.val → s.val ≫ a.val = (eta.mark n).val →
      ∃ (f' : C.ring →ₐ[R] A'), IsMarkedMap C e' f' ∧ q.comp f' = f ∧
        ∃ (N : ℕ) (hN : n ≤ N) (hf' : KillsLevel C f' N)
          (a' : Arrow (evaluationMap C f' N hf') y' (eta.obj N)),
          s'.val ≫ a'.val = (eta.mark N).val ∧
            b.val ≫ a'.val = a.val ≫ (eta.transition hN).val

end CategoryTheory.StackVersal
