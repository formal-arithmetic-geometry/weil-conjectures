/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Coherent modules with a trivial-base torus linearization

Source: Stacks Project, Groupoids, Tag 03LF, and Tags 0EKK--0EKL;
Milne, Algebraic Groups, Theorem 12.12, pp.234--235
(blueprint: def-sfb-trivial-torus-coherent-data).

A linearization is recorded on the functor of test schemes: at a point
`z : W ⟶ Z`, each `t : W ⟶ T` acts on `z^* M`, naturally in `W`.
Evaluating at `W = T × Z` recovers the inverse of the usual descent
isomorphism `a^* M ≅ pr₂^* M`; naturality and the group-homomorphism
law are precisely its pullback, identity and cocycle laws. This uses full
pullback modules on all test schemes, not just their geometric fibres.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.TrivialTorusCoherent

variable {F : Type u} [Field F]

/-- Commutativity of the multiplicative group's recorded Hopf law.
Source: Stacks, Tag 022U (blueprint: def-sfb-trivial-torus-coherent-data).
Proof: its coordinate comultiplication sends t to t tensor t and is unchanged
by swapping the factors. Equality on the invertible Laurent generator gives
equality of the algebra maps and hence of the scheme multiplications. -/
theorem multiplicative_commutative (F : Type u) [Field F] :
    IsCommMonObj (StandardGroupSchemes.multiplicative F) := by
  sorry

/-- Commutativity for the recorded multiplicative group structure.
Source: Stacks, Tag 022U (blueprint: def-sfb-trivial-torus-coherent-data). -/
instance multiplicativeCommMonObj (F : Type u) [Field F] :
    IsCommMonObj (StandardGroupSchemes.multiplicative F) :=
  multiplicative_commutative F

/-- The actual group-scheme characters, with multiplication written additively.
Source: Milne, Definition 12.45 (blueprint: def-sfb-trivial-torus-coherent-data). -/
abbrev Character (T : Grp (Over (Spec (.of F)))) :=
  Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))

/-- The integral character ring, with basis `single χ 1`.
Source: Milne, Section 12 (blueprint: def-sfb-trivial-torus-coherent-data). -/
abbrev CharacterRing (T : Grp (Over (Spec (.of F)))) := AddMonoidAlgebra ℤ (Character T)

/-- Evaluation of a character at a test-scheme point using the Laurent coordinate.
Source: Milne, Definition 12.45 (blueprint: def-sfb-trivial-torus-coherent-data). -/
def characterValue (T : Grp (Over (Spec (.of F)))) (χ : Character T)
    (W : Over (Spec (.of F))) (t : W ⟶ T.X) : Γ(W.left, ⊤) :=
  (t ≫ χ.toMul.hom.hom).left.appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T 1))

/-- The module at a test-scheme point is its actual tensor pullback.
Source: Stacks, Tag 03LF (blueprint: def-sfb-trivial-torus-coherent-data). -/
abbrev testModule {Z : Over (Spec (.of F))} (M : Z.left.Modules)
    {W : Over (Spec (.of F))} (z : W ⟶ Z) : W.left.Modules :=
  (Scheme.Modules.tensorPullback z.left).obj M

/-- The canonical pullback of a module map to a test-scheme point.
Source: Stacks, Tag 03LF (blueprint: def-sfb-trivial-torus-coherent-data). -/
@[irreducible] def atMap {Z : Over (Spec (.of F))} {M N : Z.left.Modules}
    (f : M ⟶ N) {W : Over (Spec (.of F))} (z : W ⟶ Z) : testModule M z ⟶ testModule N z := by
  unfold testModule
  exact (Scheme.Modules.tensorPullback z.left).map f

/-- The canonical identification `(z ∘ f)^* M ≅ f^* z^* M`.
Source: Stacks, Tag 0097 (blueprint: def-sfb-trivial-torus-coherent-data). -/
@[irreducible] def atComp {Z : Over (Spec (.of F))} (M : Z.left.Modules)
    {W V : Over (Spec (.of F))} (f : W ⟶ V) (z : V ⟶ Z) :
    testModule M (f ≫ z) ≅ (Scheme.Modules.tensorPullback f.left).obj (testModule M z) := by
  unfold testModule
  exact (Scheme.Modules.tensorPullbackSectionComp f.left z.left).app M

/-- A trivial-base linearization, with forward fibre action, on all test schemes.
The naturality equation uses the canonical normalized tensor-pullback comparisons.
Source: Stacks, Tag 03LF (blueprint: def-sfb-trivial-torus-coherent-data). -/
structure Linearization (T : Grp (Over (Spec (.of F))))
    (Z : Over (Spec (.of F))) (M : Z.left.Modules) where
  action : ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z), (W ⟶ T.X) →* Aut (testModule M z)
  naturality : ∀ (W V : Over (Spec (.of F))) (f : W ⟶ V) (z : V ⟶ Z) (t : V ⟶ T.X),
    (atComp M f z).hom ≫
        (Scheme.Modules.tensorPullback f.left).map (action V z t).hom =
      (action W (f ≫ z) (f ≫ t)).hom ≫ (atComp M f z).hom

/-- A coherent sheaf with a linearization, using the kernel definition exposed
by the recorded coherence module alongside its original finite-type predicate.
Source: Stacks, Tags 01BV and 03LF (blueprint: def-sfb-trivial-torus-coherent-data). -/
structure Linearized (T : Grp (Over (Spec (.of F)))) (Z : Over (Spec (.of F))) where
  moduleObj : Z.left.Modules
  coherent : RingedSpace.IsCoherent Z.left.toRingedSpace moduleObj
  linearization : Linearization T Z moduleObj

/-- Intertwining of the actual forward actions after every base change.
Source: Stacks, Tag 03LF (blueprint: def-sfb-trivial-torus-coherent-data). -/
def Equivariant {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M N : Linearized T Z) (f : M.moduleObj ⟶ N.moduleObj) : Prop :=
  ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z) (t : W ⟶ T.X),
    atMap f z ≫ (N.linearization.action W z t).hom =
      (M.linearization.action W z t).hom ≫ atMap f z

/-- A subobject has character χ if its pulled-back image has that scalar action on
all test schemes, including nonreduced algebras. This also fixes the forward sign.
Source: Stacks, Tags 03LF and 0EKL (blueprint: def-sfb-trivial-torus-coherent-data). -/
def HasWeight {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M : Linearized T Z) (χ : Character T) (P : Subobject M.moduleObj) : Prop :=
  ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z) (t : W ⟶ T.X),
    atMap P.arrow z ≫ (M.linearization.action W z t).hom =
      (testModule (P : Z.left.Modules) z).smulHom (characterValue T χ W t) ≫ atMap P.arrow z

/-- The pure-character action on a whole module.
Source: Stacks, Tag 0EKL (blueprint: def-sfb-trivial-torus-coherent-data). -/
def IsPure {T : Grp (Over (Spec (.of F)))} {Z : Over (Spec (.of F))}
    (M : Linearized T Z) (χ : Character T) : Prop :=
  ∀ (W : Over (Spec (.of F))) (z : W ⟶ Z) (t : W ⟶ T.X),
    (M.linearization.action W z t).hom =
      (testModule M.moduleObj z).smulHom (characterValue T χ W t)

/-- A finite decomposition into coherent character subobjects, with its actual
coproduct inclusions. Subobjects make uniqueness equality, not a choice of bases.
Source: Stacks, Tag 0EKL (blueprint: def-sfb-trivial-torus-coherent-data). -/
def IsWeightDecomposition {T : Grp (Over (Spec (.of F)))}
    {Z : Over (Spec (.of F))} (M : Linearized T Z)
    (P : Character T → Subobject M.moduleObj) : Prop :=
  Set.Finite {χ | ¬ IsZero (P χ : Z.left.Modules)} ∧
    (∀ χ, RingedSpace.IsCoherent Z.left.toRingedSpace (P χ : Z.left.Modules) ∧
      HasWeight M χ (P χ)) ∧
    Nonempty (IsColimit (Cofan.mk M.moduleObj (fun χ => (P χ).arrow)))

end AlgebraicGeometry.TrivialTorusCoherent
