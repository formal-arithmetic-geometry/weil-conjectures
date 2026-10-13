/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Canonical first Tor action and natural base-change map

Source: Stacks Project, Algebra, Tag 00MM (lemma-surjective-on-tor-one).
The coefficient action is induced by multiplication in the second Tor argument.
The natural map is constructed using the balanced tensor universal property.
(blueprint: lem-weil-pbc-tor-one-surjective-flat-middle).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CategoryTheory

noncomputable section

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
set_option backward.isDefEq.respectTransparency false in
/-- Additivity in coefficient maps follows by computing on one resolution of `M`.
(blueprint: lem-weil-pbc-tor-one-second-additive) -/
noncomputable instance torOneSecondAdditive :
    ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).Additive := by
  constructor
  intro X Y f g
  change (NatTrans.leftDerived ((tensoringRight (ModuleCat R)).map (f + g)) 1).app
      (ModuleCat.of R M) =
    (NatTrans.leftDerived ((tensoringRight (ModuleCat R)).map f) 1).app
      (ModuleCat.of R M) +
    (NatTrans.leftDerived ((tensoringRight (ModuleCat R)).map g) 1).app
      (ModuleCat.of R M)
  simp only [Functor.map_add]
  let P := projectiveResolution (ModuleCat.of R M)
  rw [P.leftDerived_app_eq _ 1, P.leftDerived_app_eq _ 1, P.leftDerived_app_eq _ 1]
  have h : (NatTrans.mapHomologicalComplex
      ((tensoringRight (ModuleCat R)).map f + (tensoringRight (ModuleCat R)).map g)
      (ComplexShape.down ℕ)).app P.complex =
      (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f)
        (ComplexShape.down ℕ)).app P.complex +
      (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
        (ComplexShape.down ℕ)).app P.complex := by
    ext i
    rfl
  rw [h, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

set_option backward.isDefEq.respectTransparency false in
/-- Homology preserves scalar multiplication on chain maps. -/
theorem torHomology_map_smul {X Y : ChainComplex (ModuleCat R) ℕ}
    (f : X ⟶ Y) (r : R) :
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).map
      (r • f) = r •
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) 1).map f := by
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor
    (ModuleCat R) (ComplexShape.down ℕ) 1).map (r • f)) = _
  have h : (HomologicalComplex.shortComplexFunctor
      (ModuleCat R) (ComplexShape.down ℕ) 1).map (r • f) =
      r • (HomologicalComplex.shortComplexFunctor
        (ModuleCat R) (ComplexShape.down ℕ) 1).map f := by
    ext <;> rfl
  rw [h, ShortComplex.homologyMap_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- First Tor is linear in maps of the second argument.
(blueprint: lem-weil-pbc-tor-one-second-linear) -/
noncomputable instance torOneSecondLinear :
    ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).Linear R := by
  constructor
  intro X Y f r
  change (NatTrans.leftDerived ((tensoringRight (ModuleCat R)).map (r • f)) 1).app
      (ModuleCat.of R M) = r •
    (NatTrans.leftDerived ((tensoringRight (ModuleCat R)).map f) 1).app
      (ModuleCat.of R M)
  have h : (tensoringRight (ModuleCat R)).map (r • f) =
      r • (tensoringRight (ModuleCat R)).map f := by
    ext Z x
    simp
  rw [h]
  let P := projectiveResolution (ModuleCat.of R M)
  rw [P.leftDerived_app_eq _ 1, P.leftDerived_app_eq _ 1]
  have hc : (NatTrans.mapHomologicalComplex
      (r • (tensoringRight (ModuleCat R)).map f) (ComplexShape.down ℕ)).app P.complex =
      r • (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map f)
        (ComplexShape.down ℕ)).app P.complex := by
    ext i
    rfl
  rw [hc, torHomology_map_smul, Linear.smul_comp, Linear.comp_smul]

/-- First Tor, deriving in the first argument. -/
abbrev TorOne (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (N : Type u) [AddCommGroup N] [Module R N] : ModuleCat R :=
  (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/-- The canonical algebra structure on the last ring of a compatible tower.
Its scalar action is the given `R`-action, not a replacement of it. -/
@[instance_reducible]
def torTowerAlgebra (A B : Type u) [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B] : Algebra R B :=
  Algebra.ofModule
    (fun r x y => by
      rw [← IsScalarTower.algebraMap_smul A r x,
        ← IsScalarTower.algebraMap_smul A r (x * y), smul_mul_assoc])
    (fun r x y => by
      rw [← IsScalarTower.algebraMap_smul A r y,
        ← IsScalarTower.algebraMap_smul A r (x * y), mul_smul_comm])

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Multiplication by `s`, regarded as an `R`-linear endomorphism. -/
def torCoefficientMul (s : S) : ModuleCat.of R S ⟶ ModuleCat.of R S :=
  ModuleCat.ofHom (Algebra.lsmul R R S s)

/-- The canonical action on Tor is the image of coefficient multiplication.
All module laws are proved from functoriality and additivity. -/
@[instance_reducible]
def torOneModule : Module S (TorOne R M S) where
  smul s t := (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
    (torCoefficientMul R S s)) t
  one_smul t := by
    have h : torCoefficientMul R S 1 = 𝟙 (ModuleCat.of R S) := by ext; simp [torCoefficientMul]
    change ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S 1) t = t
    simp only [h, Functor.map_id, ModuleCat.id_apply]
  mul_smul s s' t := by
    have h : torCoefficientMul R S (s * s') =
        torCoefficientMul R S s' ≫ torCoefficientMul R S s := by
      ext x
      simp [torCoefficientMul]
    change ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S (s * s')) t =
      ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S s)
        (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S s') t)
    simp only [h, Functor.map_comp, ModuleCat.comp_apply]
  smul_zero s :=
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
      (torCoefficientMul R S s)).hom.map_zero
  smul_add s t t' :=
    (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
      (torCoefficientMul R S s)).hom.map_add t t'
  add_smul s s' t := by
    have h : torCoefficientMul R S (s + s') =
        torCoefficientMul R S s + torCoefficientMul R S s' := by
      ext x
      simp [torCoefficientMul]
    change ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S (s + s')) t =
      ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S s) t +
      ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S s') t
    simp only [h, Functor.map_add, ModuleCat.hom_add, LinearMap.add_apply]
  zero_smul t := by
    have h : torCoefficientMul R S 0 = 0 := by ext; simp [torCoefficientMul]
    change ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMul R S 0) t = 0
    simp only [h, Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]


/-- The canonical action is functorial multiplication in the second argument. -/
theorem torOneModule_smul (s : S) (t : TorOne R M S) :
    letI := torOneModule R M S
    s • t = ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
      (torCoefficientMul R S s) t := rfl

/-- The canonical Tor action restricts to the original `R`-action. -/
theorem torOne_algebraMap_smul (r : R) (t : TorOne R M S) :
    letI := torOneModule R M S
    algebraMap R S r • t = r • t := by
  let := torOneModule R M S
  have h : torCoefficientMul R S (algebraMap R S r) = r • 𝟙 (ModuleCat.of R S) := by
    ext x
    simp [torCoefficientMul, Algebra.smul_def]
  change ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map
    (torCoefficientMul R S (algebraMap R S r)) t = r • t
  rw [h, Functor.map_smul, Functor.map_id]
  rfl

/-- The scalar tower of the canonical Tor module, with no arbitrary action binder. -/
theorem torOneScalarTower :
    letI := torOneModule R M S
    IsScalarTower R S (TorOne R M S) := by
  let := torOneModule R M S
  exact IsScalarTower.of_algebraMap_smul (torOne_algebraMap_smul R M S)


variable (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]

/-- The coefficient algebra map as an `R`-linear map. -/
def torCoefficientMap : ModuleCat.of R A ⟶ ModuleCat.of R B :=
  ModuleCat.ofHom
    { toFun := algebraMap A B
      map_add' := map_add _
      map_smul' := fun r a => by
        change algebraMap A B (r • a) = r • algebraMap A B a
        rw [← IsScalarTower.algebraMap_smul A r a,
          ← IsScalarTower.algebraMap_smul A r (algebraMap A B a)]
        simp [Algebra.smul_def] }

/-- Functorial map on first Tor induced by the coefficient algebra map. -/
def torOneCoefficientMap : TorOne R M A ⟶ TorOne R M B :=
  ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map (torCoefficientMap R A B)

/-- Scalar compatibility is a consequence of functoriality, not a hypothesis. -/
theorem torOneCoefficientMap_smul (a : A) (t : TorOne R M A) :
    let := torOneModule R M A
    let := torTowerAlgebra R A B
    let := torOneModule R M B
    torOneCoefficientMap R M A B (a • t) =
      algebraMap A B a • torOneCoefficientMap R M A B t := by
  let := torOneModule R M A
  let := torTowerAlgebra R A B
  let := torOneModule R M B
  have h : torCoefficientMul R A a ≫ torCoefficientMap R A B =
      torCoefficientMap R A B ≫ torCoefficientMul R B (algebraMap A B a) := by
    ext x
    change algebraMap A B (a * x) = algebraMap A B a * algebraMap A B x
    simp only [map_mul]
  let F := (Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)
  exact congrArg (fun f => f t) (show
    F.map (torCoefficientMul R A a) ≫ F.map (torCoefficientMap R A B) =
    F.map (torCoefficientMap R A B) ≫ F.map
      (torCoefficientMul R B (algebraMap A B a)) by
        rw [← F.map_comp, ← F.map_comp, h])

/-- The `B`-action on `Tor₁(M,A) ⊗[A] B`, acting on the right tensor factor. -/
@[instance_reducible]
def torOneTensorModule :
    letI := torOneModule R M A
    Module B (TorOne R M A ⊗[A] B) := by
  letI := torOneModule R M A
  exact (TensorProduct.comm A (TorOne R M A) B).toAddEquiv.module B

omit [Module R B] [IsScalarTower R A B] in
/-- The tensor source uses the standard action on its right factor. -/
theorem torOneTensorModule_smul_tmul (b c : B) (t : TorOne R M A) :
    letI := torOneModule R M A
    letI := torOneTensorModule R M A B
    b • (t ⊗ₜ[A] c) = t ⊗ₜ[A] (b * c) := by
  let := torOneModule R M A
  let := torOneTensorModule R M A B
  change (TensorProduct.comm A B (TorOne R M A))
    (b • (TensorProduct.comm A (TorOne R M A) B) (t ⊗ₜ[A] c)) = _
  simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]

/-- Balanced pure-tensor formula before taking the tensor quotient. -/
def torOnePairing :
    letI := torOneModule R M A
    letI := torTowerAlgebra R A B
    letI := torOneModule R M B
    TorOne R M A →+ B →+ TorOne R M B := by
  letI := torOneModule R M A
  letI := torTowerAlgebra R A B
  letI := torOneModule R M B
  let τ := torOneCoefficientMap R M A B
  exact
    { toFun := fun t =>
        { toFun := fun b => b • τ t
          map_zero' := zero_smul _ _
          map_add' := fun b b' => add_smul b b' (τ t) }
      map_zero' := by ext b; simp [τ]
      map_add' := by intro t t'; ext b; simp [τ, smul_add] }

/-- The natural `B`-linear base-change map. Its data is a balanced tensor lift,
not a choice of a morphism satisfying an existence statement. -/
def torOneBaseChange :
    letI := torOneModule R M A
    letI := torOneTensorModule R M A B
    letI := torTowerAlgebra R A B
    letI := torOneModule R M B
    (TorOne R M A ⊗[A] B) →ₗ[B] TorOne R M B := by
  letI := torOneModule R M A
  letI := torOneTensorModule R M A B
  letI := torTowerAlgebra R A B
  letI := torOneModule R M B
  let τ := torOneCoefficientMap R M A B
  let f := torOnePairing R M A B
  have hf : ∀ (a : A) (t : TorOne R M A) (b : B), f (a • t) b = f t (a • b) := by
    intro a t b
    change b • τ (a • t) = (a • b) • τ t
    rw [torOneCoefficientMap_smul R M A B, Algebra.smul_def, mul_smul,
      smul_comm]
  let g := TensorProduct.liftAddHom f hf
  refine { g with map_smul' := ?_ }
  intro b x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t c =>
    change g ((TensorProduct.comm A B (TorOne R M A))
      (b • (TensorProduct.comm A (TorOne R M A) B) (t ⊗ₜ[A] c))) = _
    simp only [TensorProduct.comm_tmul, TensorProduct.smul_tmul']
    exact mul_smul b c (τ t)
  | add x y hx hy =>
    change g (b • (x + y)) = b • g (x + y)
    change g (b • x) = b • g x at hx
    change g (b • y) = b • g y at hy
    rw [smul_add, g.map_add, hx, hy, g.map_add, smul_add]

/-- The natural map has the required pure-tensor value. -/
@[simp]
theorem torOneBaseChange_tmul (t : TorOne R M A) (b : B) :
    letI := torOneModule R M A
    letI := torOneTensorModule R M A B
    letI := torTowerAlgebra R A B
    letI := torOneModule R M B
    torOneBaseChange R M A B (t ⊗ₜ[A] b) = b • torOneCoefficientMap R M A B t := by
  let := torOneModule R M A
  let := torOneTensorModule R M A B
  let := torTowerAlgebra R A B
  let := torOneModule R M B
  have hf : ∀ (a : A) (t : TorOne R M A) (b : B),
      torOnePairing R M A B (a • t) b = torOnePairing R M A B t (a • b) := by
    intro a t b
    change b • torOneCoefficientMap R M A B (a • t) =
      (a • b) • torOneCoefficientMap R M A B t
    rw [torOneCoefficientMap_smul R M A B, Algebra.smul_def, mul_smul,
      smul_comm]
  change (TensorProduct.liftAddHom (torOnePairing R M A B) hf) (t ⊗ₜ[A] b) = _
  rw [TensorProduct.liftAddHom_tmul]
  rfl


/-- Let `R → A → B` be commutative-ring maps and `M` an `R`-module.
If `A ⊗[R] M` is flat over `A`, the specified natural `B`-linear map on first
Tor is surjective. The coefficient actions are constructed, not quantified over.

Source: Stacks Project, Algebra, Tag 00MM, lemma-surjective-on-tor-one.
Proof: choose a free resolution of M and tensor it with A and B. Write K_A and
K_B for its degree-one cycles, and I for the image of the first differential
with coefficients in A. Factor the augmented exact sequence into
0 → K_A → F₁ ⊗ A → I → 0 and 0 → I → F₀ ⊗ A → M ⊗ A → 0.
Flatness of the last term makes I ⊗ B → F₀ ⊗ B injective. Right exactness applied
to the first sequence therefore gives K_A ⊗ B → K_B surjective. Right exactness
of the quotient presentation F₂ ⊗ A → K_A → Tor₁(M,A) → 0 lets this surjection
descend modulo boundaries. The descended map agrees with `torOneBaseChange`:
both send a pure tensor t ⊗ b to b times the coefficient-map image of t.
Hence the constructed map is surjective.
(blueprint: lem-weil-pbc-tor-one-surjective-flat-middle) -/
-- STATEMENT-DISPUTED: The superseded signature permitted an arbitrary Tor action
-- and was false (opposite projection actions for ℤ → 𝔽₂ × 𝔽₂ → 𝔽₂).
-- This repair constructs the canonical action and map; keep the marker until delivery.
theorem torOne_surjective_flat_middle
    (R : Type u) (A : Type u) (B : Type u) (M : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat A (A ⊗[R] M)) :
    letI := torOneModule R M A
    letI := torOneTensorModule R M A B
    letI := torTowerAlgebra R A B
    letI := torOneModule R M B
    Function.Surjective (torOneBaseChange R M A B) := by
  sorry

end

end CategoryTheory
