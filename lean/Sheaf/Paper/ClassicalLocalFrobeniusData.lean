/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.NormalizedClassicalWeilRealization
public import Sheaf.Paper.LocalFrobeniusLargeCoefficients
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PathTransport
import Sheaf.Paper.ClassicalPullbackCompositionCoherence
import Sheaf.Paper.LocalFrobeniusLargeWeilAddition
import Sheaf.Paper.LocalFrobeniusLargeTransportAddition

/-! # Classical local Frobenius factors and their realization comparisons

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15;
blueprint real-mixed-by-curves, first paragraph
(blueprint: def-zl-classical-local-frobenius-data).

The classical factors use the existing finite-etale paths and the actual
inverse-limit/rationalized automorphism fibre comparison. Positive exponents are
indexed by n+1, as in the published local Frobenius construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.ClassicalLocalFrobenius

section GenericBlockRecurrence
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem classicalMk_hom {C : Type*} [Category* C]
    (F : C ⥤ C) (A : C) (t : F.obj A ≅ A) :
    HEq (CategoryTheory.Endofunctor.IsoAlgebra.mk A t).str.hom t.hom := by
  rfl

private theorem classicalIndex_heq {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem classicalStep_heq {I : Type*} {C : Type*} [Category* C]
    (mul : I → I → I) (P : I → (C ⥤ C))
    (c : ∀ f g, ∀ A : C, (P (mul f g)).obj A ⟶ (P f).obj ((P g).obj A))
    (A : C) (f f' g : I) (e : f = f') (θ : (P g).obj A ⟶ A)
    (a : (P f).obj A ⟶ A) (b : (P f').obj A ⟶ A) (hab : HEq a b) :
    HEq (c f g A ≫ (P f).map θ ≫ a)
      (c f' g A ≫ (P f').map θ ≫ b) := by
  subst f'
  cases hab
  rfl

private theorem classicalBlockRecurrence {I : Type*} {C : Type*} [Category* C]
    (mul : I → I → I) (P : I → (C ⥤ C))
    (c : ∀ f g, ∀ A : C, (P (mul f g)).obj A ⟶ (P f).obj ((P g).obj A))
    (power : I → ℕ → I) (g : I) (A : C)
    (θ : ∀ n, (P (power g n)).obj A ⟶ A)
    (hadd : ∀ a b, HEq
      (c (power g a) (power g b) A ≫
        (P (power g a)).map (θ b) ≫ θ a) (θ (a + b + 1)))
    (m : ℕ) (A' : C) (hA : A' = A)
    (ψ : (P (power g m)).obj A' ⟶ A') (hψ : HEq ψ (θ m))
    (φ : ∀ n, (P (power (power g m) n)).obj A' ⟶ A')
    (index : ℕ → ℕ)
    (hp : ∀ n, power (power g m) n = power g (index n))
    (e0 : m = index 0)
    (es : ∀ n, index n + m + 1 = index (n + 1))
    (hzero : HEq (φ 0) ψ)
    (hstep : ∀ n, HEq (φ (n + 1))
      (c (power (power g m) n) (power g m) A' ≫
        (P (power (power g m) n)).map ψ ≫ φ n))
    (n : ℕ) : HEq (φ n) (θ (index n)) := by
  cases hA
  cases eq_of_heq hψ
  induction n with
  | zero => exact hzero.trans (classicalIndex_heq θ e0)
  | succ n ih =>
    refine (hstep n).trans ?_
    refine (classicalStep_heq mul P c A _ _ (power g m) (hp n) (θ m) _ _ ih).trans ?_
    exact (hadd (index n) m).trans (classicalIndex_heq θ (es n))

end GenericBlockRecurrence

private theorem classicalBlockIndex_zero (m : ℕ) :
    m = (m + 1) * (0 + 1) - 1 := by omega

private theorem classicalBlockIndex_succ (m n : ℕ) :
    (m + 1) * (n + 1) - 1 + m + 1 = (m + 1) * (n + 1 + 1) - 1 := by
  have hp : 0 < (m + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
  have hmul : (m + 1) * (n + 1 + 1) = (m + 1) * (n + 1) + (m + 1) :=
    Nat.mul_succ (m + 1) (n + 1)
  omega

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Positive powers with exactly the recursion of localPositivePower.
Source: blueprint period convention
(blueprint: def-zl-classical-local-frobenius-data). -/
def positiveIso {X : Scheme.{u}} (g : X ≅ X) : ℕ → (X ≅ X)
  | 0 => g
  | n + 1 => positiveIso g n ≪≫ g

/-- Positive isomorphism powers have the published positive morphism powers.
Source: blueprint iterate convention
(blueprint: def-zl-classical-local-frobenius-data).
Proof: induction on n. The initial hom is g.hom; composition of isomorphisms
has hom the composite of homs, which gives the same successor recursion. -/
theorem positiveIso_hom {X : Scheme.{u}} (g : X ≅ X) (n : ℕ) :
    (positiveIso g n).hom = localPositivePower g.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (positiveIso g n).hom ≫ g.hom = localPositivePower g.hom n ≫ g.hom
    rw [ih]

private theorem positiveIso_add {Y : Scheme.{u}} (g : Y ≅ Y) (a b : ℕ) :
    positiveIso g a ≪≫ positiveIso g b = positiveIso g (a + b + 1) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega]
    change positiveIso g a ≪≫ (positiveIso g b ≪≫ g) =
      (positiveIso g (a + b + 1)) ≪≫ g
    rw [← Iso.trans_assoc, ih]

private theorem classicalPost_heq {C : Type*} [Category* C] {A A' B T : C}
    (e : A = A') {a : A ⟶ B} {b : A' ⟶ B} (hab : HEq a b) (v : B ⟶ T) :
    HEq (a ≫ v) (b ≫ v) := by
  cases e
  cases hab
  rfl

private theorem classicalApply_heq {A : Sort*} {B T : A → Sort*}
    (F : (i : A) → B i → T i) {i j : A} (e : i = j)
    {x : B i} {y : B j} (hxy : HEq x y) : HEq (F i x) (F j y) := by
  cases e
  cases hxy
  rfl


section Classical
variable {Y : Scheme.{u}} [IsNoetherian Y] [Y.IsSeparated]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Fibre functor with the published inverse-limit object function.
Source: Weil II (1.1.1)b)--d)
(blueprint: def-zl-classical-local-frobenius-data). -/
def fibre {κ : Type u} [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Y) :
    LisseAlgebraicSheaf l Y Ω ⥤ ModuleCat.{u + 1} Ω :=
  (lisseAlgebraicFiberFunctor l Y x Ω).copyObj
    (lisseAlgebraicFiber l Y Ω x)
    (fun F ↦ eqToIso (lisseAlgebraicFiberFunctor_obj l Y x Ω F))

/-- The canonical compositor is fixed on all inverse-limit fibres by keeping each germ.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: def-zl-classical-local-frobenius-data).
Proof: literal site reindexing composes by associativity of scheme maps. At each
finite quotient send a germ to that same germ, with its two reindexings associated.
The stalk comparison has this prescription on every colimit injection. Apply all
limit projections, then tensor with the finite coefficient field and Ω. This gives
the displayed equation. Naturality follows at each quotient and hence on rational
maps. Geometric fibres detect equality of lisse maps, giving uniqueness. -/
theorem classicalComposition_existsUnique (h k : Y ≅ Y) :
    ∃! c : lisseAlgebraicAutomorphismPullback k l Ω ⋙
        lisseAlgebraicAutomorphismPullback h l Ω ≅
        lisseAlgebraicAutomorphismPullback (h ≪≫ k) l Ω,
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ Y)
        (F : LisseAlgebraicSheaf l Y Ω),
        (fibre l Ω x).map (c.hom.app F) ≫
            (lisseAlgebraicAutomorphismFiberIso (h ≪≫ k) l Ω x F).hom =
          (lisseAlgebraicAutomorphismFiberIso h l Ω x
            ((lisseAlgebraicAutomorphismPullback k l Ω).obj F)).hom ≫
          (lisseAlgebraicAutomorphismFiberIso k l Ω (x ≫ h.hom) F).hom ≫
          eqToHom (congrArg (fun y ↦ lisseAlgebraicFiber l Y Ω y F)
            (Category.assoc x h.hom k.hom)) := by
  sorry

/-- The uniquely germ-normalized classical compositor.
Source: BS 6.8.4(1),(4), 6.8.15
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalComposition (h k : Y ≅ Y) :=
  (classicalComposition_existsUnique l Ω h k).exists.choose

/-- Iterate the rational Weil isomorphism; no invariant integral lattice is requested.
Source: Weil II (1.1.10); blueprint theta^[n]
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalWeilIterate (g : Y ≅ Y) (M : EtaleLisseWeilSheaf l Ω g) :
    (n : ℕ) →
      (lisseAlgebraicAutomorphismPullback (positiveIso g n) l Ω).obj M.carrier ≅ M.carrier
  | 0 => M.str
  | n + 1 =>
    (classicalComposition l Ω (positiveIso g n) g).symm.app M.carrier ≪≫
      (lisseAlgebraicAutomorphismPullback (positiveIso g n) l Ω).mapIso M.str ≪≫
      classicalWeilIterate g M n


private theorem classicalWeilIterate_zero_heq (g : Y ≅ Y)
    (M : EtaleLisseWeilSheaf l Ω g) :
    HEq (classicalWeilIterate l Ω g M 0).hom M.str.hom := by rfl

private theorem classicalWeilIterate_succ_heq (g : Y ≅ Y)
    (M : EtaleLisseWeilSheaf l Ω g) (n : ℕ) :
    HEq (classicalWeilIterate l Ω g M (n + 1)).hom
      ((classicalComposition l Ω (positiveIso g n) g).inv.app M.carrier ≫
        (lisseAlgebraicAutomorphismPullback (positiveIso g n) l Ω).map M.str.hom ≫
        (classicalWeilIterate l Ω g M n).hom) := by
  rw [classicalWeilIterate]
  rfl


section ClassicalAddition
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] lisseAlgebraicAutomorphismPullback classicalComposition
  classicalWeilIterate


private theorem classicalComposition_map_assoc (f g h : Y ≅ Y)
    (K L : LisseAlgebraicSheaf l Y Ω)
    (t : (lisseAlgebraicAutomorphismPullback h l Ω).obj K ⟶ L) :
    HEq
      ((classicalComposition l Ω f (g ≪≫ h)).inv.app K ≫
        (lisseAlgebraicAutomorphismPullback f l Ω).map
          ((classicalComposition l Ω g h).inv.app K) ≫
        (lisseAlgebraicAutomorphismPullback f l Ω).map
          ((lisseAlgebraicAutomorphismPullback g l Ω).map t))
      ((classicalComposition l Ω (f ≪≫ g) h).inv.app K ≫
        (lisseAlgebraicAutomorphismPullback (f ≪≫ g) l Ω).map t ≫
        (classicalComposition l Ω f g).inv.app L) := by
  have hc : HEq
      ((classicalComposition l Ω f (g ≪≫ h)).inv.app K ≫
        (lisseAlgebraicAutomorphismPullback f l Ω).map
          ((classicalComposition l Ω g h).inv.app K))
      ((classicalComposition l Ω (f ≪≫ g) h).inv.app K ≫
        (classicalComposition l Ω f g).inv.app
          ((lisseAlgebraicAutomorphismPullback h l Ω).obj K)) := by
    unfold classicalComposition
    exact normalizedClassicalComposition_assoc l Ω
      (fun a b ↦ (classicalComposition_existsUnique l Ω a b).exists.choose)
      (fun a b ↦ by
        simpa only [fibre] using
          (classicalComposition_existsUnique l Ω a b).exists.choose_spec) f g h K
  have hn := (classicalComposition l Ω f g).inv.naturality t
  have hs := classicalPost_heq
    (congrArg (fun j ↦ (lisseAlgebraicAutomorphismPullback j l Ω).obj K)
      (Iso.trans_assoc f g h).symm) hc
    ((lisseAlgebraicAutomorphismPullback f l Ω).map
      ((lisseAlgebraicAutomorphismPullback g l Ω).map t))
  simp only [Category.assoc] at hs
  refine hs.trans (heq_of_eq ?_)
  exact congrArg (fun v ↦ (classicalComposition l Ω (f ≪≫ g) h).inv.app K ≫ v)
    hn.symm

private theorem classicalWeilIterate_add (g : Y ≅ Y)
    (M : EtaleLisseWeilSheaf l Ω g) (a b : ℕ) :
    HEq
      ((classicalComposition l Ω (positiveIso g a) (positiveIso g b)).inv.app M.carrier ≫
        (lisseAlgebraicAutomorphismPullback (positiveIso g a) l Ω).map
          (classicalWeilIterate l Ω g M b).hom ≫
        (classicalWeilIterate l Ω g M a).hom)
      (classicalWeilIterate l Ω g M (a + b + 1)).hom := by
  let P := fun j : Y ≅ Y ↦ lisseAlgebraicAutomorphismPullback j l Ω
  let θ := fun n ↦ (classicalWeilIterate l Ω g M n).hom
  have step (n : ℕ) : θ (n + 1) =
      (classicalComposition l Ω (positiveIso g n) g).inv.app M.carrier ≫
        (P (positiveIso g n)).map M.str.hom ≫ θ n := by
    dsimp only [θ]
    rw [classicalWeilIterate]
    rfl
  have zero : θ 0 = M.str.hom := by
    simp only [θ, classicalWeilIterate]
  change HEq
    ((classicalComposition l Ω _ _).inv.app M.carrier ≫ (P _).map (θ b) ≫ θ a)
    (θ (a + b + 1))
  induction b with
  | zero =>
    simpa only [Nat.add_zero, positiveIso, zero] using heq_of_eq (step a).symm
  | succ b ih =>
    have hpow := positiveIso_add g a b
    have hc := classicalComposition_map_assoc l Ω
      (positiveIso g a) (positiveIso g b) g M.carrier M.carrier M.str.hom
    have hc' := classicalPost_heq
      (congrArg (fun j ↦ (P j).obj M.carrier)
        (Iso.trans_assoc (positiveIso g a) (positiveIso g b) g).symm)
      hc ((P (positiveIso g a)).map (θ b) ≫ θ a)
    simp only [Category.assoc] at hc'
    have hi := classicalApply_heq
      (fun (j : Y ≅ Y) (t : (P j).obj M.carrier ⟶ M.carrier) ↦
        (classicalComposition l Ω j g).inv.app M.carrier ≫ (P j).map M.str.hom ≫ t)
      hpow ih
    have ht := (hc'.trans hi).trans (heq_of_eq (step (a + b + 1)).symm)
    simpa only [step, Functor.map_comp, Category.assoc, Nat.add_succ, positiveIso] using ht

end ClassicalAddition

end Classical

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- Classical restriction/coprojection transport on finite germs, limits and scalars.
Source: BS 6.8.4(1),(4), 6.8.15; Weil II (1.1.7)
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalTransport (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω) :=
  etaleAlgebraicPathIso l Ω M
    (FiniteEtale.fiberReparamIso (positiveIso (frobeniusPointIso D) n) x).symm

/-- Equality transport from positive isomorphism powers to positive morphism powers.
Source: blueprint semilinear return convention
(blueprint: def-zl-classical-local-frobenius-data). -/
def powerFibre {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    [∀ z : X, Invertible (l : X.residueField z)] (g : X ≅ X)
    (x : Spec (.of D.k) ⟶ X) (n : ℕ) (M : LisseAlgebraicSheaf l X Ω) :
    lisseAlgebraicFiber l X Ω (x ≫ (positiveIso g n).hom) M ≅
      lisseAlgebraicFiber l X Ω (x ≫ localPositivePower g.hom n) M :=
  eqToIso (congrArg (fun f ↦ lisseAlgebraicFiber l X Ω (x ≫ f) M)
    (positiveIso_hom g n))

/-- The middle classical factor retains the actual semilinear return equality.
Source: BS 6.8.15; Weil II (1.1.7)
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalReturn (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x)
    (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω) :=
  eqToIso (congrArg (fun f ↦ lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω
    (f ≫ x) M) (positiveIso_hom (frobeniusPointIso D) n)) ≪≫
  eqToIso (congrArg (fun y ↦ lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω y M)
    h.symm) ≪≫
  (powerFibre l Ω D (D.geometricFrobenius Y₀) x n M).symm ≪≫
  (lisseAlgebraicAutomorphismFiberIso
    (positiveIso (D.geometricFrobenius Y₀) n) l Ω x M).symm

/-- The classical operator on the actual inverse-limit algebraic-coefficient fibre.
Source: Weil II (1.1.7)--(1.1.10)
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalOperator (M : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :=
  (classicalTransport l Ω D Y₀ x n M.carrier).hom ≫
    (classicalReturn l Ω D Y₀ x n h M.carrier).hom ≫
    (fibre l Ω x).map (classicalWeilIterate l Ω (D.geometricFrobenius Y₀) M n).hom

variable (R : ZlClassicalRealization D l hl Ω Y₀)

/-- The pinned comparison iterated with the actual classical and sf compositors.
Source: BS 6.8.15; blueprint proof step 5
(blueprint: def-zl-classical-local-frobenius-data). -/
def realizationIterate (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω) :
    (n : ℕ) →
      (@commonStageDerivedPullback l _ Ω _ _ _ _ _
        (localPositivePower (D.geometricFrobenius Y₀).hom n)
        (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj
        (R.functor.obj M) ≅
      R.functor.obj ((lisseAlgebraicAutomorphismPullback
        (positiveIso (D.geometricFrobenius Y₀) n) l Ω).obj M)
  | 0 => R.pullback.app M
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    LocalFrobeniusLarge.composition l Ω
        (localPositivePower (D.geometricFrobenius Y₀).hom n)
        (D.geometricFrobenius Y₀).hom (R.functor.obj M) ≪≫
      (commonStageDerivedPullback l Ω
        (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso (R.pullback.app M) ≪≫
      realizationIterate ((lisseAlgebraicAutomorphismPullback
        (D.geometricFrobenius Y₀) l Ω).obj M) n ≪≫
      R.functor.mapIso ((classicalComposition l Ω
        (positiveIso (D.geometricFrobenius Y₀) n) (D.geometricFrobenius Y₀)).app M)

/-- The comparison on the source of the middle factor is obtained by composition
of pullbacks followed by the comparison at the reparametrized geometric point.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint proof steps 3--4
(blueprint: def-zl-classical-local-frobenius-data). -/
def transportedComparison
    (c : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
      R.functor ⋙ LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ fibre l Ω x)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (LocalFrobeniusLarge.pointFibre D l hl Ω).mapIso
    (LocalFrobeniusLarge.composition l Ω
      (localPositivePower (frobeniusPointIso D).hom n) x (R.functor.obj M)).symm ≪≫
  (c (localPositivePower (frobeniusPointIso D).hom n ≫ x)).app M ≪≫
  eqToIso (congrArg (fun f ↦ lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω
    (f ≫ x) M) (positiveIso_hom (frobeniusPointIso D) n).symm)

/-- The comparison on the source of the final Weil factor uses the pinned r-fold
realization comparison, rather than a fresh vector-space isomorphism.
Source: BS 6.8.15; blueprint proof step 5
(blueprint: def-zl-classical-local-frobenius-data). -/
def weilSourceComparison
    (c : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
      R.functor ⋙ LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ fibre l Ω x)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω) :=
  (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).mapIso
    (realizationIterate l Ω D hl Y₀ R M n) ≪≫
  (c x).app ((lisseAlgebraicAutomorphismPullback
    (positiveIso (D.geometricFrobenius Y₀) n) l Ω).obj M)

/-- The three separate squares of the completed fibre comparison. All intermediate
comparisons have fixed endpoints and are constructed from the same c and pinned R.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint proof steps 3--6
(blueprint: def-zl-classical-local-frobenius-data). -/
def FactorSquares
    (c : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
      R.functor ⋙ LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ fibre l Ω x) : Prop :=
  (∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
      (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω),
    LocalFrobeniusLarge.transportIterate D l hl Ω
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ x
          (frobeniusPointPrimeInvertible D l hl) (sfWeilPrimeInvertible D l hl Y₀)).obj
            (R.functor.obj M)) n ≫
      (transportedComparison l Ω D hl Y₀ R c x n M).hom =
    (c x).hom.app M ≫ (classicalTransport l Ω D Y₀ x n M).hom) ∧
  (∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
      (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
        localPositivePower (frobeniusPointIso D).hom n ≫ x)
      (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω),
    (LocalFrobeniusLarge.pointFibre D l hl Ω).map
        (LocalFrobeniusLarge.returnComparison D l hl Ω Y₀ (R.functor.obj M) x n h).hom ≫
      (weilSourceComparison l Ω D hl Y₀ R c x n M).hom =
    (transportedComparison l Ω D hl Y₀ R c x n M).hom ≫
      (classicalReturn l Ω D Y₀ x n h M).hom) ∧
  (∀ (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
      (M : ZlClassicalWeil D l Ω Y₀),
    (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map
        (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ ((R.weil.obj M).obj) n).hom ≫
      (c x).hom.app M.carrier =
    (weilSourceComparison l Ω D hl Y₀ R c x n M.carrier).hom ≫
      (fibre l Ω x).map (classicalWeilIterate l Ω (D.geometricFrobenius Y₀) M n).hom)

private theorem positivePower_eq_pow {X : Scheme.{u}} (g : X ⟶ X) (n : ℕ) :
    localPositivePower g n = (End.of g) ^ (n + 1) := by
  induction n with
  | zero => simp only [localPositivePower, Nat.zero_add, pow_one]
  | succ n ih =>
    rw [localPositivePower, ih]
    exact (pow_succ' (End.of g) (n + 1)).symm

/-- A block of m+1 positive powers repeated n+1 times is the product exponent.
Source: blueprint constant-field extension convention
(blueprint: def-zl-classical-local-frobenius-data).
Proof: induction on n, using associativity of composition and the positive-power
recursion. The successor adds m+1 to the exponent. The arithmetic identity is
(m+1)(n+2)=(m+1)(n+1)+(m+1); both factors are positive. -/
theorem positivePower_blocks {X : Scheme.{u}} (g : X ⟶ X) (m n : ℕ) :
    localPositivePower (localPositivePower g m) n =
      localPositivePower g ((m + 1) * (n + 1) - 1) := by
  simp only [positivePower_eq_pow]
  rw [← pow_mul]
  congr 1

/-- Iteration with a new Weil generator, using the same pullback compositors.
Source: BS 6.8.15; blueprint constant-field clause
(blueprint: def-zl-classical-local-frobenius-data). -/
def sfWeilAlong (g : (D.geometricFiber Y₀).left ⟶ (D.geometricFiber Y₀).left)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (θ : (@commonStageDerivedPullback l _ Ω _ _ _ _ _ g
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K ≅ K) :
    (n : ℕ) →
      (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (localPositivePower g n)
        (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K ≅ K
  | 0 => θ
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    LocalFrobeniusLarge.composition l Ω (localPositivePower g n) g K ≪≫
      (commonStageDerivedPullback l Ω (localPositivePower g n)).mapIso θ ≪≫
      sfWeilAlong g K θ n

/-- The new one-step transport is the old m+1-fold transport; subsequent steps are
applied on its successive pulled-back objects and use the actual composition maps.
Source: point-transport composition and the blueprint constant-field clause
(blueprint: def-zl-classical-local-frobenius-data). -/
def transportBlocks (m : ℕ)
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (n : ℕ) → (LocalFrobeniusLarge.pointFibre D l hl Ω).obj N ⟶
      (LocalFrobeniusLarge.pointFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (localPositivePower (frobeniusPointIso D).hom m) n)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)
  | 0 => LocalFrobeniusLarge.transportIterate D l hl Ω N m
  | n + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    LocalFrobeniusLarge.transportIterate D l hl Ω N m ≫
      transportBlocks m
        ((commonStageDerivedPullback l Ω
          (localPositivePower (frobeniusPointIso D).hom m)).obj N) n ≫
      (LocalFrobeniusLarge.pointFibre D l hl Ω).map
        (LocalFrobeniusLarge.composition l Ω
          (localPositivePower (localPositivePower (frobeniusPointIso D).hom m) n)
          (localPositivePower (frobeniusPointIso D).hom m) N).inv

section TransportProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] commonStageDerivedPullback LocalFrobeniusLarge.composition
  LocalFrobeniusLarge.pointFibre LocalFrobeniusLarge.transportIterate

private theorem dependent_heq {α : Sort*} {β : α → Sort*} (f : ∀ a, β a)
    {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem transportStep_heq {X : Scheme.{u}} {C T : Type*} [Category C] [Category T]
    (P : (X ⟶ X) → (C ⥤ C))
    (c : ∀ f g, ∀ A : C, (P (f ≫ g)).obj A ≅ (P f).obj ((P g).obj A))
    (F : C ⥤ T) (A : C) (f f' g : X ⟶ X) (e : f = f')
    (u : F.obj A ⟶ F.obj ((P g).obj A))
    (a : F.obj ((P g).obj A) ⟶ F.obj ((P f).obj ((P g).obj A)))
    (b : F.obj ((P g).obj A) ⟶ F.obj ((P f').obj ((P g).obj A))) (hab : HEq a b) :
    HEq (u ≫ a ≫ F.map (c f g A).inv) (u ≫ b ≫ F.map (c f' g A).inv) := by
  subst f'
  have h : a = b := eq_of_heq hab
  subst b
  rfl

/-- Coherent block expansion of every point transport.
Source: blueprint proof step 8 and point-transport composition
(blueprint: def-zl-classical-local-frobenius-data).
Proof: check restriction and inverse-image coprojection at each finite quotient.
Their composite for h and k is that for hk by functoriality of restriction and the
colimit relation for coprojections. The unit/compositor identifies the endpoints.
Induct over n blocks. Pass through the jointly injective completed-fibre projections,
then rationalization and Ω tensor. All inserted compositors are those of composition. -/
theorem transport_blocks
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
    (m n : ℕ) :
    transportBlocks l Ω D hl m N n ≫
      (LocalFrobeniusLarge.pointFibre D l hl Ω).map
        (eqToHom (congrArg
          (fun f ↦ (@commonStageDerivedPullback l _ Ω _ _ _ _ _ f
            (frobeniusPointPrimeInvertible D l hl)
            (frobeniusPointPrimeInvertible D l hl)).obj N)
          (positivePower_blocks (frobeniusPointIso D).hom m n))) =
      LocalFrobeniusLarge.transportIterate D l hl Ω N ((m + 1) * (n + 1) - 1) := by
  apply eq_of_heq
  simp only [eqToHom_map, comp_eqToHom_heq_iff]
  induction n generalizing N with
  | zero =>
    exact dependent_heq (fun j ↦ LocalFrobeniusLarge.transportIterate D l hl Ω N j)
      (by omega)
  | succ n ih =>
    simp only [transportBlocks]
    let := frobeniusPointPrimeInvertible D l hl
    refine (transportStep_heq
      (X := Spec (.of D.k))
      (C := generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k)))
      (fun f ↦ commonStageDerivedPullback l Ω f)
      (fun f g A ↦ LocalFrobeniusLarge.composition l Ω f g A)
      (LocalFrobeniusLarge.pointFibre D l hl Ω) N _ _
      (localPositivePower (frobeniusPointIso D).hom m)
      (positivePower_blocks (frobeniusPointIso D).hom m n)
      (LocalFrobeniusLarge.transportIterate D l hl Ω N m) _ _ (ih _)).trans ?_
    have ha := LocalFrobeniusLarge.transportIterate_add D l hl Ω N m
      ((m + 1) * (n + 1) - 1)
    have he : m + ((m + 1) * (n + 1) - 1) + 1 =
        (m + 1) * (n + 1 + 1) - 1 := by
      have hp : 0 < (m + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
      have hmul : (m + 1) * (n + 1 + 1) = (m + 1) * (n + 1) + (m + 1) :=
        Nat.mul_succ (m + 1) (n + 1)
      omega
    exact ha.trans
      (dependent_heq (fun j ↦ LocalFrobeniusLarge.transportIterate D l hl Ω N j) he)

end TransportProof

section BlockProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] commonStageDerivedPullback LocalFrobeniusLarge.composition
  LocalFrobeniusLarge.weilIterate

private theorem weilStep_heq {X : Scheme.{u}} {C : Type*} [Category C]
    (P : (X ⟶ X) → (C ⥤ C))
    (c : ∀ f g, ∀ A : C, (P (f ≫ g)).obj A ≅ (P f).obj ((P g).obj A))
    (A : C) (f f' g : X ⟶ X) (e : f = f') (θ : (P g).obj A ⟶ A)
    (a : (P f).obj A ⟶ A) (b : (P f').obj A ⟶ A) (hab : HEq a b) :
    HEq ((c f g A).hom ≫ (P f).map θ ≫ a)
      ((c f' g A).hom ≫ (P f').map θ ≫ b) := by
  subst f'
  have h : a = b := eq_of_heq hab
  subst b
  rfl

-- Preserve the original signature, including hypotheses unused by the categorical induction.
set_option linter.unusedSectionVars false in
/-- The constant-extension sf Weil structure is the old iterated structure.
Source: blueprint proof steps 5,8
(blueprint: def-zl-classical-local-frobenius-data).
Proof: apply the recursion for sfWeilAlong, inserting the old m+1-fold structure.
Induct on n. Naturality of the pullback compositor moves the earlier structure past
the block comparison. The associativity pentagon identifies the two regroupings.
The resulting word consists of (m+1)(n+1) copies of the old Weil map. -/
theorem sfWeil_blocks (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (m n : ℕ) :
    (sfWeilAlong l Ω D hl Y₀
        (localPositivePower (D.geometricFrobenius Y₀).hom m) K.carrier
        (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K m) n).hom =
      eqToHom (congrArg
        (fun f ↦ (@commonStageDerivedPullback l _ Ω _ _ _ _ _ f
          (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier)
        (positivePower_blocks (D.geometricFrobenius Y₀).hom m n)) ≫
      (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K
        ((m + 1) * (n + 1) - 1)).hom := by
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff]
  induction n with
  | zero =>
    exact dependent_heq (fun j ↦ (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K j).hom)
      (by omega)
  | succ n ih =>
    let := sfWeilPrimeInvertible D l hl Y₀
    change HEq
      ((LocalFrobeniusLarge.composition l Ω
          (localPositivePower (localPositivePower (D.geometricFrobenius Y₀).hom m) n)
          (localPositivePower (D.geometricFrobenius Y₀).hom m) K.carrier).hom ≫
        (commonStageDerivedPullback l Ω
          (localPositivePower (localPositivePower (D.geometricFrobenius Y₀).hom m) n)).map
            (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K m).hom ≫
        (sfWeilAlong l Ω D hl Y₀
          (localPositivePower (D.geometricFrobenius Y₀).hom m) K.carrier
          (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K m) n).hom) _
    refine (weilStep_heq
      (X := (D.geometricFiber Y₀).left)
      (C := generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
      (fun f ↦ commonStageDerivedPullback l Ω f)
      (fun f g A ↦ LocalFrobeniusLarge.composition l Ω f g A) K.carrier _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom m)
      (positivePower_blocks (D.geometricFrobenius Y₀).hom m n)
      (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K m).hom _ _ ih).trans ?_
    have ha := LocalFrobeniusLarge.weilIterate_add D l hl Ω Y₀ K
      ((m + 1) * (n + 1) - 1) m
    have he : (m + 1) * (n + 1) - 1 + m + 1 = (m + 1) * (n + 1 + 1) - 1 := by
      have hp : 0 < (m + 1) * (n + 1) := Nat.mul_pos (by omega) (by omega)
      have hmul : (m + 1) * (n + 1 + 1) = (m + 1) * (n + 1) + (m + 1) :=
        Nat.mul_succ (m + 1) (n + 1)
      omega
    exact ha.trans
      (dependent_heq (fun j ↦ (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K j).hom) he)

end BlockProof

/-- Block powers of scheme isomorphisms, with their exact endpoints.
Source: blueprint constant-extension convention
(blueprint: def-zl-classical-local-frobenius-data).
Proof: apply isomorphism extensionality, positiveIso_hom and positivePower_blocks. -/
theorem positiveIso_blocks {X : Scheme.{u}} (g : X ≅ X) (m n : ℕ) :
    positiveIso (positiveIso g m) n = positiveIso g ((m + 1) * (n + 1) - 1) := by
  apply Iso.ext
  simp only [positiveIso_hom, positivePower_blocks]

/-- The new classical Weil sheaf uses precisely the old m+1-fold rational Weil map.
Source: Weil II (1.1.10), blueprint constant-extension clause
(blueprint: def-zl-classical-local-frobenius-data). -/
def classicalBlock (M : ZlClassicalWeil D l Ω Y₀) (m : ℕ) :
    EtaleLisseWeilSheaf l Ω (positiveIso (D.geometricFrobenius Y₀) m) :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk M.carrier
    (classicalWeilIterate l Ω (D.geometricFrobenius Y₀) M m)

section ClassicalBlockProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] lisseAlgebraicAutomorphismPullback classicalComposition
  classicalWeilIterate

set_option allowUnsafeReducibility true in
attribute [local reducible] classicalBlock CategoryTheory.Endofunctor.IsoAlgebra.mk

/-- Constant-extension classical Weil maps expand to the old product-period maps.
Source: Weil II (1.1.10); BS 6.8.15; blueprint proof step 8
(blueprint: def-zl-classical-local-frobenius-data).
Proof: the classical compositor is characterized at every finite germ, so its
associativity is the associativity of literal reindexing. Expand the block recursion,
use naturality on each rational Weil map and regroup the resulting word. Each
finite-stage word is identical; inverse limits and rationalization preserve it. -/
theorem classicalWeil_blocks (M : ZlClassicalWeil D l Ω Y₀) (m n : ℕ) :
    HEq (classicalWeilIterate l Ω (positiveIso (D.geometricFrobenius Y₀) m)
      (classicalBlock l Ω D Y₀ M m) n).hom
    (
    eqToHom (congrArg
      (fun g ↦ (lisseAlgebraicAutomorphismPullback g l Ω).obj M.carrier)
      (positiveIso_blocks (D.geometricFrobenius Y₀) m n)) ≫
    (classicalWeilIterate l Ω (D.geometricFrobenius Y₀) M
      ((m + 1) * (n + 1) - 1)).hom) := by
  apply (heq_eqToHom_comp_iff _ _ _).2
  let g := D.geometricFrobenius Y₀
  let B := classicalBlock l Ω D Y₀ M m
  have hA : B.carrier = M.carrier :=
    CategoryTheory.Endofunctor.IsoAlgebra.mk_carrier
      (F := lisseAlgebraicAutomorphismPullback (positiveIso g m) l Ω)
      M.carrier (classicalWeilIterate l Ω g M m)
  have hb : HEq B.str.hom (classicalWeilIterate l Ω g M m).hom :=
    classicalMk_hom (lisseAlgebraicAutomorphismPullback (positiveIso g m) l Ω)
      M.carrier (classicalWeilIterate l Ω g M m)
  exact classicalBlockRecurrence
    (I := (D.geometricFiber Y₀).left ≅ (D.geometricFiber Y₀).left)
    (C := LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω)
    (fun f g ↦ f ≪≫ g)
    (fun j ↦ lisseAlgebraicAutomorphismPullback j l Ω)
    (fun f g A ↦ (classicalComposition l Ω f g).inv.app A)
    (fun f j ↦ positiveIso f j)
    g M.carrier (fun j ↦ (classicalWeilIterate l Ω g M j).hom)
    (classicalWeilIterate_add l Ω g M) m B.carrier hA B.str.hom hb
    (fun j ↦ (classicalWeilIterate l Ω (positiveIso g m) B j).hom)
    (fun j ↦ (m + 1) * (j + 1) - 1)
    (positiveIso_blocks g m)
    (classicalBlockIndex_zero m)
    (classicalBlockIndex_succ m)
    (classicalWeilIterate_zero_heq l Ω (positiveIso g m) B)
    (classicalWeilIterate_succ_heq l Ω (positiveIso g m) B) n

end ClassicalBlockProof

end WeilConjectures.ClassicalLocalFrobenius
