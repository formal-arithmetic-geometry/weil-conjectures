/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AdicHeartIntrinsicFibres
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedModuleReturn
/-! # Ordinary condensed punctual weights

Source: latest blueprint, lem-zl-affine-curve-hc2-purity, second proof paragraph;
Deligne, Weil II, (1.1.7)--(1.1.10)
(blueprint: def-weil-punctual-weights).

The coefficient is the existing finite-subextension-valued condensed ring. Pullbacks,
their compositors, ordinary derived categories and geometric-field evaluation are reused.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeil

/-- Canonical reparametrization on the scalar fibre, through the equivalence with
condensed modules over a separably closed point; no isomorphism is chosen.
Source: Deligne, Weil II (1.1.8); latest blueprint, second proof paragraph
(blueprint: def-weil-punctual-weights). -/
def pointInsertion (l : ℕ) [Fact l.Prime] (K : Type u) [Field K] [IsAlgClosed K]
    (f : Spec (.of K) ⟶ Spec (.of K)) :
    CondensedQbarGeometricEvaluation.fieldFiber K l ≅
      CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f ⋙
        CondensedQbarGeometricEvaluation.fieldFiber K l :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l) f).symm _

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Ordered positive iterates of a Weil isomorphism, with the actual pullback compositors.
The index n denotes exponent n+1, including the original structure when n=0.
Source: blueprint constant-extension paragraph, displayed theta^[e]
(blueprint: def-weil-punctual-weights). -/
def iterateAux {C : Type*} [Category C] {X : Scheme.{u}} (g : X ⟶ X)
    (P : (X ⟶ X) → C ⥤ C)
    (comp : ∀ f h : X ⟶ X, P (f ≫ h) ≅ P h ⋙ P f)
    (M : C) (θ : (P g).obj M ≅ M) :
    (n : ℕ) → (P (localPositivePower g n)).obj M ≅ M
  | 0 => θ
  | n + 1 => (comp (localPositivePower g n) g).app M ≪≫
      (P (localPositivePower g n)).mapIso θ ≪≫ iterateAux g P comp M θ n

/-- Ordered Weil iteration with the existing pullback compositors.
Source: latest blueprint, second paragraph
(blueprint: def-weil-punctual-weights). -/
def iterate {X : Scheme.{u}} (g : X ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (θ : (CondensedRing.upperStar Λ g).obj M ≅ M) (n : ℕ) :
    (CondensedRing.upperStar Λ (localPositivePower g n)).obj M ≅ M :=
  iterateAux g (fun f ↦ CondensedRing.upperStar Λ f)
    (fun f h ↦ CondensedRing.upperStarComp Λ f h) M θ n

/-- The n+1-fold local return at a geometric point, including its reparametrization.
Source: Deligne, Weil II, (1.1.8); blueprint local Frobenius convention
(blueprint: def-weil-punctual-weights). -/
@[irreducible] def localReturn (l : ℕ) [Fact l.Prime]
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (g : X ⟶ X) (s : Spec (.of K) ⟶ Spec (.of K))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X))
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M ≅ M)
    (z : Spec (.of K) ⟶ X) (n : ℕ)
    (h : z ≫ localPositivePower g n = localPositivePower s n ≫ z) :
    End ((CondensedQbarGeometricEvaluation.fieldFiber K l).obj
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)) :=
  evaluateModuleReturn (CondensedQbarGeometricEvaluation.fieldFiber K l)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower s n))
    (pointInsertion l K (localPositivePower s n)).hom
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)
    (moduleReturnMap (Profinite.padicAlgClRingObj l)
      (localPositivePower g n) (localPositivePower s n) M
      (iterate (Profinite.padicAlgClRingObj l) g M θ n).hom z h)

/-- A Weil module has its actual module sheaf and its actual Frobenius isomorphism.
Source: Deligne, Weil II, (1.1.7)
(blueprint: def-weil-punctual-weights). -/
abbrev WeilModule (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :=
  CategoryTheory.Endofunctor.IsoAlgebra
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (D.geometricFrobenius X₀).hom)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The actual scalar stalk at a specified geometric lift of a closed point.
Source: blueprint local Frobenius convention
(blueprint: def-weil-punctual-weights). -/
def closedFiber (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :=
  (CondensedQbarGeometricEvaluation.fieldFiber D.k l).obj
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localClosedPoint D X₀ x i hi)).obj M.carrier)

/-- The canonical local operator on the actual scalar stalk.
Source: Deligne, Weil II, (1.1.8); blueprint local Frobenius convention
(blueprint: def-weil-punctual-weights). -/
@[irreducible] def closedOperator (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    End (closedFiber D l X₀ M x i hi) :=
  localReturn l D.k (D.geometricFrobenius X₀).hom (frobeniusPointIso D).hom
    M.carrier M.str (localClosedPoint D X₀ x i hi) (localClosedPointDegree D X₀ x - 1)
    (localClosedPoint_return D X₀ x i hi)

/-- Punctual purity uses every geometric lift and the actual local return spectrum.
Source: Deligne, Weil II, (1.2); blueprint punctual purity convention
(blueprint: def-weil-punctual-weights). -/
def Pure (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : PadicAlgCl l),
    Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
      ‖iota α‖ = (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (w / 2)

/-- Finite constructible Weil filtrations with punctual pure successive quotients.
Source: Deligne, Weil II (1.2), mixed-weight filtration
(blueprint: def-weil-punctual-weights). -/
def Mixed (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w : ℝ) : Prop :=
  ∃ (m : ℕ) (G : Fin (m + 1) → WeilModule D l X₀)
    (φ : ∀ i : Fin m, G i.castSucc ⟶ G i.succ),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left (G i).carrier) ∧
    IsZero (G 0) ∧ Nonempty (G (Fin.last m) ≅ M) ∧ (∀ i : Fin m, Mono (φ i)) ∧
      ∀ i : Fin m, ∃ v : ℝ, v ≤ w ∧ Pure D l X₀ (cokernel (φ i)) iota v

end WeilConjectures.CondensedWeil
