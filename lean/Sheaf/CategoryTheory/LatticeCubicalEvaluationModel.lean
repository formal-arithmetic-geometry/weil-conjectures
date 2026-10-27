/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.LatticeCubicalEvaluationCore

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedActionTensor
public import Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Products


/-! # Normalized cubical model and coordinate maps

Source: current blueprint, direct-images proof, paragraph (3), agent lattice expansion
(blueprint: def-sfb-lattice-cubical-model).

All existential data below are pinned by coproduct coordinates, action, boundary and
local evaluation formulas. No object is chosen from the concluding existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.CondensedBar
open CategoryTheory.CondensedDerivedRestriction
namespace Profinite.DiscreteLattice.CubicalEvaluation

variable (A : CondensedBar.Ring.{u}) (r : ℕ)

section

-- Use the canonical instances directly in these definitions, avoiding alias conversions.
attribute [-instance] sheafMonoidal latticeTopologicalGroup moduleMonoidal
attribute [local semireducible] total bicomplex

/-- The normalized equivariant cubical complex and its underlying integral contraction.
Every injection has source the regular module, and the cofan universal property specifies
exactly the direct sum in the node. Contraction is only required after forgetting action.
Source: paragraph (3) (blueprint: def-sfb-lattice-cubical-model). -/
structure CubicalModel where
  L : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ
  ι : ∀ n : ℤ, Cells r (-n) → (𝟙_ (CondensedBar.Modules A) ⟶ (L.X n).module)
  coproduct : ∀ n : ℤ, IsColimit (Cofan.mk (L.X n).module (ι n))
  boundary : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ (L.d n (n + 1)).val =
      ∑ i ∈ I, ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card) •
        (cell A r L ι (n + 1) (v + IntegralLatticeCubical.unitVector r i) (I.erase i) -
          cell A r L ι (n + 1) v (I.erase i))
  translation : ∀ (n : ℤ) (v w : Fin r → ℤ) (I : Finset (Fin r))
      (S : Profinite.{u}) (x : sections A (𝟙_ (CondensedBar.Modules A)) S),
    ((L.X n).act S (ContinuousMap.const S (vector w))).toFun
        ((cell A r L ι n v I).hom.hom.app (op S) x) =
      (cell A r L ι n (v + w) I).hom.hom.app (op S) x
  ε : L ⟶ HomologicalComplex.tensorUnit _ (.up ℤ)
  augmentation : ∀ v : Fin r → ℤ,
    cell A r L ι 0 v ∅ ≫ (ε.f 0).val ≫ (unitComparison A r).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom = 𝟙 _
  s : HomologicalComplex.tensorUnit (CondensedBar.Modules A) (.up ℤ) ⟶
    (forgetComplex A r).obj L
  sectionOrigin : s.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (CondensedBar.Modules A))).hom ≫
      cell A r L ι 0 0 ∅
  retraction : s ≫ (forgetComplex A r).map ε ≫ (unitComparison A r).hom = 𝟙 _
  contraction : Homotopy (𝟙 ((forgetComplex A r).obj L))
    ((forgetComplex A r).map ε ≫ (unitComparison A r).hom ≫ s)
  integral : ∀ a : ℤ,
    IntegralLatticeCubical.Chains r a →ₗ[ℤ] IntegralLatticeCubical.Chains r (a + 1)
  integralIdentity : ∀ (a : ℤ) (_ : 0 ≤ a) (x : IntegralLatticeCubical.Chains r a),
    IntegralLatticeCubical.incomingBoundary r a (integral a x) +
      LinearEquiv.cast (R := ℤ) (M := IntegralLatticeCubical.Chains r)
        (sub_add_cancel a 1)
          (integral (a - 1) (IntegralLatticeCubical.boundary r a x)) =
      x - IntegralLatticeCubical.originProjection r a x
  integralCoefficients : ∀ (n : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)),
    cell A r L ι n v I ≫ contraction.hom n (n - 1) =
      (integral (-n) (IntegralLatticeCubical.cell r (-n) v I)).sum
        (fun c m ↦ m • cell A r L ι (n - 1) c.1 c.2.val)

/-- The invariant complex with the normalized invariant-submodule inclusion.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def invariantComplex :=
  (CondensedDerivedRestriction.invariants A (D r)).functor.mapHomologicalComplex (.up ℤ)

/-- The actual invariant inclusion, obtained from the recorded normalized adjunction.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def invariantInclusion : invariantComplex A r ⋙ trivialComplex A r ⟶ 𝟭 _ :=
  (CondensedDerivedRestriction.invariants A (D r)).adjunction.counit.mapHomologicalComplex (.up ℤ)

/-- The inclusion of the (a,b) Koszul/input summand into the prescribed total.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def summand (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (P : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ) (a b : ℤ) :
    (K.functor.obj (B.equivalence.functor.obj (P.X b))).X a ⟶
      ((total A r B K).obj P).X (a + b) :=
  (bicomplex A r B K P).ιTotal (.up ℤ) a b (a + b) rfl

/-- Include a local cubical tensor summand in the total tensor complex.
All tensor comparisons are those of the recorded ordinary diagonal action tensor.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def tensorCell (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (C : CubicalModel A r) (P : CochainComplex (CondensedBar.Equivariant A (D r)) ℤ)
    (a b k n : ℤ) (hn : a + b + -k = n) (v : Fin r → ℤ) (I : Finset (Fin r)) :
    (K.functor.obj (B.equivalence.functor.obj (P.X b))).X a ⊗
        𝟙_ (CondensedBar.Modules A) ⟶
      ((HomologicalComplex.tensorObj
        ((trivialComplex A r).obj ((total A r B K).obj P)) C.L).X n).module :=
  (summand A r B K P a b ⊗ₘ cell A r C.L C.ι (-k) v I) ≫
    ((actionTensor A (D r)).forgetCore.μIso
      (((trivialComplex A r).obj ((total A r B K).obj P)).X (a + b))
      (C.L.X (-k))).hom ≫
    (HomologicalComplex.ιTensorObj
      ((trivialComplex A r).obj ((total A r B K).obj P)) C.L (a + b) (-k) n hn).val

/-- The specified unscaled action on the I-th Koszul coordinate.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def coordinateAction (B : DiscreteComparison A r) (K : KoszulModel A.toMon r)
    (P : CondensedBar.Equivariant A (D r)) (a : ℤ) (I : Subsets r a)
    (v : Fin r → ℤ) :
    (K.functor.obj (B.equivalence.functor.obj P)).X a ⟶ P.module :=
  (K.coordinates _ a).hom ≫ biproduct.π _ I ≫
    (B.equivalence.functor.obj P).ρ (Multiplicative.ofAdd v) ≫ B.underlying.hom.app P

/-- Internal equivariant Hom, obtained by invariants of the diagonal closed Hom.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
abbrev equivariantHom (M N : CondensedBar.Equivariant A (D r)) :=
  (CondensedDerivedRestriction.invariants A (D r)).functor.obj ((ihom M).obj N)

/-- Evaluation on an invariant internal-Hom section, with argument placed on the right.
Source: paragraph (3) (blueprint: lem-sfb-lattice-cubical-augmentation-evaluation). -/
def homEvaluation (M N : CondensedBar.Equivariant A (D r)) :
    ((CondensedAction.trivial (R := A.toMon) (P := D r)).obj
      (equivariantHom A r M N)) ⊗ M ⟶ N :=
  ((CondensedDerivedRestriction.invariants A (D r)).adjunction.counit.app ((ihom M).obj N)) ▷ M ≫
    (β_ ((ihom M).obj N) M).hom ≫ (ihom.ev M).app N


end

end Profinite.DiscreteLattice.CubicalEvaluation
