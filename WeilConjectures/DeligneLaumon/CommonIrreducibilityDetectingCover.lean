/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedWeilModules
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.CategoryTheory.Galois.GaloisTransitive
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.FibreFunctorBasepointTransport
import WeilConjectures.RepresentationTheory.FiniteMatrixWitness
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiberEquivalence

/-! # A common finite cover detecting geometric irreducibility

Source: latest blueprint, sec-deligne-laumon-general/sk-cor-wgen-bertini-irreducible,
lem-zl-curve-testing-irreducibility.proof.md, sentences 1--6 and 8--10
(blueprint: lem-zl-common-irreducibility-detecting-cover).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- One connected finite etale cover detects irreducibility for the whole finite family.
Irreducibility is expanded as nonzero with no proper nonzero lisse submodule; no condition
is imposed on the Weil structure of a geometric submodule.

Source: latest blueprint, lem-zl-curve-testing-irreducibility.proof.md, sentences 1--6
and 8--10 (blueprint: lem-zl-common-irreducibility-detecting-cover).

Proof plan:
1. The geometric base is connected, smooth, affine, finite type and regular. Choose a
geometric point. The exact equivalence lem-a1-condensed-lisse-monodromy identifies the
actual condensed lisse modules with irreducible geometric representations. Choose one
finite coefficient extension E for the finite family (E = Q_l for the empty family).
2. Apply lem-zl-finite-matrix-irreducibility to obtain stable O_E-lattices and finite
reduction witnesses, with exponents at least one.
3. By lem-weil-l-adic-extension-integers-dvr and lem-weil-valued-dvr-finite-quotients,
these reductions are finite. The coset basis lem-sfb-integers-coset-basis makes their
kernels open normal subgroups.
4. Intersect the finitely many kernels. The resulting quotient Q is finite and each
reduction action factors through it. For the empty family Q is the trivial group.
5. Realize this open subgroup by cor-galois-open-subgroups. By lem-fet-galois-category,
lem-galois-finite-etale-connected-object and lem-galois-transitive, its connected finite
etale cover T has fibre the regular Q-set.
6. For a curve C and immersion i, transport the basepoint using the finite-fibre part of
lem-wf-fibre-functor-basepoint-transport. By thm-galois-fundamental, the pulled-back cover
has fibre Q with the induced action. The same path and pullback identifications in
lem-a1-condensed-lisse-monodromy identify the restricted geometric representations.
7. If T times_X C is connected, the same Galois connectedness and transitivity statements
make pi_1(C) transitive on Q. Its orbit of 1 is its image, so it surjects onto Q.
8. Thus its image agrees with pi_1(X) on every reduction witness. Apply the finite-matrix
lemma and the exact condensed monodromy equivalence to conclude that every i^* S_j is
an irreducible lisse module. The one cover works for every stated C and i. -/
theorem exists_common_irreducibility_detecting_cover
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [IsAffine X₀.left]
    (d : ℕ) (hd : 1 ≤ d) [SmoothOfRelativeDimension d X₀.hom]
    [GeometricallyConnected X₀.hom] :
    letI : Smooth X₀.hom := SmoothOfRelativeDimension.smooth d X₀.hom
    ∀ (r : ℕ)
    (S : Fin r → condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (hL : ∀ j, IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) (S j).carrier)
    (hNZ : ∀ j, ¬ IsZero (S j).carrier)
    (hI : ∀ j
      (A : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber X₀).left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left))
      (a : A ⟶ (S j).carrier), Mono a →
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) A → IsZero A ∨ IsIso a),
    ∃ (T : Scheme.{u}) (π : T ⟶ (D.geometricFiber X₀).left),
      ConnectedSpace T ∧ IsFinite π ∧ Etale π ∧
      ∀ (C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left) [IsAffine C]
        [SmoothOfRelativeDimension 1 (i ≫ (D.geometricFiber X₀).hom)]
        [ConnectedSpace C] [IsClosedImmersion i],
        ConnectedSpace ↑(pullback π i) → ∀ j,
          IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) i).obj (S j).carrier) ∧
          ¬ IsZero
            ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) i).obj (S j).carrier) ∧
          ∀ (A : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
              (condensedRingObj (Profinite.padicAlgClRingObj l) C))
            (a : A ⟶
              (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) i).obj (S j).carrier),
            Mono a → IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) A →
              IsZero A ∨ IsIso a := by
  sorry

end WeilConjectures
