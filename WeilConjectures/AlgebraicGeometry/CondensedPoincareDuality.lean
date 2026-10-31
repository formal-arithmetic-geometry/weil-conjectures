/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedPoincareTraceCup
public import WeilConjectures.AlgebraicGeometry.GeometricHypotheses
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CondensedConstantGlobalFrobenius
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted

import WeilConjectures.CategoryTheory.NaturalTransportPowers
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Poincare duality for smooth proper schemes with condensed Q_ell coefficients

Source: latest blueprint, sec-poincare-duality/sk-thm-poincare-duality/
thm-weil-poincare-duality.md (blueprint: thm-weil-poincare-duality).

The groups, products, traces and pullbacks below use the actual pulled-back condensed
coefficient ring. Finite field extension uses the canonical map of geometric fibers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedPoincare

/-- Smoothness and pure dimension give relative dimension d on the geometric fiber.
Source: the smooth proper geometric hypotheses (blueprint: thm-weil-poincare-duality).
Proof: smoothness is stable under field extension. At every geometric point the
relative dimension is the dimension of its smooth component. All components have
dimension d by the stated pure-dimension hypothesis; hence the locally constant
relative-dimension function is constantly d. -/
theorem fiber_smooth (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] (d : ℕ)
    (h : D.IsSmoothOfPureDimension X₀ d) :
    SmoothOfRelativeDimension d (D.geometricFiber X₀).hom := by
  sorry

/-- Properness is preserved by the specified geometric base change.
Source: the proper geometric fiber (blueprint: thm-weil-poincare-duality). -/
instance fiber_proper (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] :
    IsProper (D.geometricFiber X₀).hom := by
  dsimp [WeilConjectures.FiniteFieldDatum.geometricFiber]
  infer_instance

/-- The actual structure morphism, supplied with its identity-open compactification.
Source: X = X_0 times k and a_X (blueprint: thm-weil-poincare-duality). -/
def geometry (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] (d : ℕ)
    (h : D.IsSmoothOfPureDimension X₀ d) : SmoothDatum D := by
  let X := D.geometricFiber X₀
  letI : IsProper X.hom := by
    dsimp [X, WeilConjectures.FiniteFieldDatum.geometricFiber]
    infer_instance
  letI := fiber_smooth D X₀ d h
  exact { X := X
          Y := Over.mk (𝟙 (Spec (.of D.k)))
          yFinite := by change LocallyOfFiniteType (𝟙 _); infer_instance
          yQuasiCompact := by change QuasiCompact (𝟙 _); infer_instance
          ySeparated := by change IsSeparated (𝟙 _); infer_instance
          map := X.hom
          isOver := ⟨by change X.hom ≫ 𝟙 _ = X.hom; simp⟩
          dim := d
          compactification := Compactification.ofIsProper X.hom }

/-- Properness of the actual geometric-fiber structure morphism.
Source: proper base change of X_0 (blueprint: thm-weil-poincare-duality). -/
instance geometry_proper (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] (d : ℕ)
    (h : D.IsSmoothOfPureDimension X₀ d) : IsProper (geometry D X₀ d h).map := by
  dsimp [geometry, WeilConjectures.FiniteFieldDatum.geometricFiber]
  infer_instance

/-- Base change of the model to a finite intermediate extension of the fixed closure.
Source: X_0' in the base-change clause (blueprint: thm-weil-poincare-duality). -/
def extendedModel (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (L : IntermediateField D.k₀ D.k) :
    Over (Spec (.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ L)))).obj X₀

/-- The iterated geometric fiber over the same fixed closure.
Source: X' = (X_0 times L) times_L k (blueprint: thm-weil-poincare-duality). -/
def extendedFiber (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (L : IntermediateField D.k₀ D.k) :
    Over (Spec (.of D.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L D.k)))).obj (extendedModel D X₀ L)

/-- Properness of the iterated geometric base change.
Source: the proper extended geometric fiber (blueprint: thm-weil-poincare-duality). -/
instance extendedFiber_proper (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) : IsProper (extendedFiber D X₀ L).hom := by
  dsimp [extendedFiber, extendedModel]
  infer_instance

/-- The canonical geometric-fiber identification map, before applying cohomology.
Its projections send ((x,b),c) to (x,bc), in affine tensor coordinates.
Source: the specified pullback X' -> X (blueprint: thm-weil-poincare-duality). -/
def fiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) :
    (extendedFiber D X₀ L).left ⟶ (D.geometricFiber X₀).left := by
  dsimp only [extendedFiber, extendedModel,
    WeilConjectures.FiniteFieldDatum.geometricFiber, Over.pullback, Over.mk_hom]
  exact pullback.lift
    (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc, pullback.condition]
      simp only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        IsScalarTower.algebraMap_eq D.k₀ L D.k])

/-- Geometric Frobenius of the extended finite-field model, on its actual fiber.
Source: F' in the base-change clause (blueprint: thm-weil-poincare-duality). -/
def extendedFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (L : IntermediateField D.k₀ D.k) [Finite L] :
    (extendedFiber D X₀ L).left ⟶ (extendedFiber D X₀ L).left :=
  letI := Fintype.ofFinite L
  let σ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic L D.k
  AlgebraicGeometry.baseChangeMap (extendedModel D X₀ L).hom
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L D.k))))
    (T' := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L D.k))))
    (Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L D.k)) =
          Spec.map (CommRingCat.ofHom (algebraMap L D.k))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact σ.commutes x))

/-- The finite-extension fiber identification respects the structure map.
Source: the canonical geometric-fiber pullback (blueprint: thm-weil-poincare-duality).
Proof: compose the defining pullback lift with its second projection. -/
theorem fiberMap_over (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) :
    fiberMap D X₀ L ≫ (D.geometricFiber X₀).hom = (extendedFiber D X₀ L).hom := by
  sorry

/-- Associativity of geometric base change makes the specified map an isomorphism.
Source: finite-extension base change (blueprint: thm-weil-poincare-duality).
Proof: the inverse pullback lift first inserts the unit of L in the model base change,
then retains the k coordinate. Pullback uniqueness proves both inverse identities. -/
theorem fiberMap_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) : IsIso (fiberMap D X₀ L) := by
  sorry

/-- The geometric field Frobenius gives the required semilinear structure square.
Source: the geometric convention (blueprint: thm-weil-poincare-duality).
Proof: the second projection of the defining base-change lift is the second
projection followed by Spec of inverse q-power Frobenius. -/
theorem frobenius_over (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] :
    (D.geometricFrobenius X₀).hom ≫ (D.geometricFiber X₀).hom =
      (D.geometricFiber X₀).hom ≫ (CondensedRing.StrictWeil.pointFrobenius D).hom := by
  sorry

/-- The extended-model Frobenius is an isomorphism, with inverse arithmetic Frobenius.
Source: the extended finite-field model (blueprint: thm-weil-poincare-duality).
Proof: use the same pullback lift with inverse field automorphism. Base-change
functoriality and the two field inverse identities prove the scheme inverse identities. -/
theorem extendedFrobenius_isIso (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (L : IntermediateField D.k₀ D.k) [Finite L] :
    IsIso (extendedFrobenius D X₀ L) := by
  sorry

/-- The coefficient-point Frobenius of the extended model.
Source: Spec of inverse card(L)-power Frobenius
(blueprint: thm-weil-poincare-duality). -/
def extendedPoint (D : WeilConjectures.FiniteFieldDatum.{u})
    (L : IntermediateField D.k₀ D.k) [Finite L] : Aut (Spec (.of D.k)) :=
  letI := Fintype.ofFinite L
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic L D.k).toRingEquiv.toCommRingCatIso.op

/-- The semilinear square for the extended model.
Source: extended-model Frobenius (blueprint: thm-weil-poincare-duality).
Proof: apply the second-projection equation for baseChangeMap. -/
theorem extendedFrobenius_over (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) (L : IntermediateField D.k₀ D.k) [Finite L] :
    extendedFrobenius D X₀ L ≫ (extendedFiber D X₀ L).hom =
      (extendedFiber D X₀ L).hom ≫ (extendedPoint D L).hom := by
  sorry

/-- Canonical complex-level pullback along an isomorphism square, on the coefficient unit.
Source: the base-change map on RΓ in the final clause
(blueprint: thm-weil-poincare-duality). -/
def complexPull (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (a : Y ⟶ Spec (.of k)) (a' : X ⟶ Spec (.of k))
    [QuasiCompact a'] (b : Spec (.of k) ⟶ Spec (.of k)) [IsIso b]
    (f : X ⟶ Y) [IsIso f] (w : f ≫ a = a' ≫ b) :=
  CondensedRing.CohomologyTransport.t (ring.{u} ell) a a' b f w (unit ell Y) ≫
    (CondensedRing.CohomologyTransport.Γ (ring.{u} ell) (Spec (.of k))).map
      ((CondensedRing.lowerStar (ring.{u} ell) a').rightDerivedFunctor.map
        (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) f).hom)

/-- The actual global geometric Frobenius of the constant coefficient complex.
Source: F on RΓ(X,K_X) (blueprint: thm-weil-poincare-duality). -/
def globalFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom] :=
  WeilConjectures.CondensedConstant.globalOrdinary (ring.{u} ell) D.k (D.geometricFiber X₀).hom
    (D.geometricFrobenius X₀).hom (CondensedRing.StrictWeil.pointFrobenius D).hom
    (frobenius_over D X₀) (unit ell (D.geometricFiber X₀).left)
    (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) (D.geometricFrobenius X₀).hom)

/-- The canonical geometric-fiber pullback, on actual ordinary coefficient complexes.
Source: the specified RΓ base-change arrow (blueprint: thm-weil-poincare-duality). -/
def globalFiberPull (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) :=
  letI := fiberMap_isIso D X₀ L
  complexPull ell D.k (D.geometricFiber X₀).hom (extendedFiber D X₀ L).hom
    (𝟙 _) (fiberMap D X₀ L) (by simpa using fiberMap_over D X₀ L)

/-- A finite-dimensional intermediate extension of the finite base field is finite.
Source: finite extension convention (blueprint: thm-weil-poincare-duality). -/
instance finiteIntermediate (D : WeilConjectures.FiniteFieldDatum.{u})
    (L : IntermediateField D.k₀ D.k) [FiniteDimensional D.k₀ L] : Finite L :=
  Module.finite_of_finite D.k₀

/-- The actual global Frobenius of the extended constant coefficient complex.
Source: F' on RΓ(X',K_X') (blueprint: thm-weil-poincare-duality). -/
def globalExtendedFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    (L : IntermediateField D.k₀ D.k) [Finite L] :=
  letI := extendedFrobenius_isIso D X₀ L
  WeilConjectures.CondensedConstant.globalOrdinary (ring.{u} ell) D.k (extendedFiber D X₀ L).hom
    (extendedFrobenius D X₀ L) (extendedPoint D L).hom
    (extendedFrobenius_over D X₀ L) (unit ell (extendedFiber D X₀ L).left)
    (CondensedRing.leftDerivedUpperStarUnitIso (ring.{u} ell) (extendedFrobenius D X₀ L))

/-- Algebraic eigenvalue multiplicity, computed after scalar extension to the chosen closure.
For a finite-dimensional space this is the dimension of the full generalized eigenspace.
Source: reciprocity with multiplicity (blueprint: thm-weil-poincare-duality). -/
def multiplicity {ell : ℕ} [Fact ell.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic ell) Ω] {V : Type (u + 1)} [AddCommGroup V] [Module (Padic ell) V]
    (f : Module.End (Padic ell) V) (α : Ω) : ℕ :=
  Module.finrank Ω (Module.End.genEigenspace (f.baseChange Ω) α ⊤)

/-- Poincare duality for the specified constant condensed Weil sheaf.

Source: latest blueprint thm-weil-poincare-duality.md, clauses Trace through Base change
(blueprint: thm-weil-poincare-duality).

Proof plan:
1. The constant coefficient unit is perfect of Tor interval [0,0] and self-dual
   (def-sf-setting, sk-def-sf-weil-complexes, def-pod-dual-tate-datum).
2. Cohomological finiteness and proper comparison give finite-dimensionality and
   support [0,2d] (prop-cohomological-finiteness). Connectedness identifies H^0 with
   the coefficient field. The chosen orientation differs from the normalized one
   by a nonzero scalar, so sk-cor-trace gives the specified top trace isomorphism.
3. Apply thm-pod-proper-poincare-duality and
   thm-pod-degreewise-perfectness-over-a-field to the unit. Their pairing is cup
   followed by the specified counit trace (sk-def-pairing), hence gives both
   bijective adjoints and the line-valued duality equivalence.
4. cor-pod-untwisted-similitude and lem-fix-weil-operations identify the actual
   root-normalized value-line action with q^d and give the simultaneous Frobenius
   formula. The adjoint is therefore equivariant for the twisted contragredient.
5. sk-thm-frobenius gives reciprocal eigenvalues, and scalar transport
   (sk-prop-scalar-six, sk-thm-transport) gives their algebraic multiplicities in
   the chosen algebraic closure, computed by full generalized eigenspaces.
6. The affine tensor associativity map identifies the geometric fibers. A basis
   counts the extended field as q^r. Geometric field Frobenius is the r-th iterate
   (def-weil-frobenius-detailed); normalized cohomology transport composes
   (lem-weil-condensed-isomorphism-cohomology-transport, lem-weil-pbc-mate-pasting,
   lem-trf-global-frobenius-iterate-formula). It preserves cup and the transported
   counit trace. Thus the pulled-back pairings stay perfect, and iteration of
   Step 4 gives multiplier (q^r)^d.

The orientation is an isomorphism from the recorded native constructible exceptional
unit to the actual shifted Tate line. Normalized line-pull coordinates are constructed
from the canonical root, tensor and unit comparisons.
-/
theorem poincareDuality (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic ell) Ω] [IsAlgClosure (Padic ell) Ω]
    (X₀ : Over (Spec (.of D.k₀))) [IsProper X₀.hom]
    [GeometricallyConnected X₀.hom] (d : ℕ)
    (hSmooth : D.IsSmoothOfPureDimension X₀ d)
    (η : exceptionalUnit (geometry D X₀ d hSmooth) hEll ≅
      Coefficient.rationals.derivedLine ell (D.geometricFiber X₀).left d)
    :
    ∃ (A : ∀ i : ℤ, cohomology ell (D.geometricFiber X₀).left i ≃ₗ[Padic ell]
        cohomology ell (D.geometricFiber X₀).left i)
      (tr : cohomology ell (D.geometricFiber X₀).left (2 * (d : ℤ)) →ₗ[Padic ell]
        valueLine ell (Spec (.of D.k)) d)
      (B : ∀ (i j : ℤ), i + j = 2 * (d : ℤ) →
        cohomology ell (D.geometricFiber X₀).left i →ₗ[Padic ell]
          cohomology ell (D.geometricFiber X₀).left j →ₗ[Padic ell]
            valueLine ell (Spec (.of D.k)) d),
      (∀ i x, A i x = pull ell (D.geometricFrobenius X₀).hom i x) ∧
      (∀ x, tr x = untwistedTrace (geometry D X₀ d hSmooth) hEll η
        (normalizedCoordinates ell D hEll (D.geometricFiber X₀).hom (𝟙 _)
          (geometry D X₀ d hSmooth).map) x) ∧
      (∀ i j h x y, B i j h x y = pairing (geometry D X₀ d hSmooth) hEll η
        (normalizedCoordinates ell D hEll (D.geometricFiber X₀).hom (𝟙 _)
          (geometry D X₀ d hSmooth).map) i j h x y) ∧
      Function.Bijective tr ∧
      (∀ i : ℤ, FiniteDimensional (Padic ell) (cohomology ell (D.geometricFiber X₀).left i)) ∧
      (∀ i : ℤ, i < 0 ∨ 2 * (d : ℤ) < i →
        Subsingleton (cohomology ell (D.geometricFiber X₀).left i)) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * (d : ℤ)), 0 ≤ i → i ≤ 2 * (d : ℤ) →
        Function.Bijective (B i j h) ∧ Function.Bijective (B i j h).flip) ∧
      (∀ z : valueLine ell (Spec (.of D.k)) d,
        pointValueFrobenius ell D hEll d z =
          (D.q : Padic ell) ^ d • z) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * (d : ℤ)), 0 ≤ i → i ≤ 2 * (d : ℤ) →
        ∀ x y, B i j h (A i x) (A j y) = (D.q : Padic ell) ^ d • B i j h x y) ∧
      (∀ (i j : ℤ) (h : i + j = 2 * (d : ℤ)),
        (∃ e : cohomology ell (D.geometricFiber X₀).left j ≃ₗ[Padic ell]
            (cohomology ell (D.geometricFiber X₀).left i →ₗ[Padic ell]
              valueLine ell (Spec (.of D.k)) d),
          (∀ y x, e y x = B i j h x y) ∧
          (∀ y x, e (A j y) (A i x) =
            pointValueFrobenius ell D hEll d (e y x))) ∧
        (∀ α : Ω, multiplicity Ω (A j).toLinearMap α =
          multiplicity Ω (A i).toLinearMap ((D.q : Ω) ^ d / α))) ∧
      (∀ (L : IntermediateField D.k₀ D.k) [FiniteDimensional D.k₀ L],
        Nat.card L = D.q ^ Module.finrank D.k₀ L ∧
        (globalFiberPull D ell X₀ L ≫ globalExtendedFrobenius D ell X₀ L =
          ((End.of (globalFrobenius D ell X₀)) ^ (Module.finrank D.k₀ L)) ≫
            globalFiberPull D ell X₀ L) ∧
        ∃ (C : ∀ i : ℤ, cohomology ell (D.geometricFiber X₀).left i ≃ₗ[Padic ell]
            cohomology ell (extendedFiber D X₀ L).left i)
          (B' : ∀ (i j : ℤ), i + j = 2 * (d : ℤ) →
            cohomology ell (extendedFiber D X₀ L).left i →ₗ[Padic ell]
              cohomology ell (extendedFiber D X₀ L).left j →ₗ[Padic ell]
                valueLine ell (Spec (.of D.k)) d),
          (∀ i x, C i x = pull ell (fiberMap D X₀ L) i x) ∧
          (∀ i x, C i (((A i) ^ Module.finrank D.k₀ L) x) =
            pull ell (extendedFrobenius D X₀ L) i (C i x)) ∧
          (∀ i j h x y, B' i j h (C i x) (C j y) = B i j h x y) ∧
          (∀ (i j : ℤ) (h : i + j = 2 * (d : ℤ)), 0 ≤ i → i ≤ 2 * (d : ℤ) →
            Function.Bijective (B' i j h) ∧ Function.Bijective (B' i j h).flip) ∧
          (∀ (i j : ℤ) (h : i + j = 2 * (d : ℤ)), 0 ≤ i → i ≤ 2 * (d : ℤ) →
            ∀ x y, B i j h (((A i) ^ Module.finrank D.k₀ L) x)
                (((A j) ^ Module.finrank D.k₀ L) y) =
              ((D.q : Padic ell) ^ Module.finrank D.k₀ L) ^ d • B i j h x y)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedPoincare
