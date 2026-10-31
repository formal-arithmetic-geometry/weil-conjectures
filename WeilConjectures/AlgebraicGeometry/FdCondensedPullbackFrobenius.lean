/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFibresExact
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficients
public import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
import WeilConjectures.AlgebraicGeometry.CondensedPullbackPowerTransport
import WeilConjectures.AlgebraicGeometry.PullbackConstantModelConstructible
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Basic

/-! # Residue-degree Frobenius for condensed coefficient pullback

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1 and 2
(blueprint: lem-fd-condensed-pullback-frobenius).

All fibres are sections of actual condensed module inverse images. The coefficients are
finite-subextension-valued continuous functions. The scalar field is the standard lift
`ULift (PadicAlgCl l)` used by the existing fibre functor, with its canonical ring equivalence
with `PadicAlgCl l`. The comparison below is the specified pullback compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Evaluate the canonical square comparison and then pull back the Weil isomorphism.
Keeping this elementary composition abstract avoids expanding the concrete module category.
Source: latest blueprint, Step 2, induced Weil structure on pullback
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdEvaluateWeilPullback {C : Type v} [Category.{w} C]
    {E : Type v'} [Category.{w'} E] (L : C ⥤ E) (G : C ⥤ C) (H : E ⥤ E)
    (e : L ⋙ H ≅ G ⋙ L) (M : C) (θ : G.obj M ≅ M) :
    H.obj (L.obj M) ≅ L.obj M :=
  e.app M ≪≫ L.mapIso θ

/-- The canonical Weil isomorphism on ordinary coefficient pullback along a square.
Its comparison is the inverse existing square comparison, followed by inverse image
of the given Weil isomorphism. The theorem specializes the square to geometric Frobenius.
Source: latest blueprint, kernel pullback in Step 1 and residue-degree formula in Step 2
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdCondensedPullbackWeilIso (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (sq : CommSq gX f f gY) (M : CondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) gY).obj M ≅ M) :=
  fdEvaluateWeilPullback
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) gY)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) gX)
    (CondensedRing.upperStarSquareComparison (Profinite.padicAlgClRingObj l)
      (g' := gX) (f' := f) (f := f) (g := gY) sq).symm M θ

/-- The canonical geometric-fibre comparison: inverse of the composition isomorphism,
then transport through compatibility of the two chosen geometric points, then sections.
Source: latest blueprint, Step 2, pullback along the first projection
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdCondensedFibreComparison (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x)
    (M : CondensedModule.Modules l Y) :
    CondensedModule.fibre l D
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) z ≅
      CondensedModule.fibre l D M x :=
  (CondensedRing.pointSections l D.k).mapIso
    ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).symm.app M ≪≫
      (CondensedRing.upperStarCongr (Profinite.padicAlgClRingObj l) h).app M)

/-- Intertwining for the specified comparison and the eigenvalue multiset with algebraic
multiplicities. Finite-dimensionality is asserted, not assumed; it supplies the instances
needed for the characteristic polynomials. The zero-dimensional case has empty root multisets.
Source: latest blueprint, Step 2, the multiset E and its residue-degree powers
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdCondensedSpectrumAssertions {K : Type v} [Field K]
    {M N : ModuleCat.{w} K} (c : M ≅ N) (A : End M) (B : End N) (e : ℕ) : Prop :=
  A ≫ c.hom = c.hom ≫ ModuleCat.ofHom (B.hom ^ e) ∧
    ∃ (_hM : FiniteDimensional K M) (_hN : FiniteDimensional K N),
      A.hom.charpoly.roots = B.hom.charpoly.roots.map (fun α ↦ α ^ e)

/-- The actual fibre comparison, iterated local operators, and their spectrum assertion.
The point-return data are explicit. The theorem below supplies the closed-point degrees
and their canonical semilinear returns, with no extra hypotheses.
Source: latest blueprint, Step 2, residue-degree pullback and eigenvalue multisets
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdCondensedPullbackLocalAssertions (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (sq : CommSq gX f f gY) (M : CondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) gY).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x)
    (nX nY : ℕ)
    (hX : z ≫ localPositivePower gX nX =
      localPositivePower (frobeniusPointIso D).hom nX ≫ z)
    (hY : x ≫ localPositivePower gY nY =
      localPositivePower (frobeniusPointIso D).hom nY ≫ x) (e : ℕ) : Prop :=
  fdCondensedSpectrumAssertions
    (fdCondensedFibreComparison D l f z x h M)
    (CondensedModule.operator l D gX
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
      (fdCondensedPullbackWeilIso l f gX gY sq M θ) z nX hX)
    (CondensedModule.operator l D gY M θ x nY hY) e

/-- The canonical geometric base change, with its geometric-fibre endpoints explicit.
Its data are exactly the existing `Over.pullback` functor applied to the model map.
Source: latest blueprint, Step 2, base-changed first projection
(blueprint: lem-fd-condensed-pullback-frobenius). -/
def fdGeometricBaseChange (D : FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- The local assertion specialized to closed-point lifts and their canonical returns.
This is a definition of the entire displayed assertion, not an additional hypothesis.
Source: latest blueprint, Step 2, closed-point residue-degree Frobenius formula
(blueprint: lem-fd-condensed-pullback-frobenius). -/
@[irreducible] def fdCondensedClosedPullbackAssertions (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) (z : {z : X₀.left // z ∈ closedPoints X₀.left})
    (hx : f₀.left.base z.val ∈ closedPoints Y₀.left)
    (ιz : X₀.left.residueField z.val →+* D.k)
    (hz : ιz.comp (X₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
    (ιx : Y₀.left.residueField (f₀.left.base z.val) →+* D.k)
    (hιx : ιx.comp (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val)) =
      algebraMap D.k₀ D.k)
    (h : localClosedPoint D X₀ z ιz hz ≫
        (fdGeometricBaseChange D X₀ Y₀ f₀) =
      localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx)
    (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀)) : Prop :=
  fdCondensedPullbackLocalAssertions D l
    (fdGeometricBaseChange D X₀ Y₀ f₀)
    (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
    ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩ F.carrier F.str
    (localClosedPoint D X₀ z ιz hz)
    (localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx) h
    (localClosedPointDegree D X₀ z - 1)
    (localClosedPointDegree D Y₀ ⟨f₀.left.base z.val, hx⟩ - 1)
    (localClosedPoint_return D X₀ z ιz hz)
    (localClosedPoint_return D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx)
    (f₀.left.residueDegree z.val)

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.upperStarFromPointMod CondensedRing.upperStarIsoIdOfIsSepClosed
  CondensedRing.pointSections

private theorem fd_pullIso_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (sq : CommSq a f f b) (M : CondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M ≅ M) :
    fdCondensedPullbackWeilIso l f a b sq M θ =
      (pullbackFamilyComparison (c := fun f g ↦ CondensedRing.upperStarComp
        (Profinite.padicAlgClRingObj l) f g) f a b sq.w).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).mapIso θ := by
  apply Iso.ext
  simp only [fdCondensedPullbackWeilIso, fdEvaluateWeilPullback, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    CondensedRing.upperStarSquareComparison, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, eqToIso.inv, eqToHom_app, pullbackFamilyComparison_hom_app,
    Category.assoc]

private theorem fd_fibreComparison_hom (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : Spec (.of D.k) ⟶ X)
    (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x) (M : CondensedModule.Modules l Y) :
    (fdCondensedFibreComparison D l f z x h M).hom =
      (CondensedRing.pointSections l D.k).map
        ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) z f).inv.app M ≫
          eqToHom (congrArg (fun x ↦
            (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) x).obj M) h)) := by
  subst x
  simp only [fdCondensedFibreComparison, Functor.mapIso_hom, Iso.trans_hom,
    Iso.app_hom, Iso.symm_hom, CondensedRing.upperStarCongr_self, Iso.refl_hom,
    NatTrans.id_app, eqToHom_refl, Category.comp_id]

private theorem fd_intertwining_congr {C : Type*} [Category C] {M N : C}
    (A A' : End M) (B : End N) (c c' : M ⟶ N)
    (hA : A = A') (hc : c = c') (h : A' ≫ c' = c' ≫ B) :
    A ≫ c = c ≫ B := by
  subst A' c'
  exact h

private theorem fd_intertwining (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (sq : CommSq a f f b) (M : CondensedModule.Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ X) (x : Spec (.of D.k) ⟶ Y) (h : z ≫ f = x)
    (n d e : ℕ) (hd : 0 < d) (he : 1 ≤ e) (hi : n = e * d - 1)
    (ha : z ≫ localPositivePower a n = localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (hb : x ≫ localPositivePower b (d - 1) =
      localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ x) :
    CondensedModule.operator l D a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M)
        (fdCondensedPullbackWeilIso l f a b sq M θ) z n ha ≫
        (fdCondensedFibreComparison D l f z x h M).hom =
      (fdCondensedFibreComparison D l f z x h M).hom ≫
        ModuleCat.ofHom ((CondensedModule.operator l D b M θ x (d - 1) hb).hom ^ e) := by
  subst x
  have hA := congrArg
    (fun θ' ↦ CondensedModule.operator l D a
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f).obj M) θ' z n ha)
    (fd_pullIso_eq l f a b sq M θ)
  exact fd_intertwining_congr _ _ _ _ _ hA (fd_fibreComparison_hom D l f z _ rfl M)
    (condensedPullbackPowerTransport l D f a b sq.w M θ z _ rfl n d e hd he hi ha hb)

private theorem fd_degree_mul (D : FiniteFieldDatum.{u})
    (X₀ Y₀ : Over (Spec (.of D.k₀))) (f₀ : X₀ ⟶ Y₀)
    (z : {z : X₀.left // z ∈ closedPoints X₀.left})
    (hx : f₀.left.base z.val ∈ closedPoints Y₀.left) :
    localClosedPointDegree D X₀ z = f₀.left.residueDegree z.val *
      localClosedPointDegree D Y₀ ⟨f₀.left.base z.val, hx⟩ := by
  let := (X₀.hom.residueFieldAlgebraMap z.val).toAlgebra
  let := (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val)).toAlgebra
  let := (f₀.left.residueFieldMap z.val).hom.toAlgebra
  let : IsScalarTower D.k₀ (Y₀.left.residueField (f₀.left.base z.val))
      (X₀.left.residueField z.val) := IsScalarTower.of_algebraMap_eq' (by
    change X₀.hom.residueFieldAlgebraMap z.val =
      (f₀.left.residueFieldMap z.val).hom.comp
        (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val))
    rw [← Scheme.Hom.residueFieldAlgebraMap_comp, Over.w])
  change Module.finrank D.k₀ (X₀.left.residueField z.val) =
    Module.finrank (Y₀.left.residueField (f₀.left.base z.val))
      (X₀.left.residueField z.val) *
        Module.finrank D.k₀ (Y₀.left.residueField (f₀.left.base z.val))
  rw [mul_comm, Module.finrank_mul_finrank]

private theorem fd_isAlgClosedOfEquiv
    {K L : Type*} [Field K] [Field L] [IsAlgClosed K] (e : K ≃+* L) :
    IsAlgClosed L := by
  refine ⟨fun p ↦ ?_⟩
  have h := (IsAlgClosed.splits (p.map e.symm.toRingHom)).map e.toRingHom
  have he : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    ext n
    simp
  rwa [he] at h

private theorem fd_roots_pow {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (n : ℕ) :
    (f ^ n).charpoly.roots = f.charpoly.roots.map (fun a ↦ a ^ n) := by
  classical
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix f
  rw [← LinearMap.charpoly_toMatrix _ b, ← LinearMap.toMatrix_pow,
    (hb.pow n).charpoly_roots_of_injective Function.injective_id,
    ← LinearMap.charpoly_toMatrix f b,
    hb.charpoly_roots_of_injective Function.injective_id, Multiset.map_map]
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, pow_succ, ← ih]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with hji | hij
      · rw [(hb.pow n) hji, zero_mul]
      · rw [hb hij, mul_zero]
    · simp

private theorem fd_roots_conjugate_power {K : Type*} [Field K] [IsAlgClosed K]
    {M N : ModuleCat.{w} K} [FiniteDimensional K M] [FiniteDimensional K N]
    (e : M ≅ N) (f : M ⟶ M) (g : N ⟶ N) (n : ℕ)
    (h : f ≫ e.hom = e.hom ≫ ModuleCat.ofHom (g.hom ^ n)) :
    f.hom.charpoly.roots = g.hom.charpoly.roots.map (fun a ↦ a ^ n) := by
  have hg : e.toLinearEquiv.conj f.hom = g.hom ^ n := by
    ext x
    have hx := congrArg (fun z : M ⟶ N ↦ z (e.inv x)) h
    simpa using hx
  rw [← LinearEquiv.charpoly_conj e.toLinearEquiv f.hom, hg]
  exact fd_roots_pow g.hom n

private theorem fd_spectrum_of_intertwining {K : Type*} [Field K] [IsAlgClosed K]
    {M N : ModuleCat.{w} K} [FiniteDimensional K M] [FiniteDimensional K N]
    (c : M ≅ N) (A : End M) (B : End N) (e : ℕ)
    (h : A ≫ c.hom = c.hom ≫ ModuleCat.ofHom (B.hom ^ e)) :
    fdCondensedSpectrumAssertions c A B e := by
  exact ⟨h, inferInstance, inferInstance, fd_roots_conjugate_power c A B e h⟩

/-- Exact coefficient pullback preserves constructible Weil modules. The closed image has
positive finite residue degree, the residue cardinalities satisfy the degree formula, and
for every compatible pair of geometric lifts the specified fibre compositor intertwines
local geometric Frobenius with its residue-degree power, with algebraic multiplicities.

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1 and 2
(blueprint: lem-fd-condensed-pullback-frobenius).

Proof: (1) The geometric fibres are qcqs by base change. Apply the existing
constant-model constructibility pullback theorem to the condensed coefficient ring.
(2) The residue field of a closed z is finite over the finite base field. The
residue-field injection makes the residue field of x=f(z) finite too, so x is closed.
The extension is finite and has positive finrank; counting a basis gives q_z=q_x^e.
(3) The composition formula for residue-field algebra maps and the Over-morphism
equation give the scalar tower. The finrank tower law gives deg(z)=e*deg(x).
(4) The geometric Frobenius square commutes by frobenius_square_cartesian. The
existing localClosedPoint_return supplies the two semilinear closed-point returns.
Expanding the square comparison and fibre comparison identifies them with the
pullback-family comparison and the specified inverse compositor, respectively.
(5) Apply condensedPullbackPowerTransport with n=deg(z)-1, d=deg(x), and the positive
residue degree e. Its proved categorical calculation commutes Weil iteration with
pullback and groups returning iterations into d-blocks, giving R_ed=(R_d)^e.
This is the asserted intertwining for exactly fdCondensedFibreComparison.
(6) Both fibres are finite-dimensional by condensed_fibres_exact, applied to F and
to its constructible pullback. Transfer algebraic closedness through the scalar lift.
(7) Conjugation preserves the characteristic polynomial. In a triangularizing basis,
the diagonal entries of a power are powers of the diagonal entries. The triangular
characteristic-polynomial root formula therefore gives the required multiset with
multiplicities, including zero fibres and colliding powers. -/
theorem fdCondensedPullbackFrobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    (∀ F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius Y₀),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber Y₀).left
        F.carrier →
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (fdGeometricBaseChange D X₀ Y₀ f₀)).obj
            F.carrier)) ∧
    ∀ z : {z : X₀.left // z ∈ closedPoints X₀.left},
      ∃ hx : f₀.left.base z.val ∈ closedPoints Y₀.left,
        (f₀.left.residueFieldMap z.val).hom.Finite ∧
        1 ≤ f₀.left.residueDegree z.val ∧
        Nat.card (X₀.left.residueField z.val) =
          Nat.card (Y₀.left.residueField (f₀.left.base z.val)) ^
            f₀.left.residueDegree z.val ∧
        ∀ (ιz : X₀.left.residueField z.val →+* D.k)
          (hz : ιz.comp (X₀.hom.residueFieldAlgebraMap z.val) = algebraMap D.k₀ D.k)
          (ιx : Y₀.left.residueField (f₀.left.base z.val) →+* D.k)
          (hιx : ιx.comp (Y₀.hom.residueFieldAlgebraMap (f₀.left.base z.val)) =
            algebraMap D.k₀ D.k)
          (h : localClosedPoint D X₀ z ιz hz ≫
              (fdGeometricBaseChange D X₀ Y₀ f₀) =
            localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx)
          (F : CondensedRing.StrictWeil.WeilModule (Profinite.padicAlgClRingObj l)
            (D.geometricFrobenius Y₀)),
          IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
            (D.geometricFiber Y₀).left F.carrier →
          fdCondensedClosedPullbackAssertions D l X₀ Y₀ f₀ z hx ιz hz ιx hιx h F := by
  classical
  have hqc (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
      [QuasiCompact T₀.hom] : CompactSpace (D.geometricFiber T₀).left := by
    change CompactSpace ((pullback T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd T₀.hom _)
  have hqs (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom]
      [QuasiCompact T₀.hom] [IsSeparated T₀.hom] :
      QuasiSeparatedSpace (D.geometricFiber T₀).left := by
    change QuasiSeparatedSpace ((pullback T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd T₀.hom _)
  let := hqc X₀
  let := hqc Y₀
  let := hqs X₀
  let := hqs Y₀
  have hpb : ConstantModelPullbackStatement (Profinite.padicAlgClRingObj.{u} l) := by
    apply pullback_constantModelConstructible l (Profinite.padicAlgClCondensedRing l)
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  refine ⟨fun F hF ↦ (hpb (fdGeometricBaseChange D X₀ Y₀ f₀) F.carrier hF).1, ?_⟩
  intro z
  let := (X₀.hom.residueFieldAlgebraMap z.val).toAlgebra
  have : Module.Finite D.k₀ (X₀.left.residueField z.val) :=
    X₀.hom.finite_residueField_of_isClosed z.val z.prop
  have : Finite (X₀.left.residueField z.val) := Module.finite_of_finite D.k₀
  have : Finite (Y₀.left.residueField (f₀.left.base z.val)) :=
    Finite.of_injective _ (f₀.left.residueFieldMap z.val).hom.injective
  have hx : f₀.left.base z.val ∈ closedPoints Y₀.left := by
    rw [← Y₀.hom.finitePoints_eq_closedPoints]
    exact Y₀.left.mem_finitePoints.mpr inferInstance
  let := (f₀.left.residueFieldMap z.val).hom.toAlgebra
  refine ⟨hx, ?_, ?_, ?_, ?_⟩
  · exact RingHom.finite_algebraMap.mpr (Module.Finite.of_finite)
  · exact Module.finrank_pos
  · exact Module.natCard_eq_pow_finrank
  · intro ιz hz ιx hιx h F hF
    let xbar := localClosedPoint D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx
    have hxbar : xbar ≫ (D.geometricFiber Y₀).hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hN := (condensed_fibres_exact D l _hl Y₀ xbar hxbar).1.2.2.2.1
      ⟨F.carrier, hF⟩
    let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
        (CondensedModule.fibre l D F.carrier xbar) := hN
    let zbar := localClosedPoint D X₀ z ιz hz
    have hzbar : zbar ≫ (D.geometricFiber X₀).hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hFpull := (hpb (fdGeometricBaseChange D X₀ Y₀ f₀) F.carrier hF).1
    have hM := (condensed_fibres_exact D l _hl X₀ zbar hzbar).1.2.2.2.1
      ⟨_, hFpull⟩
    let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
        (CondensedModule.fibre l D
          ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
            (fdGeometricBaseChange D X₀ Y₀ f₀)).obj F.carrier) zbar) := hM
    let : IsAlgClosed (PadicAlgCl l) := IsAlgClosure.isAlgClosed (Padic l)
    let : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
      fd_isAlgClosedOfEquiv ULift.ringEquiv.symm
    let cmp := fdCondensedFibreComparison D l (fdGeometricBaseChange D X₀ Y₀ f₀)
      zbar xbar h F.carrier
    let A := CondensedModule.operator l D (D.geometricFrobenius X₀).hom
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (fdGeometricBaseChange D X₀ Y₀ f₀)).obj F.carrier)
      (fdCondensedPullbackWeilIso l (fdGeometricBaseChange D X₀ Y₀ f₀)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩ F.carrier F.str)
      zbar (localClosedPointDegree D X₀ z - 1) (localClosedPoint_return D X₀ z ιz hz)
    let B := CondensedModule.operator l D (D.geometricFrobenius Y₀).hom F.carrier F.str
      xbar (localClosedPointDegree D Y₀ ⟨f₀.left.base z.val, hx⟩ - 1)
      (localClosedPoint_return D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx)
    have hcomm : A ≫ cmp.hom =
        cmp.hom ≫ ModuleCat.ofHom (B.hom ^ f₀.left.residueDegree z.val) :=
      fd_intertwining D l (fdGeometricBaseChange D X₀ Y₀ f₀)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩ F.carrier F.str
        zbar xbar h (localClosedPointDegree D X₀ z - 1)
        (localClosedPointDegree D Y₀ ⟨f₀.left.base z.val, hx⟩) (f₀.left.residueDegree z.val)
        (by have := localClosedPointDegree_pos D Y₀ ⟨f₀.left.base z.val, hx⟩; omega)
        Module.finrank_pos
        (congrArg (fun n : ℕ ↦ n - 1) (fd_degree_mul D X₀ Y₀ f₀ z hx))
        (localClosedPoint_return D X₀ z ιz hz)
        (localClosedPoint_return D Y₀ ⟨f₀.left.base z.val, hx⟩ ιx hιx)
    unfold fdCondensedClosedPullbackAssertions fdCondensedPullbackLocalAssertions
    exact fd_spectrum_of_intertwining cmp A B _ hcomm

end WeilConjectures
