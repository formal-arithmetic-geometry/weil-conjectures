module

public import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # The Chevalley exponential open cell

Source: Milne, Algebraic Groups (2017), Section 23h, equation (153) and the omitted
construction in Theorem 23.72, printed pp.510--511. The open-cell strengthening is the
agent construction lemma (blueprint: lem-sfb-chevalley-exponential-big-cell).

An arbitrary integral basis of the admissible lattice supplies matrix coordinates for
its scalar extension. The torus and root morphisms in the existence statement are fixed
by their formulas over every test algebra. No unspecified map or group law is chosen in
a definition. The subgroup is specified by its closed inclusion and minimality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.ChevalleyExponential

/-- Polynomial coordinate space, including zero coordinates. Source: Milne 23.72,
p.511 (blueprint: lem-sfb-chevalley-exponential-big-cell). -/
abbrev coordinates (F : Type u) [Field F] (N : ℕ) : Over (Spec (.of F)) :=
  StandardGroupSchemes.affine F (MvPolynomial (Fin N) F)

/-- A coordinate point, by polynomial substitution. Source: Milne (153), p.510
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def coordinatePoint (F : Type u) [Field F] {A : Type u} [CommRing A] [Algebra F A]
    {N : ℕ} (a : Fin N → A) : StandardGroupSchemes.affine F A ⟶ coordinates F N :=
  StandardGroupSchemes.map F (MvPolynomial.aeval a)

/-- Projection to one additive coordinate. Source: Milne 23.72, p.511
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def projection (F : Type u) [Field F] {N : ℕ} (i : Fin N) :
    coordinates F N ⟶ StandardGroupSchemes.additive F :=
  StandardGroupSchemes.map F (Polynomial.aeval (MvPolynomial.X i))

/-- Evaluate a root morphism by actual polynomial substitution. The result uses the
library's affine source for tangent points. Source: Milne (153), p.510
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def rootPoint {F : Type u} [Field F] {X : Over (Spec (.of F))}
    (x : StandardGroupSchemes.additive F ⟶ X)
    {A : Type u} [CommRing A] [Algebra F A] (a : A) : points X A :=
  StandardGroupSchemes.map F (Polynomial.aeval a) ≫ x

/-- Evaluation of the genuine character e^lambda, rather than its differential.
Source: Milne (152), p.510 (blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def characterValue {F P : Type u} [Field F] [AddCommGroup P]
    {A : Type u} [CommRing A] [Algebra F A]
    (s : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X) (ell : P) : A :=
  ((Spec.mapMulEquiv (R := F) (S := AddMonoidAlgebra F P) (T := A)).symm s).ofConv
    (AddMonoidAlgebra.single ell (1 : F))

/-- The actual integral restriction of a divided power. Source: Milne (153), p.510
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def dividedPower {W : Type u} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) (E : Module.End ℚ W) (m : ℕ)
    (h : ∀ w : W, w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ) :
    Module.End ℤ Λ :=
  (((Nat.factorial m : ℚ)⁻¹ • E ^ m).restrictScalars ℤ).restrict h

/-- The finite exponential matrix: all factorial division takes place over Q before
restriction to the lattice and scalar extension. Source: Milne (153), p.510
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def exponentialMatrix {W : Type u} [AddCommGroup W] [Module ℚ W]
    (Λ : Submodule ℤ W) {d : ℕ} (b : Module.Basis (ULift.{u} (Fin d)) ℤ Λ)
    (E : Module.End ℚ W) (h : ∀ (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ)
    (n : ℕ) {A : Type u} [CommRing A] (a : A) : Matrix (ULift.{u} (Fin d)) (ULift.{u} (Fin d)) A :=
  ∑ m ∈ Finset.range n,
    a ^ m • (LinearMap.toMatrix b b (dividedPower Λ E m (h m))).map (Int.castRingHom A)

/-- The three-factor coordinate source. Source: Milne 23.72, p.511
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
abbrev cellSource (F P : Type u) [Field F] [AddCommGroup P] (N : ℕ) :
    Over (Spec (.of F)) :=
  (coordinates F N ⊗ (diagonalizableGroup F P).X) ⊗ coordinates F N

/-- Multiplication of the ordered negative roots, torus, and ordered positive roots.
Source: Milne 23.72, p.511 (blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def cellMap {F P I : Type u} [Field F] [AddCommGroup P] {N : ℕ}
    (K : Grp (Over (Spec (.of F))))
    (t : (diagonalizableGroup F P).X ⟶ K.X)
    (x : I → (StandardGroupSchemes.additive F ⟶ K.X)) (β ν : Fin N → I) :
    cellSource F P N ⟶ K.X :=
  ((fst _ _ ≫ fst _ _ ≫
      ((List.finRange N).map (fun i ↦ projection F i ≫ x (ν i))).prod) *
    (fst _ _ ≫ snd _ _ ≫ t)) *
    (snd _ _ ≫ ((List.finRange N).map (fun i ↦ projection F i ≫ x (β i))).prod)

/-- Points of the product chart. Source: Milne 23.72, p.511
(blueprint: lem-sfb-chevalley-exponential-big-cell). -/
def cellPoint {F P : Type u} [Field F] [AddCommGroup P]
    {A : Type u} [CommRing A] [Algebra F A] {N : ℕ}
    (a b : Fin N → A)
    (t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X) :
    StandardGroupSchemes.affine F A ⟶ cellSource F P N :=
  lift (lift (coordinatePoint F a) t) (coordinatePoint F b)

open Classical in
/-- The exact exponential construction has an equivariant open cell and its differential
is the torus tangent plus the distinct nonzero root lines.

Source: Milne, Algebraic Groups (2017), Section 23h, (152)--(153), Theorem 23.72,
pp.510--511; agent open-cell construction
(blueprint: lem-sfb-chevalley-exponential-big-cell).

Proof plan:
1. On the torsion-free lattice, compare rational divided-power coefficients to obtain
   D_i D_j = binomial(i+j,i) D_(i+j). This proves the additive root laws over every
   test algebra. Weight shifting gives conjugation by the character e^alpha.
2. Apply lem-sfb-chevalley-unipotent-polynomial-coordinates to both ordered products.
   A positive rational functional separating the weights puts them in opposite block
   unitriangular groups. The weight characters generate P; diagonal entries and inverse
   block determinants therefore generate F[P], proving the torus inclusion closed.
3. Apply lem-sfb-block-gauss-scheme-chart. The product of the three closed subgroups is
   closed inside the Gauss open, so its multiplication into GL is a quasi-compact immersion.
   By lem-trf-fg-torsionfree-group-free, P has a finite basis. Its group algebra is Laurent
   polynomial, so the cell and its square remain integral after every field extension.
4. Apply lem-sfb-chevalley-opposite-rational-collection near the identity. Collect
   v1*u2 = u0*t0*v0, giving the factors
   u1*(t1*u0*t1^-1), t1*t0*t2, (t2^-1*v0*t2)*v2 of the product.
   Apply the same identity to v^-1*(t^-1*u^-1*t) for inversion. The resulting domains
   contain the identity and are dense by integrality.
5. Apply lem-sfb-generic-matrix-locus-subgroup-closure. The scheme-theoretic image is a
   closed subgroup. Every generator factors through the cell, and the cell factors through
   any closed subgroup containing the generators. Minimality of the scheme-theoretic image
   (def-nagata-scheme-theoretic-image) identifies this subgroup with K.
6. Apply lemma-nagata-immersion-open-in-scheme-image to get an open immersion into K.
   The origin maps to one. Conjugate each ordered factor to get the asserted equivariance
   over every test algebra; commutativity fixes the middle torus coordinate.
7. Multiply the matrices over the dual numbers. The differential sends the two root
   coordinate lists and torus tangent to their sum, and is invertible by openness.
   Its root axes are nonzero. Differentiate equivariance, retaining the actual torus
   characters, which remain distinct even in characteristics two and three. For empty
   roots, spanning gives V=P=0, both root products are empty and the chart is the identity. -/
theorem exists_open_cell
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Set V) (c : R → Module.Dual ℚ V)
    (hfinite : R.Finite) (hne : ∀ a : R, (a : V) ≠ 0)
    (hspan : Submodule.span ℚ R = ⊤)
    (htwo : ∀ a : R, c a a = 2)
    (hint : ∀ a b : R, ∃ n : ℤ, c a b = (n : ℚ))
    (hreflect : ∀ a : R, Set.BijOn (fun v : V ↦ v - c a v • (a : V)) R R)
    (hreduced : ∀ a : R,
      R ∩ (Submodule.span ℚ ({(a : V)} : Set V) : Set V) = {(a : V), -(a : V)})
    (P : Submodule ℤ V)
    (hP : ∀ v : V, v ∈ P ↔ ∀ a : R, ∃ n : ℤ, c a v = (n : ℚ))
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    (hss : LieAlgebra.HasTrivialRadical ℚ g)
    (H : LieSubalgebra ℚ g) (hab : IsLieAbelian H)
    (hmax : ∀ J : LieSubalgebra ℚ g, H ≤ J → IsLieAbelian J → J = H)
    (θ : H ≃ₗ[ℚ] Module.Dual ℚ V) (e : R → g)
    (he : ∀ a : R, e a ≠ 0 ∧ ∀ h : H, ⁅(h : g), e a⁆ = θ h a • e a)
    (hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
      (fun a : R ↦ Submodule.span ℚ ({e a} : Set g))))
    (r : ℕ) (δ : Module.Basis (Fin r) ℚ V) (hδ : ∀ i, δ i ∈ R)
    (hbase : ∀ a : R, (∀ i, ∃ n : ℤ, δ.repr a i = (n : ℚ)) ∧
      ((∀ i, 0 ≤ δ.repr a i) ∨ (∀ i, δ.repr a i ≤ 0)))
    (B : Module.Basis (Fin r ⊕ R) ℚ g)
    (hB : (∀ i, B (Sum.inl i) = (θ.symm (c ⟨δ i, hδ i⟩) : g)) ∧
      ∀ a : R, B (Sum.inr a) = e a)
    (hopp : ∀ a b : R, (b : V) = -(a : V) → ⁅e a, e b⁆ = (θ.symm (c a) : g))
    (hstring : ∀ a b k : R, (a : V) + (b : V) = (k : V) →
      ∃ p : ℕ, (b : V) - p • (a : V) ∈ R ∧
        (∀ n : ℕ, (b : V) - n • (a : V) ∈ R → n ≤ p) ∧
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ⁅e a, e b⁆ = ((ε : ℚ) * (p + 1 : ℚ)) • e k)
    (hzero : ∀ a b : R, (a : V) + (b : V) ≠ 0 → (a : V) + (b : V) ∉ R →
      ⁅e a, e b⁆ = 0)
    (W : Type u) [AddCommGroup W] [Module ℚ W]
    [LieRingModule g W] [LieModule ℚ g W] [FiniteDimensional ℚ W]
    (hfaithful : LieModule.IsFaithful ℚ g W)
    (Λ : Submodule ℤ W) (Ω : Finset V)
    (hlattice : Submodule.IsLattice ℚ Λ) (hfree : Module.Free ℤ Λ)
    (hweights : ∀ eta ∈ Ω, eta ∈ P ∧ LieModule.weightSpace W (fun h : H ↦ θ h eta) ≠ ⊥)
    (hW : DirectSum.IsInternal (fun eta : Ω ↦
      (LieModule.weightSpace W (fun h : H ↦ θ h eta)).toSubmodule))
    (hgenerate : Submodule.span ℤ (Ω : Set V) = P)
    (hΛ : DirectSum.IsInternal (fun eta : Ω ↦
      ((LieModule.weightSpace W (fun h : H ↦ θ h eta)).toSubmodule.restrictScalars
        ℤ).comap Λ.subtype))
    (n : R → ℕ) (hn : ∀ a : R, (LieModule.toEnd ℚ g W (e a)) ^ n a = 0)
    (hdiv : ∀ (a : R) (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • (LieModule.toEnd ℚ g W (e a)) ^ m) w ∈ Λ)
    (d : ℕ) (bΛ : Module.Basis (ULift.{u} (Fin d)) ℤ Λ)
    (N : ℕ) (β ν : Fin N → R) (hβ : Function.Injective β)
    (hpositive : Set.range β = {a : R | ∀ i, 0 ≤ δ.repr a i})
    (hν : ∀ i, (ν i : V) = -(β i : V))
    (horder : ∀ i j : Fin N, i ≤ j →
      (∑ k, δ.repr (β i) k) ≤ ∑ k, δ.repr (β j) k)
    (F : Type u) [Field F] [IsAlgClosed F] :
    ∃ (tGL : (diagonalizableGroup F P).X ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) F)
      (xGL : R → (StandardGroupSchemes.additive F ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) F)),
      IsClosedSubgroupScheme tGL ∧ (∀ a : R, IsMonHom (xGL a)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (s : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X)
        (eta : V) (heta : eta ∈ Ω) (w : Λ),
        (w : W) ∈ LieModule.weightSpace W (fun h : H ↦ θ h eta) →
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A (s ≫ tGL)).val.mulVec
            (fun j ↦ (bΛ.repr w j : A)) =
          characterValue s ⟨eta, (hweights eta heta).1⟩ • (fun j ↦ (bΛ.repr w j : A))) ∧
      (∀ (A : Type u) [CommRing A] [Algebra F A] (a : R) (z : A),
        (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) F A (rootPoint (xGL a) z)).val =
          exponentialMatrix Λ bΛ (LieModule.toEnd ℚ g W (e a)) (hdiv a) (n a) z) ∧
      ∃ (K : Grp (Over (Spec (.of F)))) (iK : K.X ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) F)
        (tK : (diagonalizableGroup F P).X ⟶ K.X)
        (xK : R → (StandardGroupSchemes.additive F ⟶ K.X)),
        IsClosedSubgroupScheme iK ∧ tK ≫ iK = tGL ∧
        (∀ a : R, xK a ≫ iK = xGL a) ∧
        (∀ (J : Grp (Over (Spec (.of F)))) (iJ : J.X ⟶ GeneralLinearGroup (ULift.{u} (Fin d)) F),
          IsClosedSubgroupScheme iJ →
          (∃ tJ : (diagonalizableGroup F P).X ⟶ J.X, tJ ≫ iJ = tGL) →
          (∀ a : R, ∃ y : StandardGroupSchemes.additive F ⟶ J.X, y ≫ iJ = xGL a) →
          ∃ f : K.X ⟶ J.X, f ≫ iJ = iK) ∧
        IsOpenImmersion (cellMap K tK xK β ν).left ∧
        cellPoint (fun _ : Fin N ↦ (0 : F)) (fun _ ↦ 0) 1 ≫ cellMap K tK xK β ν = 1 ∧
        (∀ (A : Type u) [CommRing A] [Algebra F A]
          (s t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X)
          (a b : Fin N → A),
          (s ≫ tK) * (cellPoint a b t ≫ cellMap K tK xK β ν) * (s ≫ tK)⁻¹ =
            cellPoint
              (fun j ↦ characterValue s ⟨(ν j : V), (hP _).2
                (fun k ↦ hint k (ν j))⟩ * a j)
              (fun j ↦ characterValue s ⟨(β j : V), (hP _).2
                (fun k ↦ hint k (β j))⟩ * b j) t ≫ cellMap K tK xK β ν) ∧
        ∃ (v : R → GrpObj.Lie K.X)
          (D : ((Fin N → F) × GrpObj.Lie (diagonalizableGroup F P).X × (Fin N → F))
            ≃ₗ[F] GrpObj.Lie K.X),
          (∀ a : R, v a ≠ 0 ∧ GrpObj.tangentPoint (v a) =
            rootPoint (xK a) (TrivSqZeroExt.inr (1 : F) : DualNumber F)) ∧
          (∀ (a b : Fin N → F) (z : GrpObj.Lie (diagonalizableGroup F P).X),
            GrpObj.tangentPoint (D (a, z, b)) =
              (((List.finRange N).map (fun j ↦
                rootPoint (xK (ν j)) (TrivSqZeroExt.inr (a j) : DualNumber F))).prod *
                (GrpObj.tangentPoint z ≫ tK)) *
              ((List.finRange N).map (fun j ↦
                rootPoint (xK (β j)) (TrivSqZeroExt.inr (b j) : DualNumber F))).prod) ∧
          (∀ (a : R)
            (s : StandardGroupSchemes.affine F F ⟶ (diagonalizableGroup F P).X),
            (points.map K.X (TrivSqZeroExt.inlAlgHom F F F) (s ≫ tK)) *
                GrpObj.tangentPoint (v a) *
                (points.map K.X (TrivSqZeroExt.inlAlgHom F F F) (s ≫ tK))⁻¹ =
              GrpObj.tangentPoint
                (characterValue s ⟨(a : V), (hP _).2 (fun k ↦ hint k a)⟩ • v a)) ∧
          (∀ (s : StandardGroupSchemes.affine F F ⟶ (diagonalizableGroup F P).X)
            (z : GrpObj.Lie (diagonalizableGroup F P).X),
            (points.map K.X (TrivSqZeroExt.inlAlgHom F F F) (s ≫ tK)) *
                (GrpObj.tangentPoint z ≫ tK) *
                (points.map K.X (TrivSqZeroExt.inlAlgHom F F F) (s ≫ tK))⁻¹ =
              GrpObj.tangentPoint z ≫ tK) ∧
          (∀ a b : R, a ≠ b →
            ∃ s : StandardGroupSchemes.affine F F ⟶ (diagonalizableGroup F P).X,
              characterValue s ⟨(a : V), (hP _).2 (fun k ↦ hint k a)⟩ ≠
                characterValue s ⟨(b : V), (hP _).2 (fun k ↦ hint k b)⟩) ∧
          (R = ∅ → IsIso tK ∧ IsIso (cellMap K tK xK β ν)) := by
  sorry

end AlgebraicGeometry.ChevalleyExponential
