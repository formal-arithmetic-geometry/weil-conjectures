module

public import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation
public import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure
public import Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces
public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Integral rank-one subgroups of a Chevalley representation

Source: Milne, Algebraic Groups (2017), Section 23h, equation (153), Theorem 23.72,
printed pp.510--511, and Section 23d, Theorem 23.71.
(blueprint: lem-sfb-chevalley-integral-rank-one)

A basis of the full integer lattice identifies its scalar extension with a coordinate
space. The divided powers are restricted to that actual lattice before reduction to a
field; factorials are never inverted in positive characteristic. All point identities
quantify over arbitrary commutative algebras, not only fields or reduced algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.ChevalleyIntegralRankOne

/-- The integral matrix of a divided power, restricted using lattice admissibility.
Source: Milne, (153), p.510 (blueprint: lem-sfb-chevalley-integral-rank-one). -/
def dividedPowerMatrix {W I : Type u} [AddCommGroup W] [Module ℚ W]
    [Fintype I] [DecidableEq I] (Λ : Submodule ℤ W) (b : Module.Basis I ℤ Λ)
    (E : Module.End ℚ W)
    (h : ∀ (m : ℕ) (w : W), w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ)
    (m : ℕ) : Matrix I I ℤ :=
  LinearMap.toMatrix b b
    ((((Nat.factorial m : ℚ)⁻¹ • E ^ m).restrictScalars ℤ).restrict (h m))

/-- The finite polynomial matrix (153), using the rational operator's nilpotency class.
Source: Milne, (153), p.510 (blueprint: lem-sfb-chevalley-integral-rank-one). -/
def exponentialMatrix {W I : Type u} [AddCommGroup W] [Module ℚ W]
    [Fintype I] [DecidableEq I] (Λ : Submodule ℤ W) (b : Module.Basis I ℤ Λ)
    (E : Module.End ℚ W)
    (h : ∀ (m : ℕ) (w : W), w ∈ Λ → ((Nat.factorial m : ℚ)⁻¹ • E ^ m) w ∈ Λ)
    {A : Type u} [CommRing A] (a : A) : Matrix I I A :=
  ∑ m ∈ Finset.range (nilpotencyClass E),
    a ^ m • (dividedPowerMatrix Λ b E h m).map (Int.castRingHom A)

/-- Evaluate a group-algebra basis element at an algebra point of D(P).
Source: Milne, Section 23h, p.510 (blueprint: lem-sfb-chevalley-integral-rank-one). -/
def weightValue {F P A : Type u} [Field F] [AddCommGroup P] [CommRing A] [Algebra F A]
    (t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X) (lam : P) : A :=
  (Scheme.ΓSpecIso (.of A)).hom
    (t.left.appTop ((Scheme.ΓSpecIso (.of (AddMonoidAlgebra F P))).inv
      (AddMonoidAlgebra.single lam 1)))

/-- The parameter point of a root homomorphism. It uses the recorded additive group and polynomial
substitution. Source: Milne, (153), p.510
(blueprint: lem-sfb-chevalley-integral-rank-one). -/
def rootPoint {F : Type u} [Field F] {G : Grp (Over (Spec (.of F)))}
    (x : Grp.mk (StandardGroupSchemes.additive F) ⟶ G)
    {A : Type u} [CommRing A] [Algebra F A] (a : A) :
    StandardGroupSchemes.affine F A ⟶ G.X :=
  StandardGroupSchemes.map F (Polynomial.aeval a) ≫ x.hom.hom

/-- The Weyl word x_a(1) x_(-a)(-1) x_a(1) on every test algebra.
Source: Milne, Section 23d and Theorem 23.71
(blueprint: lem-sfb-chevalley-integral-rank-one). -/
def weylPoint {F : Type u} [Field F] {G : Grp (Over (Spec (.of F)))}
    (x y : Grp.mk (StandardGroupSchemes.additive F) ⟶ G)
    (A : Type u) [CommRing A] [Algebra F A] :
    StandardGroupSchemes.affine F A ⟶ G.X :=
  rootPoint x (1 : A) * rootPoint y (-1 : A) * rootPoint x (1 : A)

open Classical in
/-- Integral SL2 maps, rank-one reductive subgroups and Weyl words for the given
Chevalley data. The basis bΛ is arbitrary and only supplies coordinates on Λ ⊗ F;
neg and rootWeight name the unique negative root and the inclusion of roots in P.

Source: Milne, Algebraic Groups (2017), Section 23h, (153), Theorem 23.72,
pp.510--511; Section 23d and Theorem 23.71 for the signs.
(blueprint: lem-sfb-chevalley-integral-rank-one).

Proof plan:
1. Apply lem-sfb-root-base-rational-integral-spans and reflection induction to the
   dual pairing. Every coroot is primitive in the coroot lattice, so some integral
   weight pairs to one. Character antiduality makes h_a and the weight torus closed.
2. Regroup the integral weight summands by c_a(lam). The Chevalley brackets give an
   sl2 triple. Apply lem-sfb-sl2-lattice-integration and base change; its restrictions
   are exactly the two finite exponentials and the stated diagonal, with no sign change.
3. Apply lem-sfb-sl2-diagonal-kernel-detection. Its diagonal restriction is closed by
   step 1; hence v_a and its upper unitriangular restriction x_a are closed immersions.
4. A divided power shifts weights by m*a. This proves torus equivariance integrally.
   Verify equivariance of v_a on its diagonal and two root groups; the two Gauss charts
   cover SL2, giving the identity over every test algebra.
5. Choose lam0 pairing to one and S = ker lam0 in T. Set z(t) = h_a(a(t)^(-1))*t².
   Its a-character is one, so it centralizes v_a(SL2). The homomorphism
   SL2 × S → GL, (g,t) ↦ v_a(g)z(t), has diagonal map
   (s,t) ↦ h_a(s*a(t)^(-1))*t², an isogeny of split tori.
6. Compute its kernel over A[q,q^(-1)]: an SL2 matrix commuting with every diagonal
   matrix is diagonal. The kernel equals that of the displayed torus isogeny; its
   first diagonal coordinate has square one, so this is a finite central kernel.
7. Apply lem-sfb-central-character-sublattice-quotient to SL2 × S. Its quotient is
   split reductive, its torus is T, its roots are ±a and its coroot is h_a.
8. Apply lem-sfb-affine-homomorphism-flat-image and the faithfully flat quotient
   universal property both ways to identify that quotient with its closed image J_a.
   The Gauss charts show that T and x_(±a) generate exactly that image.
9. Distinct simple roots have mixed-sign difference, hence [e_(-a),e_b] = 0.
   Their rational exponentials commute. The equality descends to integer polynomial
   matrices by injectivity into rational polynomials, and then to every F-algebra.
10. Apply lem-sfb-chevalley-adjoint-weyl-signs. The identity
    exp(E)Y exp(-E) = exp(ad E)Y gives the signed root-vector conjugation.
    Exponentiate, descend the polynomial identity to ℤ and base change to F.
11. The same adjoint calculation permutes rational weight spaces by s_a. Since the
    Weyl matrix and its inverse preserve Λ, this permutes integral weight summands.
    Base change gives normalization and the actual character reflection in every
    characteristic, even when differentiated weights coincide.
12. Apply lem-sfb-root-base-reflection-induction to roots reachable from a simple root
    by a reflection word together with the corresponding signed conjugation identity.
    The empty word handles simple roots; prepend n_a for a simple reflection and append
    n_delta for negation. Iterated step 10 supplies the signs, including in char 2,3. -/
theorem integral_rank_one
    (V : Type u) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (R : Set V) (c : R → Module.Dual ℚ V)
    (hfinite : R.Finite) (hne : ∀ a : R, (a : V) ≠ 0)
    (hspan : Submodule.span ℚ R = ⊤) (htwo : ∀ a : R, c a a = 2)
    (hint : ∀ a b : R, ∃ n : ℤ, c a b = (n : ℚ))
    (hreflect : ∀ a : R, Set.BijOn (fun v : V ↦ v - c a v • (a : V)) R R)
    (hreduced : ∀ a : R,
      R ∩ (Submodule.span ℚ ({(a : V)} : Set V) : Set V) = {(a : V), -(a : V)})
    (P : Submodule ℤ V)
    (hP : ∀ v : V, v ∈ P ↔ ∀ a : R, ∃ n : ℤ, c a v = (n : ℚ))
    (rootWeight : R → P) (hrootWeight : ∀ a : R, (rootWeight a : V) = a)
    (neg : R → R) (hneg : ∀ a : R, (neg a : V) = -(a : V))
    (g : Type u) [LieRing g] [LieAlgebra ℚ g] [FiniteDimensional ℚ g]
    (hsemisimple : LieAlgebra.HasTrivialRadical ℚ g)
    (H : LieSubalgebra ℚ g) (hab : IsLieAbelian H)
    (hmax : ∀ K : LieSubalgebra ℚ g, H ≤ K → IsLieAbelian K → K = H)
    (θ : H ≃ₗ[ℚ] Module.Dual ℚ V) (e : R → g)
    (he : ∀ a : R, e a ≠ 0 ∧ ∀ h : H, ⁅(h : g), e a⁆ = θ h a • e a)
    (hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
      (fun a : R ↦ Submodule.span ℚ ({e a} : Set g))))
    (r : ℕ) (b : Module.Basis (Fin r) ℚ V) (hb : ∀ i, b i ∈ R)
    (hbase : ∀ a : R, (∀ i, ∃ n : ℤ, b.repr a i = (n : ℚ)) ∧
      ((∀ i, 0 ≤ b.repr a i) ∨ (∀ i, b.repr a i ≤ 0)))
    (B : Module.Basis (Fin r ⊕ R) ℚ g)
    (hBsimple : ∀ i, B (Sum.inl i) = (θ.symm (c ⟨b i, hb i⟩) : g))
    (hBroot : ∀ a : R, B (Sum.inr a) = e a)
    (hopposite : ∀ a : R, ⁅e a, e (neg a)⁆ = (θ.symm (c a) : g))
    (hbracket : ∀ a d k : R, (a : V) + (d : V) = (k : V) →
      ∃ p : ℕ, (d : V) - p • (a : V) ∈ R ∧
        (∀ n : ℕ, (d : V) - n • (a : V) ∈ R → n ≤ p) ∧
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ⁅e a, e d⁆ = ((ε : ℚ) * (p + 1 : ℚ)) • e k)
    (hzero : ∀ a d : R, (a : V) + (d : V) ≠ 0 → (a : V) + (d : V) ∉ R →
      ⁅e a, e d⁆ = 0)
    (W : Type u) [AddCommGroup W] [Module ℚ W] [LieRingModule g W] [LieModule ℚ g W]
    [FiniteDimensional ℚ W] [LieModule.IsFaithful ℚ g W]
    (Λ : Submodule ℤ W) (hlattice : Submodule.IsLattice ℚ Λ) [Module.Free ℤ Λ]
    (Ω : Finset V)
    (hweights : ∀ mu ∈ Ω, mu ∈ P ∧ LieModule.weightSpace W (fun h : H ↦ θ h mu) ≠ ⊥)
    (hW : DirectSum.IsInternal (fun mu : Ω ↦
      (LieModule.weightSpace W (fun h : H ↦ θ h mu)).toSubmodule))
    (hΩ : Submodule.span ℤ (Ω : Set V) = P)
    (hΛ : DirectSum.IsInternal (fun mu : Ω ↦
      ((LieModule.weightSpace W (fun h : H ↦ θ h mu)).toSubmodule.restrictScalars ℤ).comap
        Λ.subtype))
    (hnil : ∀ a : R, IsNilpotent (LieModule.toEnd ℚ g W (e a)))
    (hdiv : ∀ (a : R) (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • (LieModule.toEnd ℚ g W (e a)) ^ m) w ∈ Λ)
    (I : Type u) [Fintype I] [DecidableEq I] (bΛ : Module.Basis I ℤ Λ)
    (F : Type u) [Field F] [IsAlgClosed F] :
    ∃ (iT : diagonalizableGroup F P ⟶ Grp.mk (GeneralLinearGroup I F))
      (χ : P → (diagonalizableGroup F P ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)))
      (h : R → (Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ diagonalizableGroup F P))
      (x : R → (Grp.mk (StandardGroupSchemes.additive F) ⟶ Grp.mk (GeneralLinearGroup I F)))
      (reflection : R → (diagonalizableGroup F P ≅ diagonalizableGroup F P)),
      IsClosedSubgroupScheme iT.hom.hom ∧
      (∀ (lam : P) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X),
        RankOneRoots.multiplicativeValue A (t ≫ (χ lam).hom.hom) = weightValue t lam) ∧
      (∀ (a : R) (lam : P) (n : ℤ), c a lam = (n : ℚ) →
        (h a ≫ χ lam).hom.hom = (𝟙 (StandardGroupSchemes.multiplicative F)) ^ n) ∧
      (∀ (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X)
        (mu : Ω) (lam : P), (lam : V) = mu → ∀ w : Λ,
        (w : W) ∈ LieModule.weightSpace W (fun q : H ↦ θ q mu) →
        (GeneralLinearGroup.homMulEquiv I F A (t ≫ iT.hom.hom)).val.mulVec
            (fun j ↦ (bΛ.repr w j : A)) =
          weightValue t lam • (fun j ↦ (bΛ.repr w j : A))) ∧
      (∀ (a : R) (A : CommAlgCat.{u} F) (z : A),
        (GeneralLinearGroup.homMulEquiv I F A (rootPoint (x a) z)).val =
          exponentialMatrix Λ bΛ (LieModule.toEnd ℚ g W (e a)) (hdiv a) z) ∧
      (∀ a : R, IsClosedSubgroupScheme (x a).hom.hom) ∧
      (∀ a : R, ∃ v : RankOneRoots.SL2Hom (Grp.mk (GeneralLinearGroup I F)),
        (∀ (A : CommAlgCat.{u} F) (z : A) (q : Matrix.SpecialLinearGroup (Fin 2) A),
          q.val = !![1, z; 0, 1] → v.app A q = rootPoint (x a) z) ∧
        (∀ (A : CommAlgCat.{u} F) (z : A) (q : Matrix.SpecialLinearGroup (Fin 2) A),
          q.val = !![1, 0; z, 1] → v.app A q = rootPoint (x (neg a)) z) ∧
        (∀ (A : CommAlgCat.{u} F)
          (z : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F)
          (q : Matrix.SpecialLinearGroup (Fin 2) A),
          q.val = !![RankOneRoots.multiplicativeValue A z, 0;
            0, RankOneRoots.multiplicativeValue A z⁻¹] →
          v.app A q = z ≫ (h a ≫ iT).hom.hom)) ∧
      (∀ a : R, ∃ (J : Grp (Over (Spec (.of F))))
        (j : J ⟶ Grp.mk (GeneralLinearGroup I F))
        (t : diagonalizableGroup F P ⟶ J)
        (upper lower : Grp.mk (StandardGroupSchemes.additive F) ⟶ J)
        (act : ModObj (diagonalizableGroup F P).X J.X),
        IsClosedSubgroupScheme j.hom.hom ∧ t ≫ j = iT ∧
        upper ≫ j = x a ∧ lower ≫ j = x (neg a) ∧
        (∀ (K : Grp (Over (Spec (.of F)))) (k : K ⟶ Grp.mk (GeneralLinearGroup I F)),
          IsClosedSubgroupScheme k.hom.hom →
          (∃ f : diagonalizableGroup F P ⟶ K, f ≫ k = iT) →
          (∃ f : Grp.mk (StandardGroupSchemes.additive F) ⟶ K, f ≫ k = x a) →
          (∃ f : Grp.mk (StandardGroupSchemes.additive F) ⟶ K, f ≫ k = x (neg a)) →
          ∃ f : J ⟶ K, f ≫ k = j) ∧
        ReductiveTorusCentralizer.IsReductive J ∧
        ReductiveTorusCentralizer.IsMaximalTorus t ∧
        (∃ d : ℕ, Nonempty (diagonalizableGroup F P ≅ MultiplicativeType.splitTorus F d)) ∧
        act.smul = (t.hom.hom ⊗ₘ 𝟙 J.X) ≫ GrpObj.conj J.X ∧
        (∀ ψ : diagonalizableGroup F P ⟶ Grp.mk (StandardGroupSchemes.multiplicative F),
          (ψ.hom.hom ≠ 1 ∧
            @TorusCharacterTangent.weightSpace F _ (diagonalizableGroup F P) J act ψ ≠ ⊥) ↔
          ψ = χ (rootWeight a) ∨ ψ = χ (rootWeight (neg a))) ∧
        (∀ ν : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ diagonalizableGroup F P,
          (∀ (lam : P) (n : ℤ),
            (ν ≫ χ lam).hom.hom = (𝟙 (StandardGroupSchemes.multiplicative F)) ^ n →
            (reflection a).hom.hom.hom ≫ (χ lam).hom.hom =
              (χ lam).hom.hom / (χ (rootWeight a)).hom.hom ^ n) → ν = h a)) ∧
      (∀ (i j : Fin r), i ≠ j → ∀ (A : CommAlgCat.{u} F) (z w : A),
        Commute (rootPoint (x (neg ⟨b i, hb i⟩)) z) (rootPoint (x ⟨b j, hb j⟩) w)) ∧
      (∀ (a : R) (A : CommAlgCat.{u} F)
        (t : StandardGroupSchemes.affine F A ⟶ (diagonalizableGroup F P).X),
        weylPoint (x a) (x (neg a)) A * (t ≫ iT.hom.hom) *
            (weylPoint (x a) (x (neg a)) A)⁻¹ =
          t ≫ ((reflection a).hom ≫ iT).hom.hom) ∧
      (∀ (a : R) (lam κ : P), (κ : V) = (lam : V) - c a lam • (a : V) →
        (reflection a).hom ≫ χ lam = χ κ) ∧
      (∃ ε : R → R → ℤ, (∀ a d : R, ε a d = 1 ∨ ε a d = -1) ∧
        ∀ (a d k : R), (k : V) = (d : V) - c a d • (a : V) →
          ∀ (A : CommAlgCat.{u} F) (z : A),
            weylPoint (x a) (x (neg a)) A * rootPoint (x d) z *
                (weylPoint (x a) (x (neg a)) A)⁻¹ =
              rootPoint (x k) ((ε a d : A) * z)) ∧
      (∀ gamma : R, ∃ (δ : Fin r) (word : List (Fin r × ℤ)) (ε : ℤ),
        (∀ q ∈ word, q.2 = 1 ∨ q.2 = -1) ∧ (ε = 1 ∨ ε = -1) ∧
        ∀ (A : CommAlgCat.{u} F) (z : A),
          (word.map (fun q ↦
            weylPoint (x ⟨b q.1, hb q.1⟩) (x (neg ⟨b q.1, hb q.1⟩)) A ^ q.2)).prod *
              rootPoint (x ⟨b δ, hb δ⟩) z *
              ((word.map (fun q ↦
                weylPoint (x ⟨b q.1, hb q.1⟩) (x (neg ⟨b q.1, hb q.1⟩)) A ^ q.2)).prod)⁻¹ =
            rootPoint (x gamma) ((ε : A) * z)) := by
  sorry

end AlgebraicGeometry.ChevalleyIntegralRankOne
