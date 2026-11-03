/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistFiniteLocallyFree
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeSignedLineFiniteness
public import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTwistLocalLine
public import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
public import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistIntegralLines
public import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree

/-! # Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3).

The statement uses the published root tower and finite tensor line for arbitrary finite
coefficients, and the current intrinsic coefficient objects for the integral, rational,
and algebraically closed coefficients. The `NativeTwistFiniteness` predicate records
local freeness of every signed power, its internal dual and cancellation, and the
inverse tensor equivalence on the ordinary unbounded derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme

/--
The compatible root cover, canonical finite Kummer comparisons, and local freeness of
all four coefficient twists. The finite coefficient clause is stated for every finite
commutative ring killed by a positive power of `ℓ`; the remaining three clauses use the
current intrinsic integral, rational, and algebraically closed coefficient constructions.

Source: Stacks Project, Tags 03PK and 03RV; coefficient-twist blueprint,
`det-def-sp-tate-twist-locally-free`, clauses (1)--(3).
Proof: the cyclotomic tower gives the common pro-etale cover and compatible primitive
roots. On that cover the root basis identifies every finite tensor line with the
coefficient unit, so Kummer transitions are isomorphisms and the signed powers cancel.
Taking the inverse limit gives the integral line; extension of scalars gives the rational
line, and the condensed Tate module gives the algebraically closed line. The native
signed-line finiteness theorem then supplies local freeness, duality, and the inverse
-derived tensor functors.
-/
theorem det_def_sp_tate_twist_locally_free
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (embedding : E →ₐ[Padic ℓ] Ω) :
    (∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A)
                (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A)
                (tateFiniteLine X ℓ A r a) hL (-(n : ℤ))))) ) ∧
    (∀ n : ℕ, CondensedRing.NativeTwistFiniteness (twistFiniteRing ℓ E n) X
      (coefficientSignedTwist X _ (coefficientFiniteTwistOne ℓ E X n))) ∧
    CondensedRing.NativeTwistFiniteness (twistIntegralRing ℓ E) X
      (coefficientSignedTwist X _ (coefficientIntegralTwistOne ℓ E X)) ∧
    CondensedRing.NativeTwistFiniteness (twistRationalRing ℓ E) X
      (coefficientSignedTwist X _ (coefficientRationalTwistOne ℓ E X)) ∧
    CondensedRing.NativeTwistFiniteness (Profinite.padicAlgClRingObj ℓ) X
      (tateTwist X ℓ) := by
  have _ := embedding
  obtain ⟨hF, hI, hR, hQ⟩ := tateTwist_locallyFree ℓ E X
  have liftLine (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
      (h : CondensedTateLineProperties Λ X
        (coefficientSignedTwist X (condensedRingObj Λ X) L)) :
      CondensedRing.NativeTwistFiniteness Λ X
        (coefficientSignedTwist X (condensedRingObj Λ X) L) := by
    obtain ⟨𝒰, h𝒰⟩ := h.locallyTrivial 1
    apply CondensedRing.nativeSignedLine_finiteness Λ X L
    refine ⟨𝒰, fun i ↦ ?_⟩
    let F := (upperStar Ab.{u + 1} (𝒰.f i)).mapMod (condensedRingObj Λ X)
    exact ⟨F.mapIso (λ_ L).symm ≪≫ (h𝒰 i).some⟩
  refine ⟨tateTwist_finite_locallyFree X ℓ,
    (fun n ↦ liftLine _ _ (hF n)), liftLine _ _ hI, liftLine _ _ hR, ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := hQ.locallyTrivial 1
  have hfin := CondensedRing.nativeSignedLine_finiteness
    (Profinite.padicAlgClRingObj ℓ) X (tateTwistOne X ℓ) (by
      refine ⟨𝒰, fun i ↦ ?_⟩
      let F := (upperStar Ab.{u + 1} (𝒰.f i)).mapMod
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      exact ⟨F.mapIso (λ_ (tateTwistOne X ℓ)).symm ≪≫ (h𝒰 i).some⟩)
  have hn (n : ℕ) : coefficientTwistNat X
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwistOne X ℓ) n =
        tateTwistNat X ℓ n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [coefficientTwistNat, tateTwistNat, ih]
  have hs : coefficientSignedTwist X
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) (tateTwistOne X ℓ) =
        tateTwist X ℓ := by
    funext m
    cases m with
    | ofNat n => exact hn n
    | negSucc n =>
      dsimp only [coefficientSignedTwist, tateTwist]
      rw [hn]
  rw [hs] at hfin
  exact hfin

end AlgebraicGeometry.Scheme
