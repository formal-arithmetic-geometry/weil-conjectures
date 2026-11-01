/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.NativeIntegralTensorTransport.NativeIntegralTensorTransport
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree

/-! # Local freeness of the condensed pulled-back Tate twist sheaves

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-coefficients-constructible/
sec-n-coefficients/sec-pulling-back-to-a-scheme/sk-def-sp-tate-twist/
def-coefficient-twists-detailed.md`, clauses (1)--(3)
(blueprint: lem-pur-twist-sheaf-locally-free).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale

open PurityTransport

/-- The canonical projection from the integral Tate limit to its `r`-th finite level.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, the projections p_r of T_S
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateProjection (S : Scheme.{u}) (ell r : ℕ) [Fact ell.Prime] :
    tateModule S ell ⟶ tateModuleLevel S ell r :=
  limit.π (tateModuleSystem S ell) (op r)

/-- The finite coefficient presentation of `ℤ/ell^r` used for the tensor reduction.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, the finite coefficient (Z/l^r Z)_S
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateFiniteCoefficient (_S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) : PurityTransport.Coefficient ell :=
  .finite (CommRingCat.of (ZMod (ell ^ r))) inferInstance (r - 1) (by
    rw [Nat.sub_add_cancel hr]
    simpa only [Nat.cast_pow] using ZMod.natCast_self (ell ^ r))

/-- The quotient coefficient map `R_S → (ℤ/ell^r)_S`.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, R_S = lim_r (Z/l^r Z)_S and its quotient maps
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateFiniteCoefficientMap (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S ⟶
      condensedRingObj ((tateFiniteCoefficient S ell r hr).obj ell) S :=
  coefficientMap ((tateFiniteCoefficient S ell r hr).integralMap ell) S

/-- The coefficient map is a morphism of ring objects.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clauses 2-3, coefficient maps
(blueprint: lem-pur-twist-sheaf-locally-free). -/
instance tateFiniteCoefficientMap_isMonHom (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    IsMonHom (tateFiniteCoefficientMap S ell r hr) := by
  dsimp [tateFiniteCoefficientMap]
  infer_instance

/-- The finite root line over the quotient coefficient ring.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, the target mu_{l^r,S} as a (Z/l^r Z)_S-module
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateFiniteLevel (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj ((tateFiniteCoefficient S ell r hr).obj ell) S) :=
  (Mod.freeFunctor _).obj (rootsOfUnitySheaf S (ell ^ r))

/-- The canonical free-module map from the integral finite root presentation to the
quotient-coefficient presentation.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, coordinatewise R_S-action on the roots
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateFiniteFreeMap (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    tateModuleLevel S ell r ⟶
      (Mod.comap (tateFiniteCoefficientMap S ell r hr)).obj
        (tateFiniteLevel S ell r hr) :=
  (Mod.comapId (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)).inv.app
      (tateModuleLevel S ell r) ≫
    (coefficientFreeTensor_linear
      (𝟙 (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S))
      (tateFiniteCoefficientMap S ell r hr)
      (tateFiniteCoefficientMap S ell r hr) (by simp)
      (𝟙 (rootsOfUnitySheaf S (ell ^ r)))).exists.choose

/-- The projection into the quotient-coefficient root line.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, p_r then coefficient reduction
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateFiniteProjection (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    tateModule S ell ⟶
      (Mod.comap (tateFiniteCoefficientMap S ell r hr)).obj
        (tateFiniteLevel S ell r hr) :=
  tateProjection S ell r ≫ tateFiniteFreeMap S ell r hr

/-- The canonical balanced map `T_S ⊗_R (ℤ/ell^r)_S → μ_{ell^r,S}`.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 2, the map t tensor a to a p_r(t)
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def tateTensorReduction (S : Scheme.{u}) (ell r : ℕ)
    [Fact ell.Prime] (hr : 0 < r) :
    (Mod.extendScalars (tateFiniteCoefficientMap S ell r hr)).obj
        (tateModule S ell) ⟶ tateFiniteLevel S ell r hr :=
  Mod.extendHom (tateFiniteCoefficientMap S ell r hr)
    (tateFiniteProjection S ell r hr)

/-- The canonical scalar extension of the Tate limit to the intrinsic integral coefficient ring.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, the source T_S tensor O_{E,S} of the first map
(blueprint: lem-pur-twist-sheaf-locally-free). -/
abbrev integralTateLine
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :=
  NativeIntegralTensorTransport.line ell E S

/-- The coefficient-limit projection `q_n`, before scalar extension to the finite quotient.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, the projections q_n of O_E(1)_S
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def coefficientIntegralProjection
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    coefficientIntegralTwistOne ell E S ⟶ coefficientIntegralTwistLevel ell E S n :=
  limit.π (coefficientIntegralTwistSystem ell E S) (op n)

/-- The map induced by `q_n` after extending scalars along the coefficient reduction.
Its defining formula is the universal balanced map, so its source is the scalar extension
of the integral limit and its target is the finite twist.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, the second map x tensor a to a q_n(x)
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def coefficientFiniteReduction
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) :
    (Mod.extendScalars (coefficientMap (twistReduction ell E n) S)).obj
        (coefficientIntegralTwistOne ell E S) ⟶
      coefficientFiniteTwistOne ell E S n :=
  Mod.extendHom (coefficientMap (twistReduction ell E n) S)
    (coefficientIntegralProjection S ell E n)

/-- The coefficient map from the integral Tate coefficient ring to the intrinsic integral
coefficient ring.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, the scalar map R_S to O_{E,S}
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def integralTateCoefficientMap
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :
    condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S ⟶
      condensedRingObj (twistIntegralRing ell E) S :=
  coefficientMap (NativeIntegralTensorTransport.integralMap ell E) S

/-- The coefficient map is a morphism of ring objects.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clauses 2-3, coefficient maps
(blueprint: lem-pur-twist-sheaf-locally-free). -/
instance integralTateCoefficientMap_isMonHom
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] :
    IsMonHom (integralTateCoefficientMap S ell E) := by
  dsimp [integralTateCoefficientMap]
  infer_instance

/-- The coefficient map at the `n`-th integral finite level, as a composite.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, coefficient reduction R_S to (A_{E,n})_S
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def integralTateFiniteMap
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S ⟶
      condensedRingObj (twistFiniteRing ell E n) S :=
  integralTateCoefficientMap S ell E ≫ coefficientMap (twistReduction ell E n) S

/-- The coefficient map is a morphism of ring objects.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clauses 2-3, coefficient maps
(blueprint: lem-pur-twist-sheaf-locally-free). -/
instance integralTateFiniteMap_isMonHom
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    IsMonHom (integralTateFiniteMap S ell E n) := by
  dsimp [integralTateFiniteMap]
  infer_instance

/-- The unique free tensor map at level `n`, before changing coefficients to `O_E`.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, coordinate t ⊗ b ↦ p_n(t) ⊗ b-bar
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def integralTateFreeMap
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    tateModuleLevel S ell (n + 1) ⟶
      (Mod.comap (integralTateFiniteMap S ell E n)).obj
        (coefficientFiniteTwistOne ell E S n) :=
  (Mod.comapId (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)).inv.app
      (tateModuleLevel S ell (n + 1)) ≫
    (coefficientFreeTensor_linear
      (𝟙 (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S))
      (integralTateFiniteMap S ell E n)
      (integralTateFiniteMap S ell E n) (by simp)
      (𝟙 (rootsOfUnitySheaf S (ell ^ (n + 1))))).exists.choose

/-- The `R_S`-linear coordinate map into the restriction of the integral finite twist.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, n-th coordinate of the first map
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def integralTateBaseLeg
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    tateModule S ell ⟶
      (Mod.comap (integralTateCoefficientMap S ell E)).obj
        (coefficientIntegralTwistLevel ell E S n) :=
  tateProjection S ell (n + 1) ≫ integralTateFreeMap S ell E n ≫
    (Mod.comapComp (integralTateCoefficientMap S ell E)
      (coefficientMap (twistReduction ell E n) S)).hom.app
      (coefficientFiniteTwistOne ell E S n)

/-- The specified integral coordinate leg, obtained by scalar extension along `R_S → O_{E,S}`.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, n-th coordinate of the first map
(blueprint: lem-pur-twist-sheaf-locally-free). -/
noncomputable def integralTateLeg
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (n : ℕ) :
    integralTateLine S ell E ⟶ coefficientIntegralTwistLevel ell E S n :=
  Mod.extendHom (integralTateCoefficientMap S ell E)
    (integralTateBaseLeg S ell E n)

/-- Compatibility of the prescribed coordinate legs with the coefficient transitions.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, compatibility with the transitions
(blueprint: lem-pur-twist-sheaf-locally-free). -/
def integralTateLegCompatibilityStatement
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] : Prop :=
  ∀ n : ℕ,
    (integralTateLeg S ell E (n + 1)).hom ≫
        (coefficientIntegralTwistTransition ell E S n).hom =
      (integralTateLeg S ell E n).hom

/-- The canonical integral comparison is the limit lift of the prescribed coordinate cone.
Source: def-coefficient-twists-detailed.md and companion
sk-def-sp-tate-twist-locally-free.proof.md, clause 3, the first canonical isomorphism
(blueprint: lem-pur-twist-sheaf-locally-free). -/
def integralTateComparisonStatement
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] : Prop :=
  ∃ (hcompat : integralTateLegCompatibilityStatement S ell E),
    IsIso (limit.lift (coefficientIntegralTwistSystem ell E S)
      (Cone.mk (integralTateLine S ell E)
        (NatTrans.ofOpSequence (integralTateLeg S ell E) (by
          intro n
          simp only [Functor.const_obj_map, coefficientIntegralTwistSystem,
            Functor.ofOpSequence_map_homOfLE_succ]
          apply Mod.hom_ext
          exact (hcompat n).symm))))

/-- The condensed coefficient-ring formulation of the finite Kummer, integral-limit, and
algebraic-closure Tate-line assertions.  The coefficient objects in every clause are
`p_S^*` images of the recorded condensed rings.  Level `n` of the finite and integral
twists is the node's level `n + 1`.

Source: def-coefficient-twists-detailed.md, finite-exponent independence, local rank-one
assertion and projection-induced comparisons of the displayed twists; companion
sk-def-sp-tate-twist-locally-free.proof.md (1)-(3)
(blueprint: lem-pur-twist-sheaf-locally-free).

Proof.
1. Apply clauses (2) and (3) of det-def-sp-tate-twist-locally-free with `X = S` and
   `A = A_{E,n}`.  This gives Kummer independence of the finite exponent and one common
   pro-etale cover trivializing all four coefficient types at every positive level.
2. On that cover choose the compatible roots `ζ_r` of its clause (1).  The integral
   coefficient limit (det-prop-sfb-qlbar-colimit-x-integral-limit, `E = ℚ_ℓ`) and sectionwise
   limits identify `a = (a_r) ∈ R_V` with `(ζ_r^{a_r})_r ∈ T_S|_V`, an `R_V`-linear
   isomorphism under which `p_r` is reduction.  Tensor restriction identifies the clause-2
   map with `a ↦ ζ_r^a`, an isomorphism; local detection on the cover proves clause 2.
3. The clause-3 maps exist globally: balancing holds at each finite coordinate, and
   `p_{n+1}(t)^ℓ = p_n(t)` gives compatibility of the first map's coordinates.  On the cover
   the bases `ζ_n ⊗ 1` identify `O_E(1)|_V` with `O_{E,V}` and `q_n` with coefficient
   reduction, so both maps become multiplication `1 ⊗ b ↦ b` and `b ⊗ a ↦ b̄ a`.  Tensor
   restriction and local detection prove both are isomorphisms; the transition
   compatibility holds coordinatewise by the defining formulas. -/
theorem pur_twist_sheaf_locally_free
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    [∀ x : S, Invertible (ell : S.residueField x)] :
    ∃ (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S),
      (∀ (n r k : ℕ)
        (hA : (ell ^ (r + 1) : Padic.coefficientExtensionRing ell E (n + 1)) = 0),
        IsIso (coefficientFiniteRootComparison ell E S n r k)) ∧
      (∀ (n : ℕ) (i : 𝒰.I₀),
        Mod.IsFree
          ((upperStar Ab (𝒰.f i)).obj
            (condensedRingObj (twistFiniteRing ell E n) S))
          (((upperStar Ab (𝒰.f i)).mapMod
            (condensedRingObj (twistFiniteRing ell E n) S)).obj
            (coefficientFiniteTwistOne ell E S n))) ∧
      (∀ (n : ℕ) (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistFiniteRing ell E n) S)).obj
              (coefficientFiniteTwistOne ell E S n)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistFiniteRing ell E n) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Mod.IsFree
          ((upperStar Ab (𝒰.f i)).obj
            (condensedRingObj (twistIntegralRing ell E) S))
          (((upperStar Ab (𝒰.f i)).mapMod
            (condensedRingObj (twistIntegralRing ell E) S)).obj
            (coefficientIntegralTwistOne ell E S))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistIntegralRing ell E) S)).obj
              (coefficientIntegralTwistOne ell E S)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistIntegralRing ell E) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Mod.IsFree
          ((upperStar Ab (𝒰.f i)).obj
            (condensedRingObj (twistRationalRing ell E) S))
          (((upperStar Ab (𝒰.f i)).mapMod
            (condensedRingObj (twistRationalRing ell E) S)).obj
            (coefficientRationalTwistOne ell E S))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (twistRationalRing ell E) S)).obj
              (coefficientRationalTwistOne ell E S)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (twistRationalRing ell E) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Mod.IsFree
          ((upperStar Ab (𝒰.f i)).obj
            (condensedRingObj (Profinite.padicAlgClRingObj ell) S))
          (((upperStar Ab (𝒰.f i)).mapMod
            (condensedRingObj (Profinite.padicAlgClRingObj ell) S)).obj
            (tateTwistOne S ell))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (Profinite.padicAlgClRingObj ell) S)).obj
              (tateTwistOne S ell)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (Profinite.padicAlgClRingObj ell) S)))) ∧
      (∀ (i : 𝒰.I₀),
        Nonempty
          ((((upperStar Ab (𝒰.f i)).mapMod
              (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)).obj
              (tateModule S ell)) ≅
            Mod.regular ((upperStar Ab (𝒰.f i)).obj
              (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ell]) S)))) ∧
      (∀ (r : ℕ) (hr : 0 < r), IsIso (tateTensorReduction S ell r hr)) ∧
      (∀ (n : ℕ), IsIso (coefficientFiniteReduction S ell E n)) ∧
      integralTateComparisonStatement S ell E := by sorry

end AlgebraicGeometry.ProEtale
