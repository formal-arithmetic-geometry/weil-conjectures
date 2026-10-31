/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.LinearAlgebra.CofactorLocalData
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
public import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Local descent of the projective cofactor map

Source: Stacks Project, duality.tex, Tag 0E9Y, displayed wedge formula and its
well-definedness; algebra.tex, Tags 00NX, 00EK, 00DM, 0C6F.
(blueprint: lem-sfb-cofactor-local-descent)

The comparison data are normalized on pure wedges, dual evaluations and pure tensors.
Localization rings are represented by `Localization S`; this includes every localization
up to its unique algebra isomorphism. No differential is assumed injective.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

open scoped TensorProduct

namespace Module

/-- Canonical transition on a scalar-extended module for S contained in T.
This is scalar extension of the unique localization ring map (Stacks Tags 00CM, 00DL).
(blueprint: lem-sfb-cofactor-local-descent). -/
noncomputable def cofactorLocalizationTransition {A : Type u} [CommRing A]
    (S T : Submonoid A) (h : S ≤ T) (M : Type v) [AddCommGroup M] [Module A M] :
    Localization S ⊗[A] M →ₗ[A] Localization T ⊗[A] M :=
  TensorProduct.map
    ({ toRingHom := IsLocalization.map (Localization T) (RingHom.id A) h
       commutes' := IsLocalization.map_eq h } :
      Localization S →ₐ[A] Localization T).toLinearMap
    LinearMap.id

/-- Coherence of the normalized comparisons on successive localizations. The exterior
maps preserve wedges, the dual maps preserve evaluation, and the line maps preserve
the dual-first tensor product. Source: Stacks Tags 0C6F and 00DL.
(blueprint: lem-sfb-cofactor-local-descent). -/
def CofactorComparisonsCoherent {A : Type u} [CommRing A]
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (u : P →ₗ[A] Q) (c : ℕ)
    (e : ∀ S : Submonoid A, CofactorScalarComparison (Localization S) u c) : Prop :=
  ∀ (S T : Submonoid A) (h : S ≤ T),
    (∀ x : Fin c → Localization S ⊗[A] P,
      (e T).source (cofactorLocalizationTransition S T h _
        ((e S).source.symm (exteriorPower.ιMulti (Localization S) c x))) =
      exteriorPower.ιMulti (Localization T) c
        (fun i ↦ cofactorLocalizationTransition S T h P (x i))) ∧
    (∀ x : Fin (c + 1) → Localization S ⊗[A] Q,
      (e T).target (cofactorLocalizationTransition S T h _
        ((e S).target.symm (exteriorPower.ιMulti (Localization S) (c + 1) x))) =
      exteriorPower.ιMulti (Localization T) (c + 1)
        (fun i ↦ cofactorLocalizationTransition S T h Q (x i))) ∧
    (∀ (l : Dual (Localization S) (⋀[Localization S]^c (Localization S ⊗[A] P)))
        (x : ⋀[Localization S]^c (Localization S ⊗[A] P)),
      (e T).dual (cofactorLocalizationTransition S T h _ ((e S).dual.symm l))
        ((e T).source (cofactorLocalizationTransition S T h _ ((e S).source.symm x))) =
      IsLocalization.map (Localization T) (RingHom.id A) h (l x)) ∧
    (∀ (l : Dual (Localization S) (⋀[Localization S]^c (Localization S ⊗[A] P)))
        (x : ⋀[Localization S]^(c + 1) (Localization S ⊗[A] Q)),
      (e T).line (cofactorLocalizationTransition S T h _
        ((e S).line.symm (l ⊗ₜ[Localization S] x))) =
      (e T).dual (cofactorLocalizationTransition S T h _ ((e S).dual.symm l)) ⊗ₜ[Localization T]
        (e T).target (cofactorLocalizationTransition S T h _ ((e S).target.symm x)))

/-- On every standard free cover, the local basis values are a matching family and
have exactly one global preimage. Source: Stacks Tag 00EK, applied to the determinant
module, with the formula from Tag 0E9Y.
(blueprint: lem-sfb-cofactor-local-descent). -/
def CofactorCoverDescent {A : Type u} [CommRing A]
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (u : P →ₗ[A] Q) (c : ℕ)
    (e : ∀ S : Submonoid A, CofactorScalarComparison (Localization S) u c) : Prop :=
  ∀ (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ →
    ∀ (p : ∀ i, Module.Basis (Fin c) (Localization.Away (f i))
        (Localization.Away (f i) ⊗[A] P))
      (_q : ∀ i, Module.Basis (Fin (c + 1)) (Localization.Away (f i))
        (Localization.Away (f i) ⊗[A] Q)) (v : Q),
    (∀ i j : Fin n,
      (IsLocalizedModule.lift (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (CofactorTarget A P Q c))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (CofactorTarget A P Q c))
        (RingTheory.localizationAway_map_units_of_dvd (f i) (f i * f j)
          (dvd_mul_right (f i) (f j))))
        ((LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) _).symm
          ((e (Submonoid.powers (f i))).line.symm
            (cofactorBasisValue (u.baseChange (Localization.Away (f i))) (p i)
              (1 ⊗ₜ[A] v)))) =
      (IsLocalizedModule.lift (Submonoid.powers (f j))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) (CofactorTarget A P Q c))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j))
          (CofactorTarget A P Q c))
        (RingTheory.localizationAway_map_units_of_dvd (f j) (f i * f j)
          (dvd_mul_left (f j) (f i))))
        ((LocalizedModule.equivTensorProduct (Submonoid.powers (f j)) _).symm
          ((e (Submonoid.powers (f j))).line.symm
            (cofactorBasisValue (u.baseChange (Localization.Away (f j))) (p j)
              (1 ⊗ₜ[A] v))))) ∧
    (∃! d : CofactorTarget A P Q c, ∀ i : Fin n,
      (e (Submonoid.powers (f i))).line (1 ⊗ₜ[A] d) =
        cofactorBasisValue (u.baseChange (Localization.Away (f i))) (p i) (1 ⊗ₜ[A] v))

/-- Local descent and uniqueness for an arbitrary differential between finite
projectives of constant ranks c and c+1. Source: Stacks Tag 0E9Y, displayed formula
and its omitted well-definedness check; Tags 00NX, 00EK, 00DM, 0C6F.
(blueprint: lem-sfb-cofactor-local-descent).

Proof: (1) Apply the finite-projective standard-free-cover theorem to both modules
and refine by products. Stalk ranks fix the basis lengths; zero charts admit either
length. (2) A splitting of P into a finite free module induces a splitting on each
exterior power; the exterior basis theorem makes the ambient exterior power finite
free. In particular J is finite projective. (3) The projective exterior scalar
comparisons give the pure-wedge and dual evaluation isomorphisms. Tensor localization
combines them, and exact localization identifies the cokernel. Their spanning-tensor
formulas give coherence under further localization. (4) Define the displayed basis
value. Adding u(x) to a lift produces repeated wedge factors and hence zero; no
injectivity is needed. (5) Expanding a change of basis by permutations multiplies the
positive wedge by its determinant and the dual by its inverse; the factors cancel,
including in characteristic two and for the empty basis. (6) These values match on
pairwise overlaps. CoverModuleExact glues them uniquely; separatedness proves
additivity, homogeneity and vanishing on u(P), hence descent to C. (7) On any further
localization, use the image of the original cover, basis independence and separatedness
to obtain the formula for any basis. The same argument proves uniqueness and cover
independence. For c=0 cover separatedness gives P=0 and the empty-wedge formula is the
canonical degree-one identification. In the zero ring all modules and maps are unique.
The proof dependencies are precisely the seven steps recorded in the DAG node. -/
theorem existsUnique_cofactor_local_descent {A : Type u} [CommRing A]
    (P : Type v) (Q : Type w) [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A P] [Module.Projective A P]
    [Module.Finite A Q] [Module.Projective A Q] (c : ℕ) (u : P →ₗ[A] Q)
    (hP : ∀ p : PrimeSpectrum A, Module.rankAtStalk P p = c)
    (hQ : ∀ p : PrimeSpectrum A, Module.rankAtStalk Q p = c + 1) :
    (∃ (n : ℕ) (f : Fin n → A), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i : Fin n,
        Nonempty (Module.Basis (Fin c) (Localization.Away (f i))
          (Localization.Away (f i) ⊗[A] P)) ∧
        Nonempty (Module.Basis (Fin (c + 1)) (Localization.Away (f i))
          (Localization.Away (f i) ⊗[A] Q))) ∧
    Module.Finite A (⋀[A]^c P) ∧ Module.Projective A (⋀[A]^c P) ∧
    ∃ e : ∀ S : Submonoid A, CofactorScalarComparison (Localization S) u c,
      CofactorComparisonsCoherent u c e ∧ CofactorCoverDescent u c e ∧
      ∃! w : (Q ⧸ LinearMap.range u) →ₗ[A] CofactorTarget A P Q c,
        IsLocalCofactor u c e w ∧
        (∀ hc : c = 0, Subsingleton P ∧ ∀ v : Q,
          (hc ▸ w) ((LinearMap.range u).mkQ v) =
            (exteriorPower.zeroEquiv (R := A) (M := P)).toLinearMap ⊗ₜ[A]
              (exteriorPower.oneEquiv (R := A) (M := Q)).symm v) := by
  sorry

end Module
