/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FormalClosedSupportFiber
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# The torsion stratum bound: the support window

Source: latest blueprint, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
`sk-lem-uniform-constructible-ext-torsion.md`, clause (1), and the opening paragraph and
paragraph (1) of its proof; Stacks Tags 099Y, 09AF and 09A6
(blueprint: det-uniform-constructible-ext-torsion-support).

The coefficients are the continuous condensed integer ring and its actual finite
quotients. The definitions below (moved here from `Sheaf.Paper.UniformConstructibleExtTorsion`,
which re-exports them) assemble the quotient sheaf and the supported complex from the
recorded module operations. Cohomological cutoffs belong to `WithTop ℕ`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Clause (1) of the torsion stratum bound: RΓ_Z b_!(M₀/π^n) lies in degrees
`[0, cd_ℓ(j)+1]` and has classical cohomology sheaves.
Source: latest blueprint, sk-lem-uniform-constructible-ext-torsion, clause (1), opening
paragraph and paragraph (1) of the proof; Stacks Tags 099Y, 09AF, 09A6
(blueprint: det-uniform-constructible-ext-torsion-support).

Proof: A = O_E / π^n is finite and killed by ℓ^n, since ℓ lies in the maximal ideal
(π); in a local finite free basis the reduction F = M₀/π^n is A^r, a locally constant
sheaf with finite stalks. Standing schemes are Noetherian, so j and k_b are qcqs, and the
module categories are Grothendieck abelian with enough injectives. By Tag 099Y, F descends
to a lisse étale sheaf on T; by Tags 09AF and 09A6, open extension by zero and the closed
direct image commute with the comparison pullback, so N = k_* v_! F is classical, and so is
j^*N. Tag 09A6 identifies Rj_* j^*N with the pullback of its étale counterpart: it has
classical cohomology, vanishing in negative degrees (injective resolution in nonnegative
degrees) and above c = cd_ℓ(j) (definition of cd_ℓ). Part (1) of the formal closed support
lemma gives RΓ_Z N = i^* fib(N → Rj_* j^*N). The long exact sequence puts this fibre in
[0, c+1] (H⁰ and H¹ are a kernel and cokernel of a map of classical sheaves, H^r = H^{r-1}
of Rj_* j^*N for r ≥ 2), with classical cohomology since comparison is exact and fully
faithful; exact i^* preserves both. If c = ⊤ only the lower bound is asserted. -/
theorem uniformConstructibleExtTorsion_support
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (_hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (n : ℕ) (_hn : 1 ≤ n) :
    (∀ q : ℤ, q < 0 ∨ torsionStratumRelativeDimension ℓ k j + 1 <
        (q.toNat : WithTop ℕ) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n))) ∧
      (∀ q : ℤ, IsClassicalAbelian
        ((DerivedCategory.homologyFunctor _ q).obj
          (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n)).X) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
