/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.CoefficientHeart
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Sheaf.Paper.FormalClosedSupport
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# A uniform Ext bound for rational constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
_section.md and sk-lem-uniform-constructible-ext.proof.md
(blueprint: sk-lem-uniform-constructible-ext).

Ext is formed in the ambient abelian category of all module objects over the pulled-back
condensed ring, hence in its ordinary unbounded derived category. The second conjunct
retains the explicit bound for an open immersion followed by a closed immersion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Every rational constructible sheaf has a bound on Ext uniform in all constructible
second arguments. For `a = i ∘ v`, the bound is exactly `cd_ℓ(j) + cd_ℓ(S) + 2`.
The base field is the fixed finite field or its algebraic closure, expressed invariantly
by a field isomorphism. Natural-number degrees and bounds encode the nonnegative-integer
convention: a degree strictly above such a bound is necessarily nonnegative.
The qcqs instances in the stratum clause only supply the domains of `sk-def-cd`; they
hold for every locally closed stratum and complementary open of the standing scheme.

Source: blueprint sk-lem-uniform-constructible-ext, statement and its four-step DAG proof
(blueprint: sk-lem-uniform-constructible-ext).

Proof plan:
1. The global finite-field datum and sk-def-sf-setting put X in sk-def-sfb-dc-setting.
By sk-lem-base-field-cd the base has finite ell-cohomological dimension. The finite-type
bounds of sk-def-cd make cd_ell(S) and cd_ell(j) finite. Empty strata cause no exception.
2. Apply det-uniform-constructible-ext-rational to a lisse L on S and every locally
closed b:T -> X and lisse M on T. Its bound is independent of b and M. The torsion
estimate det-uniform-constructible-ext-torsion has cutoff cd_ell(j)+cd_ell(S)+1;
det-uniform-constructible-ext-integral adds one for the derived inverse limit of the
reductions modulo powers of the uniformizer. The support fibre formula of
sk-lem-formal-closed-support and its limit compatibility in sk-lem-formal-closed-support-ii
are the support and inverse-limit constructions used there. The rational stratum lemma
includes passage to E and Qbar_l; it does not assume a global integral lattice in L.
3. Filter an arbitrary constructible N by sk-lem-coefficient-heart(3). Induct along
its exact subobject filtration. The exact segment from lem-sc-abelian-ext-covariant-exact
has outer terms Ext^q(a_!L,N_previous) and Ext^q(a_!L,b_!M), both zero above the same
cutoff. Its middle term vanishes, with no dependence on the target filtration length.
4. Fix the finite source filtration of C from sk-lem-coefficient-heart(3). Take the
maximum of zero and the finitely many stratum cutoffs. Induct along this filtration,
using lem-coef-ext-contravariant-six-term: Ext^q(a_!L,N) -> Ext^q(C_step,N) ->
Ext^q(C_previous,N) has zero outer terms. This gives the first conjunct for every N
simultaneously. The empty filtration gives d_0=0. For a single stratum apply step 3
directly to obtain the second conjunct. The two extra degrees are the closed-support
cone degree and the derived inverse-limit degree, respectively. -/
theorem uniformConstructibleExt
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (_hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k]
    (_hk : Nonempty (k ≃+* D.k₀) ∨ Nonempty (k ≃+* D.k))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ C : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
      ∃ d : ℕ, ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
        ∀ q : ℕ, d < q → Subsingleton (Abelian.Ext C.obj N.obj q)) ∧
    (∀ (S Z U : Scheme.{u}) (v : S ⟶ Z) (i : Z ⟶ X) (j : U ⟶ X)
      [IsOpenImmersion v] [IsClosedImmersion i] [IsOpenImmersion j]
      [CompactSpace S] [QuasiSeparatedSpace S] [QuasiCompact j],
      Set.range i.base = (Set.range j.base)ᶜ →
      ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) S),
        IsLisseCoefficientModule (coefficientHeartRingObj Λ) L →
        ∃ d : ℕ,
          (d : WithTop ℕ) = relativeCohomologicalDimension ℓ (Fact.out : ℓ.Prime) j +
            cohomologicalDimension ℓ (Fact.out : ℓ.Prime) S + 2 ∧
          ∀ N : ConstantModelConstructible (coefficientHeartRingObj Λ) X,
            ∀ q : ℕ, d < q →
              Subsingleton (Abelian.Ext
                ((CondensedRing.lowerStar (coefficientHeartRingObj Λ) i).obj
                  ((CondensedRing.openImmersionLowerShriek (coefficientHeartRingObj Λ) v).obj L))
                N.obj q)) := by
  sorry

end AlgebraicGeometry.ProEtale
