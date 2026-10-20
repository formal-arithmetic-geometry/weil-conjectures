/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.Paper.UniformConstructibleExtTorsion

import Sheaf.Paper.FormalClosedSupport
import Sheaf.Paper.FormalClosedSupportII
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import Sheaf.Paper.IntegralModels

/-!
# The integral stratum Ext bound

Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-integral.md
(blueprint: det-uniform-constructible-ext-integral).

The Ext group is the morphism group from the degree-zero source to the shifted
degree-zero target in the unbounded derived category of integral coefficient modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The integral stratum bound, with the same standing setting as the torsion bound.
Source: blueprint main-20261015, sec-six-functors-basics,
sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext-integral.md
(blueprint: det-uniform-constructible-ext-integral).

Proof plan (the six steps of the DAG node):
1. Put Q = i_* u_! L₀ and N = kb_* vb_! M₀. Integral models, clauses (2) and (4),
identify their derived reductions with the extensions by zero of their lattice
reductions and make N derived complete. The definition of derived completion gives
N ≅ Rlim N_n, where N_n is the finite reduction regarded as an integral object by
restriction of scalars, with its quotient transition maps.
2. Set F = L₀^∨ ⊗ u^* RΓ_Z N and F_n = L₀^∨ ⊗ u^* RΓ_Z N_n in integral modules.
Local dual bases and inverse transpose transition matrices make L₀^∨ finite locally
free. Formal closed support II says that support followed by open restriction and
this tensor functor carry sequential derived-limit triangles to those of their images.
Thus F ≅ Rlim F_n; no finite-coefficient support comparison is assumed.
3. The formal closed-support formula identifies RHom(Q,N) with RΓ(S,F), and similarly
for N_n and F_n. The ringed-site derived-sections/derived-limit theorem gives
RΓ(S,F) ≅ Rlim B_n in D(Ab), with B_n = RΓ(S,F_n). Consequently Ext^q(Q,N) is
H^q(Rlim B_n), and H^q(B_n) is Hom(Q,N_n[q]) in the integral derived category.
4. The derived extension/termwise restriction adjunction for O_E → O_E/π^n and the
source reduction from integral models identify H^q(B_n) with finite-coefficient
Ext^q(a_!(L₀/π^n),b_!(M₀/π^n)). This adjunction requires no flatness and compares
groups in distinct coefficient categories rather than identifying those categories.
5. Formal closed support over the finite quotient and the equality
(L₀/π^n)^∨ = L₀^∨/π^n, checked in local bases and glued, express that finite Ext as
the torsion stratum complex's cohomology. Torsion clause (2) kills it for
q > c = cd_ℓ(j) + cd_ℓ(S) + 1, uniformly in n.
6. The Milnor short exact sequence has outer terms R¹lim H^(q-1)(B_n) and
lim H^q(B_n). For q > c+1 both cohomology towers are zero, hence so are both end
terms, and exactness kills Ext^q(Q,N). No Mittag-Leffler hypothesis is needed.
An infinite dimension makes the asserted degree range empty. The comparison using
q.toNat is exact: every integer above the nonnegative cutoff is positive. -/
theorem uniformConstructibleExtIntegral
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (u : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion u.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (q : ℤ)
    (hq : torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 2 <
      (q.toNat : WithTop ℕ)) :
    Subsingleton
      (((DerivedCategory.singleFunctor
          (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
        ((lowerStar (DerivedNakayama.integerRing ℓ E) i.left).obj
          ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) u.left).obj L₀))) ⟶
        ((DerivedCategory.singleFunctor
            (FormalSupportModules (DerivedNakayama.integerRing ℓ E) X.left) 0).obj
          ((lowerStar (DerivedNakayama.integerRing ℓ E) kb.left).obj
            ((openImmersionLowerShriek (DerivedNakayama.integerRing ℓ E) vb.left).obj
              M₀))) ⟦q⟧) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
