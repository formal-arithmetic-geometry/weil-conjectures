/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.OpenTorBoundFiniteConstantTests
import Sheaf.Paper.OpenTorBoundStalkFilteredExtension

/-!
# Open direct image Tor bound over an arbitrary field

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`,
Step 3, passage from finite constant-module Tor tests for `Rj_* L` to all module
sheaves by stalks and filtered unions (blueprint: lem-sf-open-tor-bound-arbitrary-field).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Finite constant-module projection tests imply the all-module-sheaf Tor bound for an
open immersion over a field of positive characteristic.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-sf-rf-shriek-preservation/sk-prop-sf-rf-shriek-preservation.proof.md`,
Step 3 (blueprint: lem-sf-open-tor-bound-arbitrary-field).

Proof, following the six steps of the node:

1. For a finite `A`-module `M`, put `E_M = L ⊗ᴸ_A M_V`. The constant sheaf is a
   degree-zero sheaf, so the Tor hypothesis bounds the cohomology of `E_M` in `[a,b]`.
   Thus `E_M` is bounded below, without assuming finite projective dimension of `M`.
   Dependencies: def-kun-constant-sheaf, def-kun-derived-tensor, def-kun-tor-amplitude.

2. Enough injectives and the bounded-below injective representative theorem give a model
   `I_M` of `E_M` which is zero below `a`. Applying `j_*` computes its derived direct
   image and leaves the model zero below `a`, since the direct image is additive.
   Dependencies: lem-weil-pbc-module-sheaves-enough-injectives,
   lem-weil-pbc-dplus-injective-representative,
   lem-weil-pbc-module-direct-image-left-exact, lem-weil-pbc-right-derived-plus-injective.

3. Apply lem-sf-finite-cd-derived-upper-bound to `j_*`, `N=e`, and the upper bound `b`.
   The hypothesis on all sheaves supplies the finite cohomological dimension bound.
   The total derived functor and the bounded-below derived functor agree here: the
   bounded-below injective model is K-injective, every total right derived functor is
   computed on it, and any other K-injective resolution is homotopy equivalent to it.
   Hence `Rj_*E_M` lies in `[a,b+e]`. The assumed canonical projection isomorphism
   transfers this bound to `(Rj_*L) ⊗ᴸ_A M_T`.
   Dependencies: lem-sf-finite-cd-derived-upper-bound,
   lem-weil-pbc-module-sheaves-enough-injectives,
   lem-weil-pbc-module-direct-image-left-exact,
   prop-weil-pbc-kinjective-resolutions-exist, lem-weil-pbc-kinjective-total-derived.

4. At a geometric point `t` of `T`, put `C=(Rj_*L)_t`. Derived stalks are pullbacks
   and commute with derived tensor and cohomology. The stalk of `M_T` is `M`;
   naturality for scalar endomorphisms makes this identification `A`-linear. Thus
   `H^r(C ⊗ᴸ_A M)=0` outside `[a,b+e]` for every finite `M`. Forgetting scalar action
   preserves kernels, images and quotients, so the abelian-sheaf stalk statements
   apply to module-sheaf cohomology.
   Dependencies: lem-kun-stalk-as-pullback, lem-kun-inverse-image-monoidal,
   lem-kun-stalks-of-cohomology, lem-weil-pbc-constant-sheaf-geometric-stalk.

5. Every module `N` is the small filtered colimit of its finitely generated submodules.
   They contain zero, any two lie in their sum, and every element lies in a cyclic
   submodule. Each is finite because it is a quotient of a finite power of the finite
   ring `A`. Apply lem-pc-filtered-colimit-derived-tensor with both rings equal to `A`,
   a complex representing `C`, and the degree-zero submodule complexes. Cohomology
   of `C ⊗ᴸ_A N` is the colimit of the cohomologies tested in step 4, so it vanishes
   outside `[a,b+e]`. No commutation of `Rj_*` with colimits is needed.

6. For any module sheaf `F` on `T`, apply step 5 with `N=F_t` at every geometric point.
   Stalk compatibility gives zero stalks of every cohomology sheaf of
   `(Rj_*L) ⊗ᴸ_A F` outside `[a,b+e]`. Conservativity of geometric stalks, applied
   to the underlying abelian sheaf's map to zero, gives vanishing as a module sheaf.
   This is the all-module-sheaf Tor amplitude of `Rj_*L`.
   Dependencies: lem-kun-stalk-as-pullback, lem-kun-inverse-image-monoidal,
   lem-kun-stalks-of-cohomology, lemma-weil-pbc-geometric-stalk-conservative,
   def-kun-tor-amplitude. -/
theorem open_tor_bound_arbitrary_field
    (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, ∀ x : A, (l ^ n) • x = 0)
    {V T : Scheme.{u}}
    (aV : V ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    [LocallyOfFiniteType aT] [QuasiCompact aT]
    (j : V ⟶ T) (_hj : j ≫ aT = aV) [IsOpenImmersion j] [QuasiCompact j]
    (a b e : ℤ) (_hab : a ≤ b) (_he : 0 ≤ e)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hL : DerivedCategory.hasTorAmplitudeIn A V a b
      (DerivedCategory.Plus.ι.obj L))
    (_hvanish : ∀ (q : ℤ)
      (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)),
      e < q → IsZero
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F))))
    (_hproj : ∀ (M : ModuleCat.{u + 1} A), Finite M → IsIso
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app
        (DerivedCategory.Plus.ι.obj L)).app
        ((_root_.DerivedCategory.singleFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
          ((constantSheaf T.smallEtaleTopology
            (ModuleCat.{u + 1} A)).obj M)))) :
    DerivedCategory.hasTorAmplitudeIn A T a (b + e)
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
        (DerivedCategory.Plus.ι.obj L)) := by
  apply open_tor_bound_stalk_filtered_extension A a (b + e)
  exact open_tor_bound_finite_constant_tests p k l _hl A hA aV aT j _hj a b e _hab _he L _hL
    _hvanish _hproj

end AlgebraicGeometry.Etale
