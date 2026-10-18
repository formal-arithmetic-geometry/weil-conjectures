/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.Paper.IndHeartKernelsCokernels
import Sheaf.Paper.IndConstructibleExtensions
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.ProperHeartBound
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Bounded-below proper direct image of ind-constructible complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-proper-unbounded-window,
`sk-lem-proper-unbounded-window-bounded-below.md` and its proof
(blueprint: det-proper-unbounded-window-bounded-below).

IndCons is the replete small filtered-colimit closure `ObjectProperty.ind` of the
finite constant-model constructibility predicate in the actual module-object category.
The condition on every cohomology object is precisely membership in Dic. The two
statements use the canonical condensed finite subextension and algebraic-closure rings.
The standing scheme setting is that of sk-def-sfb-dc-setting, as specified by the
proper-heart theorem used in the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image with coefficients in a finite subextension of ℚ_ℓ preserves
ind-constructible cohomology of bounded-below complexes and has the stated amplitude.
Source: blueprint sk-lem-proper-unbounded-window-bounded-below, both paragraphs of its proof;
standing setting: sk-def-sfb-dc-setting and sk-lem-proper-heart-bound
(blueprint: det-proper-unbounded-window-bounded-below).

Proof (the five steps of the node):
1. The module-object action is equivalently a sheafwise ring-module action by the
universal property of the sheaf tensor product. Apply
lem-pur-ringed-site-grothendieck-abelian to the two module categories. By
def-sfb-module-lower-star the functor is additive and left exact; by
sk-def-sfb-module-derived-pushpull its total right derived functor is computed on
K-injective resolutions in this same category. Choose a cohomological lower bound a₀
and canonically truncate a representative below a₀ to get a bounded-below representative.
Apply thm-sp-truncation-e2: E₂^{r,s} = Rʳp_* Hˢ(K) converges to H^{r+s}(Rp_*K),
with r ≥ 0, s ≥ a₀, and a finite exhaustive separated abutment filtration whose graded
pieces are E∞^{r,n-r}.
2. Every Hˢ(K) is ind-constructible. Apply sk-lem-proper-heart-bound to each:
the E₂ terms are ind-constructible and vanish for r > c = 2d+1.
3. By def-sp-exact-couple the next page is the outgoing kernel modulo the incoming
image. The image lies in the kernel because the differential squares to zero.
Apply det-ind-heart-kernels-cokernels first to the differentials, then to the map
from incoming image to outgoing kernel. Every next page is ind-constructible;
zero positions remain zero. All pages are supported in 0 ≤ r ≤ c. Since page-t
differentials have bidegree (t,1-t), choose t ≥ 2 and t > c: all differentials then
have zero source or target. The stable page is ind-constructible by finite induction,
also if the column interval is empty.
4. Start at the zero end of the finite abutment filtration and descend. Each successive
quotient is a stable-page term; det-ind-heart-extensions applied to each short exact
sequence puts every filtration term, hence Hⁿ(Rp_*K), in IndCons.
5. If K vanishes below a and n < a, every E₂ term of total degree n has s ≤ n < a
and is zero. If K vanishes above b and n > b+2d+1, every possible column has
s = n-r > b. In either case the stable terms and every graded piece vanish;
descending the finite filtration gives the claimed cohomological vanishing.
-/
theorem proper_indConstructible_boundedBelow
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.continuousMapRingObj E) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    (hbelow : ∃ a₀ : ℤ, K.IsGE a₀) :
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor.obj
        K).IsLE
        (b + 2 * d + 1)) := by
  sorry

/-- Proper direct image with coefficients in the condensed algebraic closure preserves
ind-constructible cohomology of bounded-below complexes and has the stated amplitude.
Source: blueprint sk-lem-proper-unbounded-window-bounded-below, both paragraphs of its proof;
standing setting: sk-def-sfb-dc-setting and sk-lem-proper-heart-bound
(blueprint: det-proper-unbounded-window-bounded-below).

Proof (the five steps of the node):
1. The module-object action is equivalently a sheafwise ring-module action by the
universal property of the sheaf tensor product. Apply
lem-pur-ringed-site-grothendieck-abelian to the two module categories. By
def-sfb-module-lower-star the functor is additive and left exact; by
sk-def-sfb-module-derived-pushpull its total right derived functor is computed on
K-injective resolutions in this same category. Choose a cohomological lower bound a₀
and canonically truncate a representative below a₀ to get a bounded-below representative.
Apply thm-sp-truncation-e2: E₂^{r,s} = Rʳp_* Hˢ(K) converges to H^{r+s}(Rp_*K),
with r ≥ 0, s ≥ a₀, and a finite exhaustive separated abutment filtration whose graded
pieces are E∞^{r,n-r}.
2. Every Hˢ(K) is ind-constructible. Apply sk-lem-proper-heart-bound to each:
the E₂ terms are ind-constructible and vanish for r > c = 2d+1.
3. By def-sp-exact-couple the next page is the outgoing kernel modulo the incoming
image. The image lies in the kernel because the differential squares to zero.
Apply det-ind-heart-kernels-cokernels first to the differentials, then to the map
from incoming image to outgoing kernel. Every next page is ind-constructible;
zero positions remain zero. All pages are supported in 0 ≤ r ≤ c. Since page-t
differentials have bidegree (t,1-t), choose t ≥ 2 and t > c: all differentials then
have zero source or target. The stable page is ind-constructible by finite induction,
also if the column interval is empty.
4. Start at the zero end of the finite abutment filtration and descend. Each successive
quotient is a stable-page term; det-ind-heart-extensions applied to each short exact
sequence puts every filtration term, hence Hⁿ(Rp_*K), in IndCons.
5. If K vanishes below a and n < a, every E₂ term of total degree n has s ≤ n < a
and is zero. If K vanishes above b and n > b+2d+1, every possible column has
s = n-r > b. In either case the stable terms and every graded piece vanish;
descending the finite filtration gives the claimed cohomological vanishing.
-/
theorem proper_indConstructible_boundedBelow_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ y : Y,
      topologicalKrullDim (pullback p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤
        if 0 ≤ d then (d.toNat : WithBot ℕ∞) else ⊥)
    (K : DerivedCategory (pulledBackModuleObjects (Profinite.padicAlgClRingObj ℓ) X))
    (hK : ∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj K))
    (hbelow : ∃ a₀ : ℤ, K.IsGE a₀) :
    (∀ n : ℤ, ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) Y)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K))) ∧
    (∀ a : ℤ, K.IsGE a →
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K).IsGE a) ∧
    (∀ b : ℤ, K.IsLE b →
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) p).rightDerivedFunctor.obj
        K).IsLE
        (b + 2 * d + 1)) := by
  sorry

end AlgebraicGeometry.ProEtale
