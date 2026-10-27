/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.StackQcohAbelian
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.ExactFunctor

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.FlatModulePullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf

/-! # Exact smooth pullback on quasi-coherent stack modules

Source: Stacks Project, stacks-cohomology.tex, Tags 076X and 0GQF;
stacks-morphisms.tex, Tags 075U and 06FM
(blueprint: lem-sfb-stack-smooth-qcoh-exact).

The smoothness hypothesis is the scheme-presentation condition of 075U/06FM.
The functors use the existing big-fppf precomposition and Zariski restriction,
lifted through the full quasi-coherent subcategories. Exactness means preservation
of finite limits and colimits, hence short exact sequences in the abelian categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Tensor pullback on the full quasi-coherent subcategories. The witness supplies
only the established continuity and quasi-coherence proofs: objects and arrows are
literal precomposition, canonically identified with tensor pullback by its
`tensor_comparison`, `tensor_sections` and `tensor_naturality` fields.
Source: Stacks 06WE and 076X (blueprint: lem-sfb-stack-smooth-qcoh-exact). -/
def moduliQcohPullback {S : Scheme.{u}}
    {Z X : BasedCategory.{v, w} (Over S)}
    {hZ : IsFibredInGroupoids Z} {hX : IsFibredInGroupoids X}
    {f : BasedFunctor Z X} (P : ModuliQuasicoherentPrecomposition hZ hX f) :
    ModuliQCoh X hX ⥤ ModuliQCoh Z hZ :=
  (SheafOfModules.isQuasicoherent (moduliModuleRings Z hZ)).lift
    ((SheafOfModules.isQuasicoherent (moduliModuleRings X hX)).ι ⋙
      @moduliModulePrecomposition S Z X hZ hX f P.continuous) P.quasicoherent

/-- Scheme-test restriction with its quasi-coherent codomain, using the dependency's
actual Zariski restriction functor and its local-presentation proof.
Source: Stacks 06WK and 076X (blueprint: lem-sfb-stack-smooth-qcoh-exact). -/
def moduliQcohSchemeRestriction {S : Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {hX : IsFibredInGroupoids X}
    (R : ModuliSchemeRestriction X hX) (x : X.obj) :
    ModuliQCoh X hX ⥤ SchemeTestQCoh.{u, max (u + 1) v w} (schemeTestBase X x) :=
  (SheafOfModules.isQuasicoherent
    (schemeTestModuleRings.{u, max (u + 1) v w} (schemeTestBase X x))).lift
      (R.restriction x) (R.quasicoherent x)

/-- Smooth tensor pullback is exact on quasi-coherent modules, with no representability
or finiteness assumption. The existential chart square is the scheme version of the
smooth-presentation definition (075U/06FM); its isomorphism fixes the square's arrows.
Source: Stacks 076X and 0GQF (blueprint: lem-sfb-stack-smooth-qcoh-exact).

Proof:
1. Restriction along any smooth surjective scheme atlas is faithful and preserves
   kernels and cokernels. Present the stack as its flat algebraic-space groupoid by
   lem-sfb-fppf-groupoid-stack-presentations. Apply lem-sfb-space-groupoid-module-descent
   and lem-sfb-flat-space-groupoid-kernels-cokernels. Compare the resulting small-etale
   restriction with the Zariski restriction by exists_moduliSchemeRestriction and
   lem-sfb-scheme-etale-module-exact-finiteness-comparison. The associated etale sheaf
   functor is exact and reflects isomorphisms, since restriction to opens is identity.
   Thus the Zariski atlas restriction is faithful and computes kernels and cokernels.
   These are the abelian structures of stack_qcoh_abelian by their universal properties.
2. Choose an atlas V of X and an atlas U of Z times_X V. By
   lem-sfb-algebraic-stack-fibre-products and
   lem-sfb-fibred-groupoid-representable-smooth-calculus, U maps smoothly and surjectively
   to Z. The smooth-presentation criterion gives a smooth scheme map q : U to V,
   hence flatness by sbc-lem-smooth-criterion. No representability of f is needed.
3. Restrict a short exact sequence to V. Scheme module kernels and cokernels remain
   quasi-coherent by isQuasicoherent_kernel and quasiCoherent_cokernel_image, so this
   is short exact also among all modules. Pull back by the flat q using
   flat_module_pullback_exact_pushforward_injective. The scheme-test tensor comparisons
   identify the result, including both arrows, with restriction of f's tensor pullback.
4. The faithful exact atlas restriction reflects zero objects. Apply it to the first
   kernel, last cokernel and middle homology to reflect short exactness back to Z.
   Additivity is checked on this same faithful atlas. In abelian categories this is
   equivalently preservation of finite limits and finite colimits. -/
theorem stack_smooth_qcoh_exact {S : Scheme.{u}}
    (Z X : BasedCategory.{v, w} (Over S))
    (hZ : IsAlgebraicModuliStack Z) (hX : IsAlgebraicModuliStack X)
    (f : BasedFunctor Z X)
    (_hsmooth : ∃ (U V : Over S)
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) Z)
      (b : BasedFunctor (discreteModuli (yoneda.obj V)) X) (q : U ⟶ V),
      IsSmoothModuliAtlas Z U a ∧ IsSmoothModuliAtlas X V b ∧ Smooth q.left ∧
        Nonempty (a.comp f ≅ (discreteModuliMap (yoneda.map q)).comp b))
    (P : ModuliQuasicoherentPrecomposition hZ.1.1 hX.1.1 f) :
    PreservesFiniteLimits (moduliQcohPullback P) ∧
      PreservesFiniteColimits (moduliQcohPullback P) := by
  sorry

/-- For a smooth scheme test, F maps to F_f exactly. Finite-limit preservation
includes kernels and monomorphisms, finite-colimit preservation includes cokernels;
together they give short-exact-sequence preservation in the quasi-coherent categories.
The expanded hypothesis says every scheme base change is a smooth algebraic space,
with no surjectivity requirement on the test.
Source: Stacks 076X, 0GQF and 03DX (blueprint: lem-sfb-stack-smooth-qcoh-exact).

Proof (step 5 of the node): identify the big-fppf quasi-coherent category of the test
scheme with its Zariski quasi-coherent modules using
scheme_big_fppf_quasicoherent_equivalence. The inverse equivalence is restriction to
opens and preserves kernels and cokernels by their Hom universal properties.
exists_moduliSchemeRestriction identifies its composite with tensor pullback with
F maps to F_f, including morphisms. Apply the preceding exactness assertion to this
smooth test. An exact additive functor preserves kernels and cokernels by factoring
an arrow through its image and applying it to the two resulting short exact sequences.
A monomorphism has zero kernel, so it too is preserved. -/
theorem stack_smooth_scheme_qcoh_restriction_exact {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsAlgebraicModuliStack X)
    (T : Over S) (f : BasedFunctor (discreteModuli (yoneda.obj T)) X)
    (_hsmooth : ∀ (W : Over S)
      (t : BasedFunctor (discreteModuli (yoneda.obj W)) X),
      ∃ (A : AlgebraicSpace S) (p : A.obj.obj ⟶ yoneda.obj W),
        HasSpaceBaseChange f W t A p ∧ SpaceMapIsSmooth A W p)
    (R : ModuliSchemeRestriction X hX.1.1) :
    PreservesFiniteLimits
      (moduliQcohSchemeRestriction R (f.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))) ∧
    PreservesFiniteColimits
      (moduliQcohSchemeRestriction R (f.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))) := by
  sorry

end CategoryTheory
