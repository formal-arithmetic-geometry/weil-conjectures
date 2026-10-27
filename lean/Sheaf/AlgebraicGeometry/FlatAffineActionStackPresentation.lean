/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q87
-/
module

public import Sheaf.AlgebraicGeometry.AffineActionStackPresentation
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # An fppf presentation of an affine action quotient

Source: Stacks Project, criteria.tex, Tags 06FI and 06FH; spaces-groupoids.tex,
Tag 04M9; stacks-morphisms.tex, Tag 06R7
(blueprint: lem-sfb-flat-affine-action-stack-presentation).

We use the scheme-action formulation of a rational action. On affine schemes,
`ModObj H (affineActionScheme k E)` is equivalently an algebra coaction
`E → E ⊗[k] k[H]`: the right action dual to the coaction is converted to the
left action by `h • x = x · h⁻¹`. Inversion does not change the invariant ring.
The imported `affineInvariants` is its equalizer on regular functions, using
the actual action and projection after swapping the two factors. The quotient and
its canonical map are the existing scheme-torsor
constructions, which do not assume smoothness. No chosen quotient or invariant map
is an input to the theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v₁ w₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace AlgebraicGeometry.SchemeAction

variable (k E : Type u) [Field k] [CommRing E] [Algebra k E]
variable (H : Over (Spec (CommRingCat.of k))) [GrpObj H]
variable [ModObj H (affineActionScheme k E)]

/-- Affine action quotients admit an fppf presentation even for non-smooth groups.
Quasi-separatedness and the affine diagonal are expressed relative to Spec k;
these agree with the absolute properties, since Spec k is separated over Spec Z.
The existential functor is the descent of the specified invariant inclusion,
as recorded by its actual 2-isomorphism on the trivial-torsor presentation.
Source: Stacks 06FI, 06FH, 04M9, 04WM, 06R7, 04YC and 075S
(blueprint: lem-sfb-flat-affine-action-stack-presentation).

Proof:
1. The field-module flatness lemma and the affine flatness criterion make H flat.
Finite type over the Noetherian field implies finite presentation. The left action
defines R = H × U with s(h,u)=u and t(h,u)=hu, inverse (h,u)↦(h⁻¹,hu), and
composition (h,gu)∘(g,u)=(hg,u). Both s and t are flat and locally finitely presented
by the chartwise calculus and the affine fibre-product and affine-Hom lemmas.
2. Apply lem-sfb-flat-groupoid-algebraic-quotient (06FI, 06FH), then
lem-sfb-affine-group-torsor-stackification (04WM). This identifies its quotient and
presentation with torsorGroupoid and quotientAtlas. It proves algebraicity,
representability, flatness, local finite presentation and surjectivity of the latter.
3. Pull back the diagonal to U × U. It becomes (t,s):H × U → U × U, a map
of affine schemes. Apply lem-sfb-representable-stack-fppf-locality and affine
morphism permanence. The absolute diagonal follows by the closed equalizer of
the two maps to Spec k, since k ⊗_Z k → k is surjective. Affine morphisms are qcqs.
4. After any algebraic-stack base change, take a smooth scheme atlas of the target.
The resulting map of spaces is flat and locally finitely presented, hence open by
lem-sfb-flat-lfp-space-universally-open. Field objects in the 2-fibre product show
that inverse image commutes with its image of an open. The atlas quotient topology
of lem-sfb-stack-point-topology descends openness; surjectivity survives base change.
5. Spec E is quasi-compact by affine-scheme qcqs. Apply
lem-sfb-algebraic-stack-quasicompact-surjection to quotientAtlas.
6. The invariant inclusion equalizes the action and projection. On every fppf
torsor trivialization it therefore gives maps to Spec E^H agreeing on overlaps.
Use lem-trf-fppf-covering-is-fpqc and lem-weil-pbc-fpqc-representable-descent
to glue them uniquely. Uniqueness gives the functor and its displayed comparison.
7. Spec E^H is affine even without finite generation. Apply
lem-sfb-algebraic-stack-qcqs-permanence to this quasi-separated target and the
quasi-compact, quasi-separated source to obtain qcqs of the descended morphism. -/
theorem flat_affine_action_stack_presentation [Algebra.FiniteType k E]
    [IsAffineHom H.hom] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom] :
    IsAlgebraicModuliStack (torsorGroupoid H (affineActionScheme k E)) ∧
    IsQuasiCompactModuli (torsorGroupoid H (affineActionScheme k E)) ∧
    IsQuasiSeparatedAlgebraicModuliMap
      (moduliBaseStructure (torsorGroupoid H (affineActionScheme k E))) ∧
    ModuliSchemeTest @IsAffineHom (moduliRelativeDiagonal
      (moduliBaseStructure (torsorGroupoid H (affineActionScheme k E)))) ∧
    IsRepresentableByAlgebraicSpaces (quotientAtlas H (affineActionScheme k E)) ∧
    ModuliSpaceTest @Flat (quotientAtlas H (affineActionScheme k E)) ∧
    ModuliSpaceTest @LocallyOfFinitePresentation (quotientAtlas H (affineActionScheme k E)) ∧
    IsSurjectiveModuliMap (quotientAtlas H (affineActionScheme k E)) ∧
    (∀ (Z : BasedCategory.{v, w} (Over (Spec (CommRingCat.of k))))
      (g : BasedFunctor Z (torsorGroupoid H (affineActionScheme k E))),
      IsAlgebraicModuliStack Z →
        IsOpenMap (moduliPointMap (moduliTwoFiberFst g
          (quotientAtlas H (affineActionScheme k E)))) ∧
        Function.Surjective (moduliPointMap (moduliTwoFiberFst g
          (quotientAtlas H (affineActionScheme k E))))) ∧
    ∃ φ : BasedFunctor (torsorGroupoid H (affineActionScheme k E))
        (discreteModuli (yoneda.obj (affineInvariantSpectrum k E H))),
      Nonempty (ModuliTwoIso ((quotientAtlas H (affineActionScheme k E)).comp φ)
        (discreteModuliMap (yoneda.map (affineInvariantProjection k E H)))) ∧
      IsQuasiCompactAlgebraicModuliMap.{u, u, u + 1, u, u + 1, v₁, w₁} φ ∧
      IsQuasiSeparatedAlgebraicModuliMap φ := by
  sorry

end AlgebraicGeometry.SchemeAction
