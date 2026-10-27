/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
import Sheaf.AlgebraicGeometry.StablePointedCurve
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.PicardSemicontinuity
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import Sheaf.AlgebraicGeometry.ProperFlatGlobalSections
import Sheaf.AlgebraicGeometry.ProperCurveBundlePullbackDegree
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Sheaf.AlgebraicGeometry.DegreeWeightedIrreducibleComponents
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import Sheaf.AlgebraicGeometry.FppfLocalOpenSubfunctorDescent
import Sheaf.TraceFormula.ProjectiveBundleProper
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective

/-! # The multidegree-zero open subgroup of the relative Picard space

Source: Deligne, Le lemme de Gabber, §2, printed pp.135--136
(blueprint: lem-sfb-nodal-multidegree-zero-locus).

The representing space has small section sets; `e` identifies their universe lift
with the existing fppf Picard sheaf. The characterization is on all line-bundle
representatives on all test schemes, so it also specifies independence of the
fppf-local representative. The canonical Picard group law specifies the subgroup.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a locally Noetherian base and a stable unpointed family of genus at least two,
the fibrewise multidegree-zero classes form a quasi-compact separated open subgroup
of the relative Picard algebraic space. Here the base of `X` is `X.base.left`;
the auxiliary `B` only records its scheme-over-a-base presentation. The equivalence
for every line `L` identifies this subgroup after every fppf refinement, and hence
makes its condition independent of the representative. Degree is the existing
Euler-characteristic difference on the canonical normalized reduced component.

Source: Deligne, Le lemme de Gabber, §2, printed pp.135--136
(blueprint: lem-sfb-nodal-multidegree-zero-locus).

Proof (the node's seven steps):
1. Stability supplies a flat finitely presented projective family of connected
   reduced nodal curves. Projective-bundle properness and universal global sections
   give universally trivial structure-sheaf pushforward: in a rank-one algebra,
   writing 1 = ce and e² = de gives cd = 1. Apply the relative-curve Picard theorem
   to obtain smoothness, local finite presentation and an immersion diagonal.
2. Picard classes have fppf-local line representatives. Base lines restrict trivially
   to geometric fibres. Degree is invariant under isomorphism and field extension,
   additive under tensor product, and negated by dualization. Thus the condition
   descends and is preserved by multiplication and inverse. The finite birational
   normalization of each reduced component preserves its degree.
3. Locally on the Noetherian base choose a relatively very ample line H with
   constant total degree h. Its normalized component degrees satisfy 0 < h_Z ≤ h.
   Put N = h+1. For any representative L, both H tensor L^N and H tensor L^(-N)
   have positive component degrees exactly when all degrees of L vanish. The
   fibre-degree ample criterion and relative ample-locus theorem make this an open
   condition on every test scheme, compatible with base change.
4. Refine a presentation of P until universal classes have line representatives.
   Fppf-local open-subfunctor descent represents the condition by an open subspace.
   Tensor and dual closure from step 2 make it an open subgroup algebraic space.
5. With m = 2g+1 and d = mh, the finite-type parameter scheme of degree-d smooth
   divisors maps to P by E ↦ O(E) tensor H^(-m). Its inverse image of D is a
   quasi-compact open in a Noetherian scheme. The uniform smooth-divisor theorem
   makes it surjective on geometric points. The quasi-compact atlas criterion,
   also after affine base changes, gives quasi-compactness over the base.
6. A nonzero section of a multidegree-zero line on a geometric fibre is nowhere
   zero on each normalized component where it is nonzero, by section-degree
   positivity. Equality of the two branch residues at a node propagates this
   property across the connected component graph. It trivializes the line.
   Thus triviality is equivalent to h^0 ≥ 1, and h^0(O) = 1.
7. The diagonal is an immersion by step 1 and base change. Locally represent the
   difference of two sections by M. Step 6 identifies the diagonal image with
   h^0(M) ≥ 1. Flat base change and upper semicontinuity make this image closed
   on arbitrary, possibly nonreduced test schemes. Flat finitely presented covers
   are open, so closedness descends. An immersion with closed image is a closed
   immersion. Therefore D is separated. -/
theorem exists_nodal_multidegreeZero_openSubgroup
    {B : Scheme.{u}} {g : ℕ} (X : StablePointedModuli B g 0)
    [IsLocallyNoetherian X.base.left] (P : AlgebraicSpace X.base.left)
    (e : P.obj.obj ⋙ uliftFunctor.{u + 1, u} ≅ (picardFunctor X.projection).obj) :
    ∃ (D : AlgebraicSpace X.base.left) (j : D ⟶ P),
      AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
        j.hom.hom ∧
      AlgebraicSpace.IsQuasiCompactPresheafMap (terminal.from D.obj.obj) ∧
      AlgebraicSpace.IsSeparatedPresheafMap (terminal.from D.obj.obj) ∧
      (∀ T : Over X.base.left,
        ∃ K : Subgroup ((picardFunctorGrp X.projection).obj (op T)),
          ∀ z : (picardFunctorGrp X.projection).obj (op T),
            z ∈ K ↔ (e.inv.app (op T) z).down ∈ Set.range (j.hom.hom.app (op T))) ∧
      (∀ (T : Over X.base.left) (L : (pullback X.projection T.hom).Modules)
          (_ : L.IsInvertible),
        (e.inv.app (op T) ((toPicardFunctor X.projection).app (op T)
          (Scheme.Pic.ofIsInvertible L))).down ∈ Set.range (j.hom.hom.app (op T)) ↔
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (a : Spec (.of Ω) ⟶ T.left)
          (Z : irreducibleComponents (pullback (C := Scheme.{u})
            (pullback.snd (C := Scheme.{u}) X.projection T.hom) a)),
          @Scheme.Modules.degree Ω _
            ((pullback (C := Scheme.{u})
              (pullback.snd (C := Scheme.{u}) X.projection T.hom) a).reducedNormalizationComponent
                Z).normalization
            ⟨(pullback (C := Scheme.{u})
                (pullback.snd (C := Scheme.{u}) X.projection T.hom) a).normalizedComponentMap Z ≫
              pullback.snd (pullback.snd (C := Scheme.{u}) X.projection T.hom) a⟩
            ((Scheme.Modules.tensorPullback
              ((pullback (C := Scheme.{u})
                (pullback.snd (C := Scheme.{u}) X.projection T.hom) a).normalizedComponentMap Z ≫
                pullback.fst
                  (pullback.snd (C := Scheme.{u}) X.projection T.hom) a)).obj L) = 0) := by
  sorry

end AlgebraicGeometry
