/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.ModuliInertia
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.StackTopologyOpenSubstacks
import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme
import Sheaf.AlgebraicGeometry.EtaleSpaceLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # The self-relation of an affine etale chart with finite inertia

Source: Stacks Project, stacks-morphisms.tex, Tags 0CL0, 0DU3 and 0DU4;
spaces-morphisms.tex, Tag 03XX; algebraic.tex, Tags 04T4 and 04WY
(blueprint: lem-sfb-dm-finite-inertia-affine-relation).

The open image itself is given its fppf quotient presentation. Thus its full inclusion
is the canonical quotient functor, with the original chart and its isomorphism arrows
retained, rather than an unspecified equivalence of orbit sets. The stabilizer is the
actual scheme pullback along the diagonal, and the residue-field fibre represents the
base change of inertia at the specified residue-field object.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- An affine etale chart of a finite-inertia DM stack has a separated etale scheme
self-relation, finite stabilizer, and quotient equal to its open image. No surjectivity
of the chart, separatedness of the base, or quasi-compactness of the relation is assumed.
The `SchemeGroupoidQuotientPresentation` identifies all arrows and their composition,
so the groupoid operations are the ones on isomorphism triples. Its target is the open
substack itself: this states the canonical identification `[V/R] = W` without choosing
a second stackification. The residue-fibre scheme test is precisely the automorphism functor of
`a(v)` on all schemes over its residue field, not just its rational automorphism group.
The point space of `W` is the image of `|V| → |X|` under `moduliPointMap`; its openness
is stated through `ModuliPointIsClosed` of the complement, i.e. tested on every etale
atlas (def-sfb-dm-stack-morphism-properties).

Source: Stacks Project, Tags 0CL0, 0DU3, 0DU4, 03XX, 04T4, 04WY and 050Q
(blueprint: lem-sfb-dm-finite-inertia-affine-relation).

Proof:
1. The etale atlas is smooth by lem-sfb-stack-chartwise-smooth-etale-calculus.
   The etale-to-fppf descent theorem makes the DM stack an fppf stack. Apply
   lem-sfb-self-relation-quotient-embedding to obtain the algebraic-space relation,
   its isomorphism-triple operations and the canonical fully faithful quotient map.
   Both projections are etale by lem-sfb-dm-etale-atlas-calculus.
2. The affine scheme V is absolutely separated: its diagonal is a closed immersion
   and hence proper. Apply lem-sfb-stack-separated-source-separated-inertia-target
   to a, then lem-sfb-representable-stack-diagonal-criterion: the relative diagonal
   of a is a closed immersion on every scheme test. This does not require S separated.
3. By lem-sfb-groupoid-diagonal-two-pullback-identities, the diagonal of either
   projection is a base change of that of a. Both projections are separated.
   Apply lem-a1-separated-etale-space-scheme to obtain the scheme R. Etaleness
   gives flatness and local finite presentation. The etale locally-quasi-finite
   lemma gives the Stacks finite-type-inclusive local quasi-finiteness predicate.
4. On every test scheme the pullback along the diagonal has arrows (v,v,alpha).
   Conjugation identifies this functor with V times_X I_X, compatibly with projection
   to V. It is finite by the inertia hypothesis. Base change by the canonical
   Spec kappa(v) -> V identifies the displayed fibre with automorphisms of a(v).
5. The flat locally finitely presented map a is open on point spaces by
   lem-sfb-stack-point-topology-flat-lfp-open. The open-substack classification
   gives W with this exact image. The chart factors through W, is surjective there,
   and remains representable etale. Hence W is DM and is fppf by the same descent.
6. Strict fullness identifies V times_W V with V times_X V, including arrows and
   composition. Apply lem-sfb-fppf-groupoid-stack-presentations to obtain the fppf
   quotient presentation of W. Its full inclusion is the canonical quotient map.
   Every scheme base change is an open immersion, hence etale by
   lem-weil-pbc-open-immersion-etale. Empty charts and empty stacks are included. -/
theorem dm_finite_inertia_affine_relation {S : Scheme.{u}}
    (X : BasedCategory.{v, w} (Over S)) (hX : IsDeligneMumfordModuliStack X)
    (hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X))
    (V : Over S) [IsAffine V.left]
    (a : BasedFunctor (discreteModuli (yoneda.obj V)) X)
    (ha : IsRepresentableByAlgebraicSpaces a) (het : IsEtaleModuliMap a) :
    ∃ (R : Over S) (s t : R ⟶ V)
      (e : V.left ⟶ R.left) (i : R.left ⟶ R.left)
      (c : pullback s.left t.left ⟶ R.left),
      IsGroupoidScheme s.left t.left e i c ∧
      (IsSeparated s.left ∧ Etale s.left ∧ Flat s.left ∧
        LocallyOfFinitePresentation s.left ∧ Scheme.Hom.IsLocallyQuasiFinite s.left) ∧
      (IsSeparated t.left ∧ Etale t.left ∧ Flat t.left ∧
        LocallyOfFinitePresentation t.left ∧ Scheme.Hom.IsLocallyQuasiFinite t.left) ∧
      (∃ E : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct a a),
        E.toFunctor.IsEquivalence ∧
        Nonempty (ModuliTwoIso (E.comp (moduliTwoFiberFst a a))
          (discreteModuliMap (yoneda.map s))) ∧
        Nonempty (ModuliTwoIso (E.comp (moduliTwoFiberSnd a a))
          (discreteModuliMap (yoneda.map t)))) ∧
      IsFinite (pullback.snd (prod.lift s t) (prod.lift (𝟙 V) (𝟙 V))).left ∧
      (∀ v₀ : V.left,
        ∀ r : Over.mk (V.left.fromSpecResidueField v₀ ≫ V.hom) ⟶ V,
          r.left = V.left.fromSpecResidueField v₀ →
          ∃ E : BasedFunctor (discreteModuli (yoneda.obj
              (pullback (pullback.snd (prod.lift s t) (prod.lift (𝟙 V) (𝟙 V))) r)))
              (moduliTwoFiberProduct ((discreteModuliMap (yoneda.map r)).comp a)
                (moduliInertiaProjection X)),
            IsSchemeModuliBaseChange E
              (pullback.snd (pullback.snd (prod.lift s t) (prod.lift (𝟙 V) (𝟙 V))) r)) ∧
      ∃ (W : OpenModuliSubstack X)
        (b : BasedFunctor (discreteModuli (yoneda.obj V)) W.category),
        b.comp (fullModuliInclusion X W.property) = a ∧
        Nonempty (SchemeGroupoidQuotientPresentation s t e i c W.category b) ∧
        Set.range (moduliPointMap (fullModuliInclusion X W.property)) =
          Set.range (moduliPointMap a) ∧
        ModuliPointIsClosed X (Set.range (moduliPointMap a))ᶜ ∧
        IsDeligneMumfordModuliStack W.category ∧
        ModuliSchemeTest @IsOpenImmersion (fullModuliInclusion X W.property) ∧
        IsEtaleModuliMap (fullModuliInclusion X W.property) := by
  sorry

end CategoryTheory
