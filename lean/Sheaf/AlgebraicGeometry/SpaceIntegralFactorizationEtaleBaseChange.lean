/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction

/-!
# Étale base change of the universal integral factorization

Source: Stacks Project, Morphisms of Spaces, Tag 0ABP(1)
(lemma-properties-normalization), characterized by Tag 0823
(lemma-characterize-normalization)
(blueprint: lem-sfb-space-integral-factorization-etale-base-change).

The fibre products are arbitrary cartesian squares of fppf sheaves. The two projection
identities specify the induced map between them. Integrality is representability with
integral scheme projections, using the existing scheme-test interface.

Quasi-compactness uses the existing affine-test atlas predicate. For algebraic spaces
this equals the all-quasi-compact-scheme-test condition: a quasi-compact test scheme
has a finite affine open cover, and the corresponding quasi-compact scheme atlases
assemble by finite disjoint union. The converse follows by testing on affine schemes.
The plain predicates are owned by def-sfb-space-quasi-compact-presheaf-map and
def-sfb-presheaf-map-separated-diagonal; no étale-locality theorem is a statement input.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universal integral factorization of a quasi-compact separated algebraic-space
morphism remains universal after representable étale base change.
Source: Stacks Project, Morphisms of Spaces, Tags 0ABP(1) and 0823
(blueprint: lem-sfb-space-integral-factorization-etale-base-change).

Proof:
1. Put A = f_* O_Y, using the canonical small-étale module direct image of
   def-trf-space-etale-module-functors. The structure module is quasi-coherent by its
   identity presentation. Thus lem-trf-space-qc-separated-quasi-coherent-pushforward
   makes A quasi-coherent. Apply lem-sfb-space-quasicoherent-integral-closure to obtain
   its integral-closure subalgebra C. By lem-sfb-space-relative-spec-correspondence,
   B = Spec_X C is affine and integral over X, since its affine-chart sections are integral.
2. For v : Z → X and a quasi-coherent algebra D, maps Z → Spec_X D over X are sections
   of its base change to Z, hence algebra maps v^* D → O_Z by the relative-Spec
   equivalence. Pullback preserves quasi-coherence by
   lem-sfb-space-module-pullback-quasicoherent. The tensor adjunction identifies these
   with algebra maps D → v_* O_Z: the formulas are pushforward followed by the unit,
   and pullback followed by the counit. On tensors the second is r tensor d mapped
   to r times the image of d; the inverse restricts to 1 tensor d. These preserve
   scalars, products and units, and the triangle identities make them inverse.
   Apply this mapping rule to C → A to obtain j : Y → B over X.
3. An integral q : T → X is affine, hence T = Spec_X D by the relative-Spec
   correspondence. A map a : Y → T gives an algebra map D → A. Applying it to each
   monic relation puts its image in C on every affine étale chart. These maps glue
   uniquely through the subalgebra inclusion. Relative Spec gives the unique
   k : B → T with j followed by k equal to a and k followed by q equal to b : B → X.
4. The given initial property and that of (j,b) give inverse maps u : N → B and
   v : B → N respecting the factorizations. Their composites are identities by
   uniqueness. Pull back both maps to W; their identities remain identities and
   the resulting isomorphism carries i_W to j_W.
5. By lem-trf-space-etale-module-pushforward-restriction, restriction along W → X
   identifies A|_W with (f_W)_* O_{Y_W}, and tensor pullback with restriction. The
   restricted algebras are quasi-coherent by the pullback theorem. Each affine étale
   chart over W is one over X, with the same sections. Thus C|_W is exactly the
   integral closure in A|_W by lem-sfb-space-quasicoherent-integral-closure. The
   relative-Spec base-change correspondence identifies B ×_X W with Spec_W(C|_W)
   and j_W with the restricted inclusion. The chartwise integral criterion makes
   this relative spectrum integral over W.
6. Given (q_W,a_W), repeat step 3 over W to obtain its unique extension from
   B ×_X W. Compose with u_W to obtain h_W. Composing any competing extension with
   v_W reduces uniqueness to step 3. The same isomorphism transports integrality
   of B ×_X W → W to n_W, on every scheme test. -/
theorem integralFactorization_etale_baseChange
    {S : Scheme.{u}} {Y X N W YW NW : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Y ⟶ N) (n : N ⟶ X)
    (_hfactor : i ≫ n = f)
    (_hqc : IsQuasiCompactPresheafMap f.hom.hom)
    (_hsep : IsSeparatedPresheafMap f.hom.hom)
    (_hn : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) n.hom.hom)
    (_huniversal : ∀ (T : AlgebraicSpace S) (q : T ⟶ X) (a : Y ⟶ T),
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) q.hom.hom →
        a ≫ q = f → ∃! h : N ⟶ T, i ≫ h = a ∧ h ≫ q = n)
    (w : W ⟶ X) (_hw : IsEtale w.hom.hom)
    (pY : YW ⟶ Y) (fW : YW ⟶ W) (pN : NW ⟶ N) (nW : NW ⟶ W)
    (_hY : IsPullback pY.hom fW.hom f.hom w.hom)
    (_hN : IsPullback pN.hom nW.hom n.hom w.hom)
    (iW : YW ⟶ NW) (_hiY : iW ≫ pN = pY ≫ i) (_hiW : iW ≫ nW = fW) :
    IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) nW.hom.hom ∧
      ∀ (TW : AlgebraicSpace S) (qW : TW ⟶ W) (aW : YW ⟶ TW),
        IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) qW.hom.hom →
          aW ≫ qW = fW →
            ∃! hW : NW ⟶ TW, iW ≫ hW = aW ∧ hW ≫ qW = nW := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
