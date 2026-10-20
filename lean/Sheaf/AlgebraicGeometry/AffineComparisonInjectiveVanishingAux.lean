/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

import Sheaf.AlgebraicGeometry.AffineComparisonCechCocycleDescent
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.FibreProductLimit
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite affine Čech exactness for comparison pullbacks of injectives

Source: Stacks Project, Tag 099U, verification of condition (3).
(blueprint: lem-cbc-abelian-affine-comparison-vanishing-aux).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Finite Čech complexes of the comparison pullback of an injective étale sheaf
are exact in positive degrees on the affine ind-étale basis. The nerve hypothesis
includes its one-factor terms, so every cover member is a basis object up to isomorphism.
Source: Stacks Project, Tag 099U, verification of condition (3).
(blueprint: lem-cbc-abelian-affine-comparison-vanishing-aux).

Proof:
1. Put F = nu⁻¹J. The comparison section formula identifies F(W) with sections
   of the étale inverse image of J on W. Naturality for zero, addition and negation
   makes this an additive identification compatible with restriction maps. At étale
   Y-objects it identifies these sections and restrictions with those of J.
2. If W is a directed affine inverse limit, degree-zero étale continuity identifies
   F(W) with the filtered colimit of the stage sections, naturally in W. Affine
   schemes are qcqs. A finite product of abelian groups is a finite direct sum,
   hence commutes with these colimits. Exact filtered colimits preserve kernels
   and images, and thus cohomology. Naturality for each omitted-factor projection
   identifies the alternating differentials, not only the degreewise groups.
3. Every arrow between affine ind-étale Y-objects is ind-étale. Present each member
   U_i over V as a directed limit of affine étale V-schemes. The finite product
   of the indexing directed sets is nonempty and directed. Every stage family
   covers V, since the jointly surjective limit family factors through it.
   Fibre products commute with limits, including repeated indices in a tuple.
   Consequently step 2 identifies the original Čech complex with the filtered
   colimit of the Čech complexes of these finite affine étale covers of V.
4. Present V as a directed limit of affine étale Y-schemes V_b. Descend any finite
   affine étale cover of V, its arrows and its covering relation to a common stage.
   If the descended target is only isomorphic to V after base change, descend the
   target isomorphism and its inverse too, and make both composite identities at
   a later common stage. This fixes the target as V_b. The tail is cofinal.
   Base change gives covers at every later stage. Étale composition and base
   change put every stage intersection and face arrow on the original Y_et site;
   affine fibre-product limits recover the intersections of the given cover.
5. Apply step 2 again. The entire stage Čech complex is now that of J on Y_et
   by step 1. Injectivity on this fixed site makes it exact in positive degrees.
   Exact filtered colimits give the asserted exactness, first for the étale
   covers of V and then for the original ind-étale cover. No injectivity on V_et
   is asserted. For an empty indexing family each Čech group is the zero group;
   the same conclusion holds directly, including empty Y and empty V. -/
theorem exactAt_cechComplex_comparisonUpperStar_of_injective
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) (q : ℕ) :
    ((Presheaf.cechComplex U).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J).obj).ExactAt (q + 1) := by
  rw [Presheaf.exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨W, T, f, hcover', φ, c', hc', hφ⟩ :=
    exists_etale_cech_cocycle_lift Y J V hV U hU hcover q c hc
  let C := (cechComplexFunctor fun i ↦ Over.mk (f i)).obj
    ((Over.forget W).op ⋙ J.obj)
  have hzero : IsZero (C.homology (q + 1)) :=
    injective_sheaf_cech_acyclic Y J W _ T f hcover' (q + 1) (Nat.zero_lt_succ q)
  have hex : C.ExactAt (q + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology C (q + 1)).mpr hzero
  rw [HomologicalComplex.exactAt_iff' C q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff] at hex
  obtain ⟨b, hb⟩ := hex c' hc'
  refine ⟨φ.f q b, ?_⟩
  have h := ConcreteCategory.congr_hom (φ.comm q (q + 1)) b
  exact h.trans ((congrArg (φ.f (q + 1)) hb).trans hφ)

end AlgebraicGeometry.ProEtale
