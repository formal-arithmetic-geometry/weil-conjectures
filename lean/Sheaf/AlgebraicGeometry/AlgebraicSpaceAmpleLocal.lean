/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q75
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent
import Sheaf.AlgebraicGeometry.SchemeAmpleCanonicalProjCriterion
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Sheaf.AlgebraicGeometry.SpaceOpenImmersionEtaleLocal
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.TraceFormula.SpaceLineModuleProjMap
import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
import Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange

/-!
# Relative ampleness is étale local on an algebraic-space base

Source: Stacks Project, Descent on Spaces, Tag 0D3C; Divisors on Spaces, Tag 0D36;
Morphisms, Tag 01VH (blueprint: lem-trf-algebraic-space-ample-local).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A line module which is relatively ample on a jointly surjective étale scheme
cover of the base makes the morphism representable. On every étale scheme test,
its restriction is ample over every affine open of the test scheme. In particular,
if the base is a scheme, its identity test gives a scheme representing the source
and the stated ampleness over all affine opens of the base.

The covering hypothesis uses the sieve of local factorizations through the members
of the family. Membership in the big fppf topology says that the family is jointly
surjective: for representable étale arrows this is precisely fppf-local lifting of
scheme-valued sections. It imposes no finiteness condition on the family.
`schemeRestriction` is restriction to Zariski opens, the ordinary invertible module
corresponding to the line module on the small étale site.

Source: Stacks, Tags 0D3C, 0D36 and 01VH
(blueprint: lem-trf-algebraic-space-ample-local).

Proof:
1. For any scheme test `T → Y`, form `X = F ×_Y T` and the base-changed covers.
   The scheme relative-ample base-change lemma makes the local pullbacks ample.
   Invertible descent glues them to a line module on `X`; on étale tests full
   faithfulness identifies it with the restriction of `M`. These are
   lem-trf-scheme-relative-ample-base-change,
   lem-trf-algebraic-space-invertible-descent and
   lem-trf-space-fibre-products-etale-covers; tensor-pullback functoriality and
   lem-weil-pbc-invertible-pullback-tensor give the cocycle and invertibility.
2. The forward scheme canonical-Proj criterion gives quasi-compactness and
   separatedness locally. Descend both properties by
   lem-trf-space-qc-separated-etale-local.
3. By lem-trf-space-section-algebra-etale-base-change, the graded direct image
   of powers of the line module is quasi-coherent and its formation and evaluation
   maps commute with the étale cover. Form its relative Proj by
   lemma-nagata-relative-proj-exists. The space line-module Proj construction
   lem-trf-space-line-module-proj-map gives a canonical map on an open of `X`.
4. The local canonical-Proj criterion makes this open all of `X` and makes each
   local map an open immersion. The covering base-change lemma
   lem-weil-pbc-etale-covering-base-change verifies the cover of relative Proj.
   By lem-trf-space-open-immersion-etale-local the global map is an open
   immersion into a scheme, so `X` is a scheme.
5. The section-algebra and canonical-map comparisons identify this map with
   the scheme canonical map. The reverse implication of
   lem-trf-scheme-ample-canonical-proj-criterion gives ampleness over each affine
   open of `T`. All scheme tests give representability; étale tests identify the
   module with `M`'s restriction. Take the identity test when `Y` is a scheme. -/
theorem representable_and_ample_of_etale_cover
    {S : Scheme.{u}} {F Y : AlgebraicSpace S} (f : F ⟶ Y)
    (M : F.Modules) (hM : F.IsLineModule M)
    (I : Type v) (Yᵢ : I → Y.EtaleSite) (Xᵢ : I → F.EtaleSite)
    (pᵢ : ∀ i : I, (Xᵢ i).obj.left ⟶ (Yᵢ i).obj.left)
    (hcover : ∀ (T : Over S) (a : yoneda.obj T ⟶ Y.obj.obj),
      Sieve.generate (fun (U : Over S) (k : U ⟶ T) ↦
        ∃ (i : I) (b : U ⟶ (Yᵢ i).obj.left),
          yoneda.map k ≫ a = yoneda.map b ≫ (Yᵢ i).obj.hom) ∈
            (Scheme.fppfTopology.over S) T)
    (hpb : ∀ i : I, IsPullback (Xᵢ i).obj.hom (yoneda.map (pᵢ i))
      f.hom.hom (Yᵢ i).obj.hom)
    (hample : ∀ (i : I) (W : (Y.etaleForget.obj (Yᵢ i)).Opens), IsAffineOpen W →
      ∃ hL : ((Scheme.Modules.restrictFunctor (((pᵢ i).left ⁻¹ᵁ W).ι)).obj
          ((F.schemeRestriction (Xᵢ i)).obj M)).IsInvertible,
        @Scheme.Modules.IsAmple ((pᵢ i).left ⁻¹ᵁ W).toScheme
          ((Scheme.Modules.restrictFunctor (((pᵢ i).left ⁻¹ᵁ W).ι)).obj
            ((F.schemeRestriction (Xᵢ i)).obj M)) hL) :
    IsRepresentable f.hom.hom ∧
      ∀ T : Y.EtaleSite, ∃ (X : F.EtaleSite) (p : X.obj.left ⟶ T.obj.left),
        IsPullback X.obj.hom (yoneda.map p) f.hom.hom T.obj.hom ∧
          ∀ W : (Y.etaleForget.obj T).Opens, IsAffineOpen W →
            ∃ hL : ((Scheme.Modules.restrictFunctor ((p.left ⁻¹ᵁ W).ι)).obj
                ((F.schemeRestriction X).obj M)).IsInvertible,
              @Scheme.Modules.IsAmple (p.left ⁻¹ᵁ W).toScheme
                ((Scheme.Modules.restrictFunctor ((p.left ⁻¹ᵁ W).ι)).obj
                  ((F.schemeRestriction X).obj M)) hL := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
