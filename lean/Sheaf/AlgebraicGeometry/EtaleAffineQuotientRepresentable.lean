/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.AffineEtaleRelationSeparatedQuasiFinite
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import Sheaf.AlgebraicGeometry.FppfSheafRepresentabilityDescentData
import Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent

/-!
# Representability for an affine étale-relation quotient

Source: Stacks Project, Spaces, Tag 0265 (lemma-presentation-quasi-compact), first
and third representability steps (blueprint: lem-trf-etale-affine-quotient-representable).

The coequalizer of the two Yoneda maps is the pointwise quotient presheaf. Its
sheafification is specified by the universal property of its unit, as in
`etale_relation_quotient`; no sheafification functor for all small-valued presheaves
on the big site is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quotient map from an affine scheme by an étale equivalence relation is
representable, and the quotient sheaf has representable diagonal. The condition `hη`
is precisely the sheafification universal property for the quotient presheaf; its
composition with the coequalizer projection is the canonical map `h_U → F`.
Source: Stacks Project, Spaces, Tag 0265, first and third representability steps
(blueprint: lem-trf-etale-affine-quotient-representable).

Proof:
1. By lem-trf-affine-etale-relation-separated-lqf, affineness of U makes s, t and
   j = (s,t) separated and locally quasi-finite, without a separatedness assumption on S.
2. Given a map h_T → F, lem-weil-pbc-site-sheafification-sections-local supplies an
   fppf cover T_i → T and representatives a_i : T_i → U lifting that map.
3. By lem-trf-etale-relation-kernel-pair, the restriction of h_T ×_F h_U to T_i is
   represented by T_i ×_{a_i,U,s} R, with the other projection given by t. Its map
   to T_i is separated and locally quasi-finite by lem-weil-pbc-separated-lqf-base-change.
4. The fibre product is an fppf sheaf. The local models carry descent data by
   lem-trf-fppf-sheaf-representability-descent-data. They descend effectively by
   lem-trf-separated-lqf-fppf-effective-descent, so that same sheaf/descent-data
   correspondence represents h_T ×_F h_U by a scheme over T.
5. Given h_T → F × F, lift both components to maps u_i,v_i : T_i → U after a
   common fppf refinement. Such refinements exist by the covering axioms of
   def-weil-pbc-sites-and-cohomology and the local-sections lemma from step 2.
6. The kernel-pair identity identifies the pullback of the diagonal over T_i with
   T_i ×_{(u_i,v_i),U×_S U,j} R. Its projection is separated and locally quasi-finite
   by step 1 and lem-weil-pbc-separated-lqf-base-change.
7. Equality of the two sections of F is local, so this pullback is a sheaf. Apply
   lem-trf-fppf-sheaf-representability-descent-data and
   lem-trf-separated-lqf-fppf-effective-descent once more to represent it over T.
   Since T and its map were arbitrary, the diagonal is representable. -/
theorem etale_affine_quotient_representable {S : Scheme.{u}} {R U : Over S}
    [IsAffine U.left] (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    IsRepresentable (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
