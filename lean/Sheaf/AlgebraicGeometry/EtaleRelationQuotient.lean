/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.FpqcDescentEtale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenGluing
import Sheaf.AlgebraicGeometry.EtaleAffineQuotientRepresentable
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient

/-!
# Quotients of étale equivalence relations

Source: Stacks Project, Spaces, Tags 02WW and 02WV, with the quotient universal
property and presentation kernel-pair identity (blueprint: lem-trf-etale-relation-quotient).

The presheaf coequalizer of the two Yoneda maps is the pointwise quotient presheaf.
Its sheafification is specified by its universal property at this presheaf, without
assuming existence of sheafification for every small-valued presheaf on the big site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical quotient map is the presheaf coequalizer projection followed by the
sheafification unit `η`. Source: Stacks, Spaces, quotient preceding Tag 02WW
(blueprint: lem-trf-etale-relation-quotient). -/
noncomputable def relationQuotientMap {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj) : yoneda.obj V ⟶ F.obj :=
  coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η

/-- An étale equivalence relation has an algebraic-space quotient, with an étale
surjective quotient map, the given relation as kernel pair, étale-local lifts of every
section, and the universal property for maps to any fppf sheaf. The hypothesis `hη`
is exactly the universal property of the sheafification unit of the quotient presheaf;
`∃!` in the last clause is the bijection onto the maps equalizing `s` and `t`.
Source: Stacks, Spaces, Tags 02WW and 02WV
(blueprint: lem-trf-etale-relation-quotient).

Proof:
1. Restrict the relation along a surjective étale refinement of the atlas; the quotient
   is unchanged by lem-trf-etale-relation-restriction-quotient.
2. Use lem-weil-pbc-scheme-coproduct-family to replace `V` by the coproduct of an affine
   open covering. Restriction along each summand gives an étale relation, without
   claiming that an individual summand quotient is the whole quotient.
3. Each affine quotient has representable diagonal and representable atlas by
   lem-trf-etale-affine-quotient-representable. The lemma
   lem-trf-etale-relation-kernel-pair identifies its kernel pair with the relation.
   After an fppf cover a section has representatives, and the atlas pullback is a
   base change of `t`. Reflexivity makes `t` surjective. Apply
   lem-galois-fpqc-descend-etale to descend étaleness and descend surjectivity on the base.
4. The lemma lem-trf-etale-relation-finding-opens makes the affine quotient maps open
   immersions; their images cover since quotient sections locally have representatives.
5. Apply lem-trf-algebraic-space-coproduct and lem-trf-algebraic-space-open-gluing to
   obtain the algebraic-space property for the entire quotient.
6. Its representable diagonal makes every atlas base change a scheme. On an fppf
   covering, the kernel-pair identity identifies this scheme with a base change of `t`.
   Again descend étaleness and surjectivity. The surjective étale atlas supplies the
   asserted local lifts. The kernel-pair lemma gives the stated pullback square.
   Finally, the presheaf coequalizer property and `hη` give the unique factorization
   of every map equalizing `s` and `t`, hence the asserted bijection. -/
theorem etale_relation_quotient {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    IsAlgebraicSpace F ∧
    IsEtale (relationQuotientMap s t F η) ∧
    IsSurjective (relationQuotientMap s t F η) ∧
    IsPullback (yoneda.map s) (yoneda.map t)
      (relationQuotientMap s t F η) (relationQuotientMap s t F η) ∧
    (∀ (T : Over S) (x : F.obj.obj (op T)),
      ∃ C : Sieve T, C ∈ (Scheme.etaleTopology.over S) T ∧
        ∀ (U : Over S) (f : U ⟶ T), C f →
          ∃ a : U ⟶ V,
            (relationQuotientMap s t F η).app (op U) a = F.obj.map f.op x) ∧
    (∀ (G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (f : yoneda.obj V ⟶ G.obj),
      yoneda.map s ≫ f = yoneda.map t ≫ f →
        ∃! g : F.obj ⟶ G.obj, relationQuotientMap s t F η ≫ g = f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
