/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.GroupTheory.QuotientGroup.Basic

import Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Normalizer and centralizer of a torus

Source: Milne, Algebraic Groups (2017), Corollary 12.40, printed p.244,
Corollaries 13.10 and 13.11, printed p.257
(blueprint: lem-sfb-torus-normalizer-components).

The representing closed subgroup inclusions are characterized over every algebra,
including nonreduced algebras. The identity components are identified over the ambient
scheme, retaining their open subscheme structures. The final quotient uses the image
of the centralizer in the rational points of the normalizer.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A torus has smooth finite-type closed normalizer and centralizer with the same
identity component; their rational-point quotient is a finite group.
Source: Milne, Algebraic Groups (2017), Corollary 12.40, printed p.244,
Corollaries 13.10 and 13.11, printed p.257
(blueprint: lem-sfb-torus-normalizer-components).

Proof plan, following the node's six steps:
1. Apply lem-sfb-constant-source-closed-factorization-locus to conjugation
   S times G to G and the closed immersion S into G. Affineness gives
   separatedness by lem-weil-pbc-affine-source-morphism-separated. Test on the
   universal point of S to identify the locus L with preservation by inclusion
   after all algebra extensions (def-weil-closed-immersion). Intersect L with its
   inverse image under inversion using def-pc-fibre-product and
   lem-weil-pbc-closed-immersion-base-change. This represents equality of the
   conjugate subgroup functor, hence the stated normalizer condition.
2. Identity, multiplication and inversion preserve this condition, so the locus
   is a closed subgroup (def-sc-group-scheme-subgroup). Quotients of finitely
   generated coordinate algebras remain finitely generated. Apply
   lem-sfb-torus-centralizer-smooth-connected to obtain the smooth closed
   centralizer, also affine of finite type. It is contained in the normalizer.
3. Apply lem-sfb-group-neutral-component-translates to N and C. Restrict
   conjugation to N's identity component times S. Split S as a product of G_m
   (def-sc-gm-ga), whose Hopf algebra is F[Z^r]. Apply
   lem-sfb-diagonalizable-hom-family-rigidity with parameter N's identity
   component and base point the identity. The resulting action is trivial,
   including on nilpotents, so N's identity component lies in C.
4. Conversely C's identity component maps into N's identity component by
   connectedness. Apply lem-weil-pbc-morphism-factors-through-open-subscheme
   in both directions. The two maps are inverse since their composites with
   the monic inclusions into G agree. This identifies the open subschemes.
5. C's identity component is smooth by
   lem-weil-pbc-smooth-restrict-open-subschemes. Hence so is N's identity
   component. By lem-sfb-group-neutral-component-translates each component
   of N is a rational translate of it. Translation preserves smoothness, and
   lem-weil-pbc-smooth-local-on-source gives smoothness of N.
6. Conjugation by a normalizing element preserves the centralizer: rewrite s
   as n(n inverse s n)n inverse in the commuting relation. Thus C is normal
   in N. The finitely many components supplied by
   lem-sfb-group-neutral-component-translates have rational representatives.
   Every element of N(F) differs from its component representative by an
   element of N's identity component, hence of C(F). These representatives
   therefore surject onto the quotient, proving it finite. -/
theorem torus_normalizer_centralizer_components
    (F : Type u) [Field F] [IsAlgClosed F]
    (G S : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : S ⟶ G) [IsClosedSubgroupScheme i.hom.hom]
    (hS : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus F r)) :
    ∃ (N C : Grp (Over (Spec (.of F)))) (iN : N ⟶ G) (iC : C ⟶ G),
      IsClosedSubgroupScheme iN.hom.hom ∧ IsClosedSubgroupScheme iC.hom.hom ∧
      IsAffine N.X.left ∧ IsAffine C.X.left ∧
      ∃ (_ : LocallyOfFiniteType N.X.hom) (_ : QuasiCompact N.X.hom)
        (_ : LocallyOfFiniteType C.X.hom) (_ : QuasiCompact C.X.hom),
        Smooth N.X.hom ∧ Smooth C.X.hom ∧
        (∀ (A : Type u) [CommRing A] [Algebra F A],
          Set.range (fun n : StandardGroupSchemes.affine F A ⟶ N.X ↦ n ≫ iN.hom.hom) =
            {g : StandardGroupSchemes.affine F A ⟶ G.X |
              ∀ (B : Type u) [CommRing B] [Algebra F B] (f : A →ₐ[F] B),
                (fun s : StandardGroupSchemes.affine F B ⟶ G.X ↦
                  (StandardGroupSchemes.map F f ≫ g) * s *
                    (StandardGroupSchemes.map F f ≫ g)⁻¹) ''
                      Set.range (fun s : StandardGroupSchemes.affine F B ⟶ S.X ↦
                        s ≫ i.hom.hom) =
                      Set.range (fun s : StandardGroupSchemes.affine F B ⟶ S.X ↦
                        s ≫ i.hom.hom)}) ∧
        (∀ (A : Type u) [CommRing A] [Algebra F A],
          Set.range (fun c : StandardGroupSchemes.affine F A ⟶ C.X ↦ c ≫ iC.hom.hom) =
            ReductiveTorusCentralizer.centralizerPoints i A) ∧
        (∃ e : GrpObj.identityComponent N.X ≅ GrpObj.identityComponent C.X,
          e.hom ≫ GrpObj.identityComponentι C.X ≫ iC.hom.hom =
            GrpObj.identityComponentι N.X ≫ iN.hom.hom) ∧
        ∃ j : C ⟶ N, j ≫ iN = iC ∧ IsNormalSubgroupScheme j.hom.hom ∧
          Finite ((𝟙_ (Over (Spec (.of F))) ⟶ N.X) ⧸
            (IsMonHom.monoidHom j.hom.hom (𝟙_ (Over (Spec (.of F))))).range) := by
  sorry

end AlgebraicGeometry
