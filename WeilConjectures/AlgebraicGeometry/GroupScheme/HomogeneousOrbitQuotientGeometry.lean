/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
import WeilConjectures.AlgebraicGeometry.FppfAffineRefinement
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFppfFiniteAffineRefinement
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Homogeneous quotients and reduced orbits

Source: Milne, Algebraic Groups (2017), Definition 5.20, Propositions 5.24--5.25,
Corollary 5.27, Propositions 7.11--7.12 and 7.17, and Theorem 7.18, pp.104--105,
141--143 (blueprint: lem-sfb-homogeneous-orbit-quotient-geometry).

The pointwise coequalizer of right multiplication and projection is the presheaf
of right cosets. Its displayed arrow to the represented sheaf has the sheafification
universal property. The orbit identification is the unique isomorphism compatible
with the orbit map, for every such quotient presentation. Stabilizers retain their
full scheme structure, including nilpotents.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- The fppf coset quotient by an arbitrary closed subgroup is a separated finite-type
scheme. The two projection equations specify the torsor isomorphism `(g,h) ↦ (g,gh)`.
The arrow `ηq`, its equation on generators, and its bijection on maps to every sheaf
are precisely sheafification of the coset presheaf. The final two clauses give the
canonical bijection on rational points, including when the subgroup is nonreduced.

Source: Milne, Definition 5.20, Propositions 5.24--5.25, Corollary 5.27 and
Theorem 7.18, pp.104--105, 143
(blueprint: lem-sfb-homogeneous-orbit-quotient-geometry).

Proof, steps 1--4 and 7 of the node:
1. The group-scheme separatedness lemma makes G separated. Apply
   lem-sfb-algebraic-group-homogeneous-quotient to obtain Q and a flat surjective
   finitely presented q with the all-test-schemes coset criterion. This also proves
   right invariance; no normality, smoothness or connectedness of H is used.
2. On G ×[Q] G let a,b be the universal points. The coset criterion gives the
   unique h in H with a⁻¹b = h. The map (a,b) ↦ (a,a⁻¹b) inverts (g,h) ↦ (g,gh),
   by the group identities and the fibre-product universal property.
3. Pull back the singleton fppf cover q along an affine test point of Q. The
   fppf-covering base-change and affine-refinement lemmas give local affine lifts.
   Affine source and target turn local finite presentation into finite presentation
   by lem-weil-pbc-qcqs-morphism-permanence. The finite-affine-refinement lemma
   also provides a singleton affine refinement when desired.
4. Representable fpqc descent and fppf-to-fpqc comparison make h_Q a sheaf. The
   coset criterion embeds the pointwise coset presheaf in h_Q, and step 3 makes it
   locally surjective. For a map to a sheaf Z, glue the images of local lifts.
   Overlap compatibility follows from the coset criterion; common refinement gives
   independence, naturality and uniqueness. This is the stated universal property
   of def-weil-pbc-sheafification.
7. The fibre of q over a rational point is nonempty and finite type, by covering
   base change and finite-type base change. The locally-finite-type Jacobson lemma
   supplies a closed point, and lem-weil-pbc-closed-point-residue-field-base identifies
   its residue field with F. It lifts the given rational point. The coset criterion
   identifies exactly the pairs of rational lifts differing by an element of H(F).
-/
theorem exists_homogeneous_fppf_quotient
    {F : Type u} [Field F] [IsAlgClosed F]
    (G H : Over (Spec (.of F))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    [IsAffine H.left] [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (i : H ⟶ G) [IsClosedSubgroupScheme i] :
    ∃ (Q : Over (Spec (.of F))) (q : G ⟶ Q),
      IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom ∧
      Flat q.left ∧ Surjective q.left ∧
      (fst G H ≫ q = lift (fst G H) (snd G H ≫ i) ≫ μ[G] ≫ q) ∧
      (∃ e : G ⊗ H ≅ pullback q q,
        e.hom ≫ pullback.fst q q = fst G H ∧
        e.hom ≫ pullback.snd q q = lift (fst G H) (snd G H ≫ i) ≫ μ[G]) ∧
      Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q) ∧
      (∃ ηq : coequalizer (yoneda.map (fst G H))
          (yoneda.map (lift (fst G H) (snd G H ≫ i) ≫ μ[G])) ⟶ yoneda.obj Q,
        coequalizer.π _ _ ≫ ηq = yoneda.map q ∧
        ∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
          Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) ∧
      Function.Surjective (fun g : 𝟙_ (Over (Spec (.of F))) ⟶ G ↦ g ≫ q) ∧
      (∀ g₁ g₂ : 𝟙_ (Over (Spec (.of F))) ⟶ G,
        g₁ ≫ q = g₂ ≫ q ↔
          ∃ h : 𝟙_ (Over (Spec (.of F))) ⟶ H, g₂ = g₁ * (h ≫ i)) := by
  sorry

/-- The scheme-theoretic stabilizer represents the pointwise fixing condition on every
base scheme. The reduced orbit is its canonical homogeneous quotient: for every
presentation of the fppf coset sheaf, there is a unique isomorphism to the reduced
orbit that carries the quotient map to the orbit map.

Source: Milne, Propositions 7.11--7.12 and 7.17, pp.141--143; Remark 7.14 explains
why the stabilizer must retain its possibly nonreduced scheme structure
(blueprint: lem-sfb-homogeneous-orbit-quotient-geometry).

Proof, steps 5--6 of the node:
5. Form the stabilizer as the pullback of the diagonal X → X × X along
   g ↦ (gx,x). Its test points are exactly the fixing elements, and the action
   identities give its group structure. Separatedness of X makes its diagonal
   closed, so closed-immersion base change makes the stabilizer inclusion closed.
   Apply lem-sfb-smooth-group-orbit-geometry: the reduced orbit O is locally closed
   and smooth, and G → O is faithfully flat, without reducedness assumptions on X
   or on the stabilizer.
6. The immersion-over-separated-base lemma makes O separated. Finite-type
   cancellation into a separated target makes G → O quasi-compact, hence fpqc.
   The quotient map is fpqc as well. On each kernel pair, the two maps to the
   other target agree: equal quotient points differ by a stabilizer element, and
   equal orbit points give a⁻¹b in the stabilizer. Representable fpqc descent
   supplies maps Q → O and O → Q. Their composites pull back to identities on G;
   uniqueness in descent proves they are inverse. The same uniqueness gives the
   displayed unique isomorphism, whose value on a coset is gx.
-/
theorem exists_orbit_stabilizer_quotient_iso
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Over (Spec (.of F))) [GrpObj G]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (X : Over (Spec (.of F))) [ModObj G X]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (x : 𝟙_ (Over (Spec (.of F))) ⟶ X) :
    ∃ (K : Grp (Over (Spec (.of F)))) (i : K.X ⟶ G),
      IsClosedSubgroupScheme i ∧ IsAffine K.X.left ∧
      LocallyOfFiniteType K.X.hom ∧ QuasiCompact K.X.hom ∧
      (∀ (T : Over (Spec (.of F))) (g : T ⟶ G),
        (∃ h : T ⟶ K.X, h ≫ i = g) ↔ g • (toUnit T ≫ x) = toUnit T ≫ x) ∧
      ∃ (O : Over (Spec (.of F))) (j : O ⟶ X) (a : G ⟶ O),
        IsReduced O.left ∧ IsImmersion j.left ∧
        Set.range j.left.base =
          Set.range (lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X]).left.base ∧
        a ≫ j = lift (𝟙 G) (toUnit G ≫ x) ≫ γ[G, X] ∧
        ∀ (Q : Over (Spec (.of F))) (q : G ⟶ Q),
          Presheaf.IsSheaf (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.obj Q) →
          ∀ ηq : coequalizer (yoneda.map (fst G K.X))
              (yoneda.map (lift (fst G K.X) (snd G K.X ≫ i) ≫ μ[G])) ⟶ yoneda.obj Q,
            coequalizer.π _ _ ≫ ηq = yoneda.map q →
            (∀ Z : Sheaf (Scheme.fppfTopology.over (Spec (.of F))) (Type u),
              Function.Bijective (fun f : yoneda.obj Q ⟶ Z.obj ↦ ηq ≫ f)) →
            ∃! e : Q ≅ O, q ≫ e.hom = a := by
  sorry

end AlgebraicGeometry
