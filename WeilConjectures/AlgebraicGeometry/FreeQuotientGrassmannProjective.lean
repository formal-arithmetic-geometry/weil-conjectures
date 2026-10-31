/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints

/-! # Free quotient Grassmannians and their Plücker embedding

Source: Stacks Project, Constructions, Tag 089T, `lemma-gkn-representable`, with
the quotient convention immediately preceding it; the explicit determinant-equation
completion in the node's proof supplies the projective embedding and endpoint cases
(blueprint: lem-sfb-free-quotient-grassmann-projective).

The classification is expressed by unique morphisms preserving the quotient up to
isomorphism. This is the universal-element formulation of representability; it avoids
choosing representatives for isomorphism classes. The projective coordinates are indexed
by the r-element subsets of Fin N, a set of cardinality N.choose r.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The canonical pullback of a quotient of a trivial bundle, specified on its standard
generators by the section-normalized tensor-pullback unit. This constructs the actual
map, without choosing a comparison isomorphism for the free source.
Source: Stacks, the quotient convention preceding Tag 089T
(blueprint: lem-sfb-free-quotient-grassmann-projective). -/
noncomputable def freeQuotientPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {N : ℕ}
    {Q : Y.Modules} (q : SheafOfModules.free (R := Y.ringCatSheaf)
      (ULift.{u} (Fin N)) ⟶ Q) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin N)) ⟶
      (Scheme.Modules.tensorPullback f).obj Q :=
  Sigma.desc (fun i ↦ Scheme.Modules.homOfGlobalSection
    ((Scheme.Modules.tensorPullback f).obj Q)
    (((Scheme.Modules.tensorPullbackSectionAdjunction f).unit.app Q).app ⊤
      ((SheafOfModules.freeHomEquiv Q q i).val (op ⊤))))

/-- Free quotient Grassmannians, including the universal quotient, arbitrary base
change, the determinant-coordinate Plücker embedding, and the endpoint cases.

Source: Stacks, Tag 089T, `lemma-gkn-representable`, quotient convention preceding
it, and the explicit projectivity completion in the node's proof
(blueprint: lem-sfb-free-quotient-grassmann-projective).

Proof, following the twelve steps of the node:
1. The opens where selected r columns form a frame cover every quotient. Residue-field
   linear algebra and the adjugate identity give their normalized quotient matrices;
   the other r(N-r) entries determine the quotient uniquely.
2. Introduce homogeneous variables p_J and equations
   p_I^(r-1) p_K = det(p_(I with its a-th entry replaced by k_b)).
   The Cramer formula, determinant multiplication and determinant of an adjugate
   (lem-sfb-matrix-cramer-determinant-identities) show they vanish on maximal minors
   over every commutative ring, without cancellation.
3. Proj of this homogeneous quotient is a closed subscheme of projective space by
   prop-nagata-relative-proj-functoriality; its standard opens cover by
   prop-nagata-proj-standard-open.
4. On D_+(p_I), the single-column replacement ratios are independent coordinates.
   The equations express every p_J/p_I as the corresponding normalized minor.
   Evaluation on the generic normalized matrix gives the inverse polynomial-ring map.
5. On overlaps, the two matrices differ by the inverse pivot matrix. Its adjugate
   formula gives the transition isomorphisms, and the identity columns prove the cocycle.
6. Glue the free rank-r modules and quotient maps using both clauses of
   lem-weil-pbc-glue-sheaves-of-modules. The pivot columns split the local quotient.
7. The top exterior sheaf is locally a line by
   lem-sc-exterior-sheaf-local-free-comparison and the free exterior basis. Its
   coordinate sections are the ordered wedges of the quotient generators. They generate
   everywhere, giving a projective-space map by
   lem-weil-pbc-projective-space-functor-of-points.
8. The determinant equations make this map factor scheme-theoretically through the
   constructed closed subscheme. The affine ring maps glue by scheme-morphism-gluing.
9. Pulling back the universal matrices recovers the quotient; conversely their
   single-column minors recover every affine coordinate of the classifying map.
   Gluing gives uniqueness, and polynomial evaluation commutes with pullback.
10. Base change the integer construction to S. The fibre-product universal property
   gives classification over S and after every S' → S. Representable-unique identifies
   the result with any representative over S', preserving the universal quotient.
11. Base change the integer closed immersion. Closed-immersion-base-change preserves
   it, projective-space-base-change identifies its target, and the wedge coordinates
   identify it as the Plücker map. This proves H-projectivity.
12. In rank zero the quotient is zero. In rank N the square surjection has invertible
   determinant locally and its adjugate gives an inverse. Both functors are singleton
   functors, represented by S; P^0_S = S gives H-projectivity. This includes N = 0
   and empty bases and test schemes. -/
theorem exists_freeQuotientGrassmann_projective (S : Scheme.{u}) (N r : ℕ) (hr : r ≤ N) :
    ∃ (G : Scheme.{u}) (π : G ⟶ S) (Q : G.Modules)
      (q : SheafOfModules.free (R := G.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ Q),
      Epi q ∧ Q.IsFiniteLocallyFreeOfRank r ∧
      (∀ (T : Scheme.{u}) (a : T ⟶ G),
        Epi (freeQuotientPullback a q) ∧
          ((Scheme.Modules.tensorPullback a).obj Q).IsFiniteLocallyFreeOfRank r) ∧
      (∀ (T : Scheme.{u}) (t : T ⟶ S) (P : T.Modules)
        (p : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ P),
        Epi p → P.IsFiniteLocallyFreeOfRank r →
        ∃! a : T ⟶ G, a ≫ π = t ∧
          ∃ e : (Scheme.Modules.tensorPullback a).obj Q ≅ P,
            freeQuotientPullback a q ≫ e.hom = p) ∧
      (∀ (S' : Scheme.{u}) (f : S' ⟶ S) (T : Scheme.{u}) (t : T ⟶ S')
        (P : T.Modules)
        (p : SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin N)) ⟶ P),
        Epi p → P.IsFiniteLocallyFreeOfRank r →
        ∃! a : T ⟶ pullback π f, a ≫ pullback.snd π f = t ∧
          ∃ e : (Scheme.Modules.tensorPullback a).obj
              ((Scheme.Modules.tensorPullback (pullback.fst π f)).obj Q) ≅ P,
            freeQuotientPullback a (freeQuotientPullback (pullback.fst π f) q) ≫ e.hom = p) ∧
      ((r = 0 ∨ r = N) → IsIso π) ∧
      (0 < r → r < N →
        ∃ j : G ⟶ ℙ(ULift.{u} (Set.powersetCard (Fin N) r); S),
          IsClosedImmersion j ∧
          j ≫ ℙ(ULift.{u} (Set.powersetCard (Fin N) r); S) ↘ S = π ∧
          ∃ e : (Scheme.Modules.tensorPullback j).obj
              (ProjectiveSpace.twist (ULift.{u} (Set.powersetCard (Fin N) r)) S 1) ≅
                Scheme.Modules.exteriorSheaf Q r,
            ∀ I : ULift.{u} (Set.powersetCard (Fin N) r),
              e.hom.app ⊤
                  (((Scheme.Modules.tensorPullbackSectionAdjunction j).unit.app
                    (ProjectiveSpace.twist (ULift.{u} (Set.powersetCard (Fin N) r)) S 1)).app ⊤
                    (ProjectiveSpace.twistOneSection
                      (ULift.{u} (Set.powersetCard (Fin N) r)) S I)) =
                Scheme.Modules.exteriorSheafSection Q r ⊤
                  (fun k ↦ (SheafOfModules.freeHomEquiv Q q
                    (ULift.up (I.down.val.orderEmbOfFin I.down.property k))).val (op ⊤))) ∧
      IsHProjective π := by
  sorry

end AlgebraicGeometry
