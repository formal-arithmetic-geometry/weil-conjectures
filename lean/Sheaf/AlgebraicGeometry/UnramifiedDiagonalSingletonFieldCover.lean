/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SingletonStackFlatLfpFieldCover
import Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient

/-! # An etale field cover of a singleton stack with unramified diagonal

Source: Stacks Project, stacks-morphisms.tex, Tag 06N0 (lemma-DM-residual-gerbe),
with the relative-base formulation of Tag 050N (1)
(blueprint: lem-sfb-unramified-diagonal-singleton-field-cover).

The hypotheses use a reduced locally Noetherian smooth atlas and the unramified
relative diagonal over the original base. The singleton condition retains a
field-valued object and identifies any other such object over a common extension.
The conclusion tests the actual algebraic-space base-change projections on charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A reduced locally Noetherian singleton algebraic stack with unramified relative
 diagonal admits a representable surjective etale map from a field spectrum.
Source: Stacks Project, Tag 06N0 and Tag 050N (1)
(blueprint: lem-sfb-unramified-diagonal-singleton-field-cover).

Proof:
1. Apply lem-sfb-singleton-stack-flat-lfp-field-cover to obtain a representable
   surjective flat locally finitely presented a : U = Spec K -> F. The smooth
   atlas gives fppf descent by lem-sfb-etale-smooth-atlas-fppf-descent. Form
   R = U x_F U. The projections are flat and locally finitely presented, and
   [U/R] is equivalent to F, by lem-sfb-fppf-groupoid-stack-presentations.
   They are locally of finite type by lem-sfb-stack-chartwise-smooth-etale-calculus.
2. The map R -> U x_S U is a base change of the given relative diagonal.
   Apply lem-sfb-field-groupoid-identity-finite-relation: R is a separated
   scheme, its relation map is separated and locally quasi-finite, and the
   identity component P = Spec B is open and closed. Its projections are finite
   locally free, and P -> U x_S U is a monomorphism of groupoids.
3. Apply lem-sfb-divide-finite-flat-subgroupoid. Its quotient q : U -> Ubar is
   finite locally free and surjective, and (U,R) is the restriction of a scheme
   groupoid (Ubar,Rbar). By lem-a1-finite-flat-affine-relation-quotient, Ubar is
   Spec k, where k is the equalizer of the two maps K -> B. This equalizer is a
   subfield: the images of a nonzero invariant are equal units, hence their
   inverses agree. Use P-invariants, rather than invariants of the whole R.
4. Restriction along the fppf cover q gives [Ubar/Rbar] equivalent to [U/R],
   compatibly with U, by lem-sfb-fppf-groupoid-stack-presentations. The map
   R -> Rbar is the base change of q x q, so is fppf by chartwise calculus.
   Descend flatness and local finite presentation of each projection of Rbar
   using lem-sfb-representable-fppf-etale-open-descent. For the source projection,
   use the target cover U -> Ubar and the source cover
   R -> Rbar x_(Ubar) U; their composite to U is s. Treat t in the same way.
5. The unit clause of lem-sfb-divide-finite-flat-subgroupoid identifies the
   inverse image of the unit of Rbar under R -> Rbar with P, compatibly with
   its inclusion in R. This inclusion is open. Target-local descent of open
   immersions makes the unit of Rbar open. Now lem-sfb-groupoid-open-unit-etale
   makes both flat locally finitely presented projections of Rbar etale.
6. By lem-sfb-fppf-groupoid-stack-presentations, b : Ubar -> [Ubar/Rbar] = F
   is representable, surjective, flat and locally finitely presented, with
   self-relation Rbar. Its base change along b is an etale projection of Rbar.
   Descend etaleness by lem-sfb-representable-fppf-etale-open-descent. Since
   Ubar = Spec k, this is the desired cover. No perfectness of k or Noetherian
   hypothesis on S was used. -/
theorem exists_unramified_diagonal_singleton_field_cover
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hstack : IsModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (U : Over S) (atlas : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (hatlas : IsSmoothModuliAtlas F U atlas)
    (hreduced : ∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x))
    (hnoetherian : IsLocallyNoetherian U.left)
    (hsingleton : ∃ (K : Type u) (_ : Field K) (s : Spec (.of K) ⟶ S)
      (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) F),
      ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ S)
        (y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk t))) F),
        ∃ (E : Type u) (_ : Field E) (e : Spec (.of E) ⟶ S)
          (i : Over.mk e ⟶ Over.mk s) (j : Over.mk e ⟶ Over.mk t),
          Nonempty (ModuliTwoIso
            ((discreteModuliMap (yoneda.map i)).comp x)
            ((discreteModuliMap (yoneda.map j)).comp y)))
    (hunramified : HasUnramifiedModuliDiagonal F) :
    ∃ (K : Type u) (_ : Field K) (s : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) F),
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧
            SpaceMapIsEtale Z T p ∧ SpaceMapIsSurjective Z T p := by
  sorry

end CategoryTheory
