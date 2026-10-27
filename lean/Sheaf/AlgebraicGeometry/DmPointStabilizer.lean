/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Field points of the Deligne--Mumford locus

Source: Stacks Project, stacks-morphisms.tex, Tag 0DSN(1), with the relative-base
convention of Tag 050N(1) (blueprint: lem-sfb-algebraic-stack-dm-point-stabilizer).

The automorphism space is identified on every test scheme, naturally under restriction.
The field is arbitrary; its algebraic closure or perfectness is never required.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A space over `T` represents automorphisms of the object specified by `x`.
For each scheme mapping to `T`, its sections are the vertical natural automorphisms
of the pulled-back object. The last equality imposes naturality under every test map,
component by component. By the fibred Yoneda lemma these are precisely automorphisms
in the fibre groupoid, including on nonreduced test schemes.
Source: Stacks Project, Tag 0DSN, the automorphism group algebraic space of a point;
Tag 04XR, the isomorphism sheaf
(blueprint: lem-sfb-algebraic-stack-dm-point-stabilizer). -/
def IsModuliAutomorphismSpace {S : Scheme.{u}}
    {F : BasedCategory.{v, w} (Over S)} (T : Over S)
    (x : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    (G : AlgebraicSpace S) (p : G.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∃ θ : ∀ (V : Over S) (b : yoneda.obj V ⟶ yoneda.obj T),
      {g : yoneda.obj V ⟶ G.obj.obj // g ≫ p = b} ≃
        ModuliTwoIso ((discreteModuliMap b).comp x) ((discreteModuliMap b).comp x),
    ∀ (V W : Over S) (f : W ⟶ V) (b : yoneda.obj V ⟶ yoneda.obj T)
      (g : {g : yoneda.obj V ⟶ G.obj.obj // g ≫ p = b})
      (g' : {g : yoneda.obj W ⟶ G.obj.obj // g ≫ p = yoneda.map f ≫ b}),
      g'.val = yoneda.map f ≫ g.val →
        ∀ z : (discreteModuli (yoneda.obj W)).obj,
          (θ W (yoneda.map f ≫ b) g').val.hom.app z =
            (θ V b g).val.hom.app ((discreteModuliMap (yoneda.map f)).toFunctor.obj z)

/-- A field point factors through the largest open with unramified relative diagonal
if and only if its automorphism group algebraic space is unramified over that field.
Source: Stacks Project, Tag 0DSN(1), and relative-base convention Tag 050N(1)
(blueprint: lem-sfb-algebraic-stack-dm-point-stabilizer).

Proof:
1. Choose the smooth surjective scheme atlas P. Its automorphism space G is locally
   of finite type by lem-sfb-stack-isom-space-locally-finite-type. Over the relation
   P x_X P, the two pullbacks of G are identified by conjugation with the tautological
   isomorphism; this commutes with pullback, composition and inversion.
2. Apply lem-sfb-group-space-unramified-base-locus to G over P. Its maximal open V
   commutes with arbitrary base change. Conjugation identifies its two inverse images
   in P x_X P, so V is invariant under the atlas groupoid.
3. By lem-sfb-invariant-open-substack-descent, V descends to an open W of X. Its
   restricted atlas has unramified automorphism space. The criterion
   lem-sfb-smooth-atlas-automorphism-diagonal-test gives unramified diagonal of W.
   Maximality therefore places W inside the given open U.
4. Conversely, pull U back to P. Fullness identifies the restricted automorphism
   space with the pullback of G. The same diagonal test and maximality of V put
   this open inside V. Descent then gives U contained in W, hence equality.
5. For x over Spec K, use the whole nonempty smooth surjective atlas fibre
   Q = Spec K x_X P. Conjugation identifies the two automorphism spaces on Q.
   Arbitrary base change of the maximal group locus identifies the inverse image
   of V with that of the maximal unramified base open V_x in Spec K.
6. Factoring x through U is equivalent to the latter inverse image being all of Q.
   A field spectrum has only the empty and full opens, and Q is nonempty, so this
   is equivalent to V_x = Spec K, hence to unramifiedness of G_x over K. No field
   extension or perfectness is needed. -/
theorem fieldPoint_factors_dmOpen_iff_unramified_automorphismSpace {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S))
    (hstack : IsModuliStack F) (hdiag : HasAlgebraicSpaceDiagonal F)
    (hatlas : ∃ (P : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj P)) F),
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSurjective Z T p ∧
          ∀ (V : Over S) (b : yoneda.obj V ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Smooth ((yoneda.preimage (b ≫ p)).left))
    (U : OpenModuliSubstack F) (hU : HasUnramifiedModuliDiagonal U.category)
    (hmax : ∀ V : OpenModuliSubstack F,
      HasUnramifiedModuliDiagonal V.category → V.IsContainedIn U)
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ S)
    (x : BasedFunctor (discreteModuli (yoneda.obj (Over.mk a))) F)
    (G : AlgebraicSpace S) (p : G.obj.obj ⟶ yoneda.obj (Over.mk a))
    (hG : IsModuliAutomorphismSpace (Over.mk a) x G p) :
    (∃ y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk a))) U.category,
      Nonempty (ModuliTwoIso (y.comp (fullModuliInclusion F U.property)) x)) ↔
        SpaceMapIsUnramified G (Over.mk a) p := by
  sorry

end CategoryTheory
