/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import WeilConjectures.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover

/-! # Flat locally finitely presented spaces over an infinitesimal pushout

Source: Stacks Project, spaces-pushouts.tex, Tag 07W3, part (3) and the final equivalence;
Tag 07SY for agreement with scheme pushouts
(blueprint: lem-sfb-flat-lfp-space-pushout-gluing).

The equivalence is stated by preservation of objects under the canonical pullback
functors, essential surjectivity with the specified gluing isomorphism, and unique
lifting of every compatible pair of morphisms. Morphisms are all maps in the presheaf
slice, not just isomorphisms. Pullback associativity is expanded using `Over.pullbackComp`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An object of the category F(T): an algebraic space with a flat locally finitely
presented map to T. Both properties use the existing tests on every etale scheme chart.
Source: Stacks, Tag 07W3(3) (blueprint: lem-sfb-flat-lfp-space-pushout-gluing). -/
structure FlatLfpSpaceFamily {B : Scheme.{u}} (T : Over B) where
  space : AlgebraicSpace B
  projection : space.obj.obj ⟶ yoneda.obj T
  flat : AlgebraicSpace.MapToSchemeIsLocally (@Flat) space T projection
  lfp : AlgebraicSpace.MapToSchemeIsLocally (@LocallyOfFinitePresentation) space T projection

namespace FlatLfpSpaceFamily

/-- The actual projection in the presheaf slice. Its Hom sets are exactly all maps of
algebraic spaces over T, since algebraic spaces form a full subcategory of sheaves.
Source: Stacks, Tag 07W3 (blueprint: lem-sfb-flat-lfp-space-pushout-gluing). -/
def presentation {B : Scheme.{u}} {T : Over B} (X : FlatLfpSpaceFamily T) :
    Over (yoneda.obj T) :=
  Over.mk X.projection

/-- The canonical presheaf pullback again has an algebraic-space source and the two
required chartwise properties. The isomorphism preserves the base projection.
Source: Stacks, Tag 07W3 (blueprint: lem-sfb-flat-lfp-space-pushout-gluing). -/
def HasPullback {B : Scheme.{u}} {T U : Over B} (f : T ⟶ U) : Prop :=
  ∀ X : FlatLfpSpaceFamily U, ∃ Y : FlatLfpSpaceFamily T,
    Nonempty (Y.presentation ≅ (Over.pullback (yoneda.map f)).obj X.presentation)

/-- The canonical base-change functor across a scheme infinitesimal pushout is an
equivalence on flat locally finitely presented spaces, with all morphisms as arrows.
The three conjuncts are well-defined restriction, essential surjectivity on the exact
specified triples, and bijectivity on every Hom set. Each occurrence of the iterated
restriction comparison is pullback associativity, transport by the square equation,
and inverse associativity, in that order.

Source: Stacks, Tag 07W3(3) and final equivalence, with Tag 07SY
(blueprint: lem-sfb-flat-lfp-space-pushout-gluing).

Proof plan from the node:
1. The scheme affine-thickening pushout lemma makes S -> P a thickening and the square
   cartesian. Fibre-product functoriality and stack-chartwise-smooth-etale-calculus
   preserve flatness and local finite presentation under the four restrictions.
2. Given (X,Y,phi), form Z = X amalg_U Y by space-affine-thickening-pushout, with
   U = X times_S T identified with Y times_T' T by phi. Its recovery isomorphisms
   identify the restrictions with X and Y with exactly the specified overlap phi.
   Pushout uniqueness defines the gluing functor on every compatible pair of arrows.
3. Choose compatible etale scheme charts by space-pushout-compatible-etale-charts.
   Scheme-pushout-flat-patching makes their pushout flat and locally finitely presented
   over P. Testing on this surjective etale atlas proves the same for Z.
4. For W over P, let D be the pushout of its restrictions and epsilon : D -> W its
   canonical map. A surjective etale scheme atlas W1 -> W is flat over P. The scheme
   flat-patching counit identifies the pushout Q of its restrictions with W1.
   Compatible etale charts make Q -> D surjective etale; epsilon composed with it
   is the atlas W1 -> W, by agreement on both pushout pieces.
5. For a scheme chart C -> D and a test scheme L -> W, the scheme R_L obtained from
   Q times_D C by base change to L covers C_L surjectively and etale. Its map to L
   is etale by chartwise-etale-permanence and fibre-product permanence. Apply
   etale-descent-through-source-cover to obtain C_L -> L etale. Thus epsilon is
   chartwise etale, without requiring a quasi-compact atlas.
6. Space-pushout recovery identifies the base change of epsilon to W_S with the
   identity of W_S. The scheme pushout makes W_S -> W a thickening, also for a
   non-nilpotent nil ideal: a finite sum of nilpotent generators is nilpotent, with
   exponent 1 + sum(n_i - 1). Space-etale-thickening-detects-iso makes epsilon an
   isomorphism. Its naturality follows by uniqueness on the two pushout pieces.
7. Given any compatible pair of maps on restrictions, glue them to g : D -> W'.
   Then g composed with epsilon inverse is the unique map W -> W' restricting to
   that pair. Agreement and uniqueness follow from fibre-product and pushout
   uniqueness. This is full faithfulness on all arrows; together with steps 2--3
   it proves the equivalence without properness, quasi-compactness, a uniform
   nilpotence bound, or a fibre-dimension condition. -/
theorem infinitesimalPushout
    {B : Scheme.{u}} {T S T' P : Over B}
    (a : T ⟶ S) (i : T ⟶ T') (j : S ⟶ P) (b : T' ⟶ P)
    (hi : IsThickening i.left) [IsAffineHom a.left]
    (h : a ≫ j = i ≫ b) (hp : IsPushout a.left i.left j.left b.left) :
    (HasPullback j ∧ HasPullback b ∧ HasPullback a ∧ HasPullback i) ∧
    (∀ (X : FlatLfpSpaceFamily S) (Y : FlatLfpSpaceFamily T')
      (φ : (Over.pullback (yoneda.map a)).obj X.presentation ≅
        (Over.pullback (yoneda.map i)).obj Y.presentation),
      ∃ (W : FlatLfpSpaceFamily P)
        (s : (Over.pullback (yoneda.map j)).obj W.presentation ≅ X.presentation)
        (t : (Over.pullback (yoneda.map b)).obj W.presentation ≅ Y.presentation),
        (((Over.pullbackComp (yoneda.map a) (yoneda.map j)).symm ≪≫
          eqToIso (congrArg (fun f : yoneda.obj T ⟶ yoneda.obj P ↦ Over.pullback f)
            (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ≪≫
          Over.pullbackComp (yoneda.map i) (yoneda.map b)).app W.presentation) ≪≫
            (Over.pullback (yoneda.map i)).mapIso t =
          (Over.pullback (yoneda.map a)).mapIso s ≪≫ φ) ∧
    (∀ (X Y : FlatLfpSpaceFamily P)
      (s : (Over.pullback (yoneda.map j)).obj X.presentation ⟶
        (Over.pullback (yoneda.map j)).obj Y.presentation)
      (t : (Over.pullback (yoneda.map b)).obj X.presentation ⟶
        (Over.pullback (yoneda.map b)).obj Y.presentation),
      (Over.pullback (yoneda.map a)).map s ≫
          (((Over.pullbackComp (yoneda.map a) (yoneda.map j)).symm ≪≫
            eqToIso (congrArg (fun f : yoneda.obj T ⟶ yoneda.obj P ↦ Over.pullback f)
              (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ≪≫
            Over.pullbackComp (yoneda.map i) (yoneda.map b)).app Y.presentation).hom =
        (((Over.pullbackComp (yoneda.map a) (yoneda.map j)).symm ≪≫
          eqToIso (congrArg (fun f : yoneda.obj T ⟶ yoneda.obj P ↦ Over.pullback f)
            (by rw [← Functor.map_comp, ← Functor.map_comp, h])) ≪≫
          Over.pullbackComp (yoneda.map i) (yoneda.map b)).app X.presentation).hom ≫
            (Over.pullback (yoneda.map i)).map t →
      ∃! f : X.presentation ⟶ Y.presentation,
        (Over.pullback (yoneda.map j)).map f = s ∧
          (Over.pullback (yoneda.map b)).map f = t) := by
  sorry

end FlatLfpSpaceFamily

end AlgebraicGeometry
