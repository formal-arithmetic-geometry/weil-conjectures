/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicModuliStack
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # A flat locally finitely presented field cover of a singleton stack

Source: Stacks Project, Tags 06MP, 06MN and 06MM
(blueprint: lem-sfb-singleton-stack-flat-lfp-field-cover).

Field extensions are written as scheme morphisms between field spectra over the base.
The singleton condition includes a field-valued object and identifies every other one
with it over a common field extension. Representable-map properties are tested on the
actual algebraic-space base-change projections and their etale scheme charts.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory

/-- A reduced locally Noetherian smooth atlas and a singleton of field-valued points
supply a representable surjective flat locally finitely presented field cover.
Source: Stacks Project, Tags 06MP (1) implies (2), 06MN and 06MM
(blueprint: lem-sfb-singleton-stack-flat-lfp-field-cover).

Proof:
1. Choose a nonempty Noetherian affine open W = Spec R in the reduced atlas.
Choose a prime minimal over zero. Its localization E is a field, and is the stalk
at the corresponding generic point, by the minimal-prime localization and affine-stalk
lemmas. The canonical stalk-spectrum map is flat.
2. The composite Spec E -> W -> F is flat, since the second map is smooth. Its
scheme source and the algebraic-space diagonal give representability. Every field
object becomes isomorphic to this one over a common field extension, so it is surjective.
3. Choose a maximal ideal m of R. The quotient K = R/m is a field. Noetherianity
makes m finitely generated, so R -> K is finitely presented. Composition with the
smooth W -> F makes Spec K -> F locally finitely presented. It is representable
and surjective by the same diagonal and singleton arguments. Flatness remains to check.
4. Set T = Spec E x_F Spec K. Its projection p to Spec K is flat and surjective
by base change. Its projection q to Spec E is flat on etale scheme charts because
every scheme over a field is flat. Thus T -> F is flat by composition.
5. For every V -> F and etale scheme chart Q -> Spec K x_F V, set
D = T x_{Spec K} Q = (T x_F V) x_{Spec K x_F V} Q and take an etale surjective
scheme chart P -> D. Then P -> Q is flat and surjective and P -> V is flat.
Apply scheme flat source descent to P -> Q -> V, without a quasi-compactness
hypothesis. The chart criterion makes Spec K x_F V -> V flat. This proves flatness
of Spec K -> F and completes the construction. -/
theorem exists_singleton_stack_flat_lfp_field_cover
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
            ((discreteModuliMap (yoneda.map j)).comp y))) :
    ∃ (K : Type u) (_ : Field K) (s : Spec (.of K) ⟶ S)
      (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) F),
      IsRepresentableByAlgebraicSpaces a ∧
      (∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ S)
        (y : BasedFunctor (discreteModuli (yoneda.obj (Over.mk t))) F),
        ∃ (E : Type u) (_ : Field E) (e : Spec (.of E) ⟶ S)
          (i : Over.mk e ⟶ Over.mk s) (j : Over.mk e ⟶ Over.mk t),
          Nonempty (ModuliTwoIso
            ((discreteModuliMap (yoneda.map i)).comp a)
            ((discreteModuliMap (yoneda.map j)).comp y))) ∧
      ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange a T t Z p ∧
          ∀ (V : Over S) (b : yoneda.obj V ⟶ Z.obj.obj), AlgebraicSpace.IsEtale b →
            Flat ((yoneda.preimage (b ≫ p)).left) ∧
              LocallyOfFinitePresentation ((yoneda.preimage (b ≫ p)).left) := by
  sorry

end CategoryTheory
