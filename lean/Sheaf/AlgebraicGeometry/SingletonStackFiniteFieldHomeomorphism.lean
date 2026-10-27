/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.SpaceFieldDiscretenessCriterion
import Sheaf.AlgebraicGeometry.ReducedQuasiFiniteSpaceFieldDecomposition

/-! # A finite field base for a reduced singleton algebraic stack

Source: Stacks Project, stacks-morphisms.tex, Tags 06R6, 06QK, 06QI and 06R9;
spaces-descent.tex, Tag 06EW; decent-spaces.tex, Tag 0ACA; spaces-over-fields.tex,
Tag 06S0 (blueprint: lem-sfb-singleton-stack-finite-field-homeomorphism).

The conclusion uses the actual projection of the existing 2-fibre product and the
smooth-atlas topology on the existing field-valued point quotient. The test stack is
placed first in the product to use its canonical first projection.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A reduced singleton algebraic stack locally of finite type over a field admits a
map to a finite extension spectrum which is a homeomorphism on points after every
algebraic-stack base change. No condition on its inertia or separatedness is imposed.

Source: Stacks Project, Tags 06R6, 06QK, 06QI, 06R9, 06EW, 0ACA and 06S0
(blueprint: lem-sfb-singleton-stack-finite-field-homeomorphism).

Proof:
1. Choose the reduced smooth surjective atlas U. Its map to Spec k is locally of
finite type by hlft. Since k is Noetherian, pqf-lem-locnoeth-lft makes U locally
Noetherian. Apply lem-sfb-noetherian-singleton-gerbe (06QK) to obtain a gerbe
p : F -> Q over k, with Q a reduced locally Noetherian singleton algebraic space.
2. By lem-sfb-gerbe-smooth-universal-homeomorphism, the atlas composite U -> Q is
surjective, flat and locally finitely presented. Its composite to Spec k is locally
of finite type. Apply lem-sfb-representable-lft-fppf-source-descent (06EW) to
U -> Q -> Spec k, all maps here being maps of algebraic spaces. Thus Q is locally
of finite type over k; no representability of p is required.
3. The singleton point space of Q is discrete. By lem-sfb-space-field-discreteness-criterion
(0ACA), Q is locally quasi-finite over k, without a separation assumption. Apply
lem-sfb-reduced-quasifinite-space-field-decomposition (06S0). Its decomposition into
spectra of finite extensions has exactly one component because Q has exactly one
point. Thus there is a k-isomorphism e : Q -> Spec K with K finite-dimensional over k.
4. Take pi = e p. For any G -> Spec K, transport it along e inverse to a stack over Q.
The isomorphism e identifies the two 2-fibre products compatibly with their projections.
The universal homeomorphism clause of lem-sfb-gerbe-smooth-universal-homeomorphism
(06R9) gives the required IsHomeomorph of the canonical projection on point classes. -/
theorem exists_singleton_stack_finite_field_homeomorphism
    (k : Type u) [Field k] (F : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (hstack : IsAlgebraicModuliStack F)
    (hsingleton : Nonempty (ModuliPoints F) ∧ Subsingleton (ModuliPoints F))
    (hreduced : ∃ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a ∧
        ∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x))
    (hlft : ∀ (U : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U a → LocallyOfFiniteType U.hom) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Module.Finite k K ∧
      ∃ pi : BasedFunctor F (discreteModuli (yoneda.obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
        ∀ (G : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))),
          IsAlgebraicModuliStack G →
          ∀ g : BasedFunctor G (discreteModuli (yoneda.obj
            (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
            IsHomeomorph (moduliPointMap (moduliTwoFiberFst g pi)) := by
  sorry

end CategoryTheory
