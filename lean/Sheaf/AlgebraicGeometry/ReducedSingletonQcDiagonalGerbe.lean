/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.AlgebraicGeometry.ModuliInertia
import Sheaf.AlgebraicGeometry.SpaceSmoothReducedLocality
import Sheaf.AlgebraicGeometry.ReducedSingletonFieldFactorization

/-! # A reduced singleton algebraic stack is a gerbe over a field

Source: Stacks Project, Morphisms of Stacks, Tags 06RC and 0DQL; Descent on Spaces,
Tag 0GB3; Decent Spaces, Tags 03JX, 03JV, 0H1T and 047Z
(blueprint: lem-sfb-reduced-singleton-qc-diagonal-gerbe).

The two gerbe conditions are written using covering sieves on the existing big fppf site.
Objects over a test scheme are its morphisms to the stack, retaining their 2-isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory

/-- A reduced algebraic stack with exactly one point and quasi-compact relative diagonal
is a gerbe over the spectrum of a field extension, without finiteness assumptions.
Source: Stacks Project, Tags 06RC, 0DQL, 0GB3, 03JX, 03JV, 0H1T and 047Z
(blueprint: lem-sfb-reduced-singleton-qc-diagonal-gerbe).

Proof:
1. The inertia projection is the base change of the relative diagonal along itself
(def-sfb-moduli-inertia). The quasi-compactness tests of def-sfb-stack-qcqs-morphism are
stable under base change, so inertia is quasi-compact.
2. Apply lem-sfb-reduced-qc-inertia-dense-open-gerbe (06RC). Its dense open substack
has full point image, since the point space is a nonempty singleton. Scheme base changes
of that open immersion have all points and therefore are the whole scheme; here use
lem-sfb-smooth-presentation-closed-subsets for the base change of point images.
Thus the original stack is a gerbe over an algebraic space Q.
3. By lem-sfb-gerbe-smooth-universal-homeomorphism, Q has one point and the composite
of a reduced smooth atlas with the gerbe map is smooth and surjective. Apply
lem-sfb-space-smooth-reduced-locality to deduce reducedness of Q. By
lem-sfb-gerbe-qc-diagonal-descent, its relative diagonal is quasi-compact.
4. By lem-sfb-qs-space-field-monomorphism there is a quasi-compact monomorphism
j : Spec L → Q representing its point. Apply
lem-sfb-reduced-singleton-field-factorization to id_Q, giving g with jg = id_Q.
Cancellation by j gives gj = id, hence Q is Spec L over k. The structure morphism gives
the field extension k → L. Compose the gerbe map with g; the inverse j identifies every
fibre groupoid, preserving local existence and local isomorphisms on the fppf site. -/
theorem reduced_singleton_qc_diagonal_gerbe (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (hred : ∃ (U : Over (Spec (.of k)))
      (q : BasedFunctor (discreteModuli (yoneda.obj U)) F),
      IsSmoothModuliAtlas F U q ∧ AlgebraicGeometry.IsReduced U.left)
    (hpoint : Nonempty (ModuliPoints F) ∧ Subsingleton (ModuliPoints F))
    (hdiag : IsQuasiCompactAlgebraicModuliMap.{u, v, w, v, max w u, 0, 0}
      (moduliRelativeDiagonal (moduliBaseStructure F))) :
    ∃ (L : Type u) (_ : Field L) (ι : k →+* L)
      (p : BasedFunctor F
        (discreteModuli (yoneda.obj (Over.mk (Spec.map (CommRingCat.ofHom ι)))))),
      (∀ (T : Over (Spec (.of k)))
        (a : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ι))),
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over (Spec (.of k))) T ∧
          ∀ (U : Over (Spec (.of k))) (f : U ⟶ T), R f →
            ∃ x : BasedFunctor (discreteModuli (yoneda.obj U)) F,
              Nonempty (ModuliTwoIso (x.comp p) (discreteModuliMap (yoneda.map (f ≫ a))))) ∧
      (∀ (T : Over (Spec (.of k)))
        (a : T ⟶ Over.mk (Spec.map (CommRingCat.ofHom ι)))
        (x y : BasedFunctor (discreteModuli (yoneda.obj T)) F),
        Nonempty (ModuliTwoIso (x.comp p) (discreteModuliMap (yoneda.map a))) →
        Nonempty (ModuliTwoIso (y.comp p) (discreteModuliMap (yoneda.map a))) →
        ∃ R : Sieve T, R ∈ (Scheme.fppfTopology.over (Spec (.of k))) T ∧
          ∀ (U : Over (Spec (.of k))) (f : U ⟶ T), R f →
            Nonempty (ModuliTwoIso ((discreteModuliMap (yoneda.map f)).comp x)
              ((discreteModuliMap (yoneda.map f)).comp y))) := by
  sorry

end CategoryTheory
