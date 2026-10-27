/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Mathlib.Topology.Separation.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Rational objects on universally closed algebraic stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 0DQN, 06RC, 0DQL, 06R9 and 0DN8;
decent-spaces.tex, Tag 047Z; morphisms.tex, Tag 01WM
(blueprint: lem-sfb-universally-closed-stack-rational-point).

Universal closedness uses the smooth-presentation topology on the actual 2-fibre products.
The diagonal conditions are tested on their algebraic-space scheme base changes.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A nonempty universally closed algebraic stack with quasi-compact separated diagonal
and a quasi-compact smooth atlas has an object over the same algebraically closed field.
No local finite-type or Noetherian hypothesis is imposed.
Source: Stacks Project, Tags 0DQN, 06RC, 0DQL, 06R9, 0DN8, 047Z and 01WM
(blueprint: lem-sfb-universally-closed-stack-rational-point).

Proof:
1. By lem-sfb-qc-diagonal-stack-spectral the point space is compact and Kolmogorov.
Use lem-sc-quasi-compact-kolmogorov-closed-point to obtain a closed point z.
The lemma lem-sfb-smooth-presentation-closed-subsets supplies its reduced closed
substack C with singleton support.
2. The diagonal of C is the base change of the original diagonal, since a closed
substack is full; it is quasi-compact by def-sfb-stack-qcqs-morphism. For every scheme
base change, lem-sfb-stack-closed-immersion-calculus makes the inclusion of C a closed
embedding on points. Therefore C inherits universal closedness.
3. Apply lem-sfb-reduced-singleton-qc-diagonal-gerbe to obtain a field extension L/K
and a gerbe C to Spec L. By lem-sfb-gerbe-smooth-universal-homeomorphism this map is
smooth and surjective and induces a homeomorphism after every stack base change.
4. For every K-scheme T, pull back that homeomorphism to Spec L times T. A closed
subset of this scheme pulls back to a closed subset of C times T, with the same image
in T. Universal closedness of C therefore makes Spec L to Spec K universally closed.
This map is affine, so pqf-lem-integral-univclosed makes L integral over K.
5. For each element of L a monic polynomial over K vanishes on it. As K is algebraically
closed, factor this polynomial into linear factors. Since L is a field, one factor
vanishes, putting the element in K. Hence K to L is an isomorphism.
6. A smooth surjective scheme atlas of C is now a nonempty smooth K-scheme, by
 def-sfb-algebraic-moduli-stack. The field K is separably closed, so
lem-pc-rational-points-dense supplies a K-point of this atlas. Compose it with the
atlas and the inclusion of C to obtain the required K-object of the original stack. -/
theorem universallyClosedStack_nonempty_rationalObjects (K : Type u) [Field K] [IsAlgClosed K]
    (F : BasedCategory.{v, w} (Over (Spec (.of K))))
    (hF : IsAlgebraicModuliStack F) (hne : Nonempty (ModuliPoints F))
    (hqc : IsQuasiCompactModuli F)
    (hdiag : ∀ (T : Over (Spec (.of K)))
      (t : BasedFunctor (discreteModuli (yoneda.obj T))
        (moduliTwoFiberProduct (moduliBaseStructure F) (moduliBaseStructure F))),
      ∃ (Z : AlgebraicSpace (Spec (.of K))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure F)) T t Z p ∧
          AlgebraicSpace.MapIsQuasiCompact p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T p)
    (hclosed : ∀ T : Over (Spec (.of K)),
      @IsClosedMap _ _
        (moduliSmoothPointTopology (moduliTwoFiberProduct (moduliBaseStructure F)
          (moduliBaseStructure (discreteModuli (yoneda.obj T)))))
        (moduliSmoothPointTopology (discreteModuli (yoneda.obj T)))
        (moduliPointMap (moduliTwoFiberSnd (moduliBaseStructure F)
          (moduliBaseStructure (discreteModuli (yoneda.obj T)))))) :
    Nonempty (Functor.Fiber F.p (Over.mk (𝟙 (Spec (.of K))))) := by
  sorry

end CategoryTheory
