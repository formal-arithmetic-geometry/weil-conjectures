/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Sheaf.AlgebraicGeometry.FiniteStackSchemeTests
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.RelativeInertiaSecondDiagonalGeometry
import Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Separated source and finite target inertia

Source: Stacks Project, Tags 050M(3), 0CL0(1), 01WN and the final paragraph of 0DUE
(blueprint: lem-sfb-separated-source-finite-inertia-target).

Separatedness is properness of the relative diagonal. Each proper representable map is
expressed using algebraic-space presentations of all scheme base changes, with their
actual projection proper as an algebraic-space map. In particular these tests do not
require a proper algebraic space to be a scheme. No DM hypothesis is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- A map from a separated algebraic stack to one with finite inertia is separated.
Source: Stacks Project, Tags 050M(3), 0CL0(1), 01WN, and 0DUE
(blueprint: lem-sfb-separated-source-finite-inertia-target).

Proof:
1. First establish cancellation as in stack_separated_of_comp_diagonal_separated below.
   Put D = A ×_B A and E = A ×_C A. These are algebraic by
   lem-sfb-algebraic-stack-fibre-products. The forgetful D → E is the base change
   of Δ_g. On objects its extra comparison is recovered as g(β). The diagonal is
   representable by lem-sfb-relative-inertia-second-diagonal-geometry; use
   lem-sfb-fibred-groupoid-representable-smooth-calculus for base-change
   representability and lem-sfb-stack-separation-compactness-permanence for
   separatedness. The composite with Δ_f is Δ_(gf), with its canonical 2-isomorphism.
2. For a scheme T → D, put V = A ×_E T and W = D ×_E T. Both are algebraic spaces
   by the representability in step 1 and the relative-inertia geometry node.
   V → T is proper and W → T separated. By lem-sfb-space-proper-cancellation,
   V → W is proper. The given T → D supplies a section T → W, and
   A ×_D T = V ×_W T by the compatibility of the comparison isomorphisms.
   Pull back along this section using lem-sfb-space-proper-base-change. This
   proves properness of the actual test of Δ_f, including the essential last pullback.
3. For separated inertia p : I_B → B, its diagonal is a closed immersion by
   lem-sfb-stack-separation-compactness-permanence. The neutral section is its
   pullback along (id, ep): equality of an automorphism with the identity is precisely
   the neutral section. Use lem-sfb-stack-closed-immersion-calculus and
   lem-sfb-space-closed-subspace-proper. The second-diagonal identification in
   lem-sfb-relative-inertia-second-diagonal-geometry proves separatedness of Δ_(B/k).
4. Finite inertia has finite scheme tests. They are proper by lem-sfb-affine-proper-finite
   (Mathlib IsFinite.iff_isProper_and_isAffineHom), hence separated by
   def-weil-proper-morphism. Representable compatibility in
   lem-sfb-stack-separation-compactness-permanence gives separated inertia.
   Apply step 3 and cancellation to f followed by the structural map of B.
   Its composite is the given separated structural map of A. -/
theorem stack_separated_source_finite_inertia_target
    (k : Type u) [Field k]
    (A : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (B : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (f : BasedFunctor A B)
    (hAsep : (∀ (T : Over (Spec (.of k)))
          (t : BasedFunctor (discreteModuli (yoneda.obj T))
            (moduliTwoFiberProduct (moduliBaseStructure A) (moduliBaseStructure A))),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange (moduliRelativeDiagonal (moduliBaseStructure A)) T t Z p ∧
            MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T)))
    (hI : IsRepresentableFiniteModuliMap (moduliInertiaProjection B)) :
    ∀ (T : Over (Spec (.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj T))
          (moduliTwoFiberProduct f f)),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p ∧
          MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T) := by
  sorry

/-- Cancellation of separatedness when the second morphism has separated diagonal.
Source: Stacks Project, Tag 050M(3) and its Tag 050H cartesian square
(blueprint: lem-sfb-separated-source-finite-inertia-target).

Proof: These are steps 1--2 above. Algebraic-stack fibre products and relative-diagonal
representability give D → E as the representable base change of Δ_g. The permanence
node gives separatedness of D → E. For T → D, properness of V → T and separatedness
of W → T imply properness of V → W by lem-sfb-space-proper-cancellation.
The section T → W then gives A ×_D T = V ×_W T, proper over T by
lem-sfb-space-proper-base-change. All comparisons retain their canonical 2-isomorphisms.
The cited fibre-product, relative-inertia and representable calculus nodes justify
all the algebraic-space tests, exactly as in steps 1--2 above. -/
theorem stack_separated_of_comp_diagonal_separated
    (k : Type u) [Field k]
    (A : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (B : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (C : BasedCategory.{v₃, w₃} (Over (Spec (.of k))))
    (hA : IsAlgebraicModuliStack A) (hB : IsAlgebraicModuliStack B)
    (hC : IsAlgebraicModuliStack C) (f : BasedFunctor A B) (g : BasedFunctor B C)
    (hcomp : (∀ (T : Over (Spec (.of k)))
          (t : BasedFunctor (discreteModuli (yoneda.obj T))
            (moduliTwoFiberProduct (f.comp g) (f.comp g))),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange (moduliRelativeDiagonal (f.comp g)) T t Z p ∧
            MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T)))
    (hdiag : (∀ (T : Over (Spec (.of k)))
          (t : BasedFunctor (discreteModuli (yoneda.obj T))
            (moduliTwoFiberProduct (moduliRelativeDiagonal g) (moduliRelativeDiagonal g))),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange (moduliRelativeDiagonal (moduliRelativeDiagonal g)) T t Z p ∧
            MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T))) :
    ∀ (T : Over (Spec (.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj T))
          (moduliTwoFiberProduct f f)),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p ∧
          MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T) := by
  sorry

/-- Separated inertia implies that the structural diagonal is separated.
Source: Stacks Project, Tag 0CL0(1), implication (a) to (b)
(blueprint: lem-sfb-separated-source-finite-inertia-target).

Proof: This is step 3 above. The inertia geometry node makes inertia algebraic and
its projection representable. Representable compatibility in
lem-sfb-stack-separation-compactness-permanence identifies the diagonal of its
separated projection with a closed immersion. Pull it back along (id, ep).
An automorphism equal to the identity is exactly an object of the neutral section;
composition of the pullback comparisons and its inverse give that identification.
By lem-sfb-stack-closed-immersion-calculus this section is a closed immersion.
Its algebraic-space tests are proper by lem-sfb-space-closed-subspace-proper.
Identify the section with the second diagonal using
lem-sfb-relative-inertia-second-diagonal-geometry (including its absolute
specialization). This gives properness of the second diagonal, as required. -/
theorem stack_diagonal_separated_of_inertia_separated
    (k : Type u) [Field k]
    (B : BasedCategory.{v₂, w₂} (Over (Spec (.of k))))
    (hB : IsAlgebraicModuliStack B)
    (hIsep : (∀ (T : Over (Spec (.of k)))
          (t : BasedFunctor (discreteModuli (yoneda.obj T))
            (moduliTwoFiberProduct (moduliInertiaProjection B) (moduliInertiaProjection B))),
        ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
          HasSpaceBaseChange (moduliRelativeDiagonal (moduliInertiaProjection B)) T t Z p ∧
            MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T))) :
    ∀ (T : Over (Spec (.of k)))
        (t : BasedFunctor (discreteModuli (yoneda.obj T))
          (moduliTwoFiberProduct (moduliRelativeDiagonal (moduliBaseStructure B))
            (moduliRelativeDiagonal (moduliBaseStructure B)))),
      ∃ (Z : AlgebraicSpace (Spec (.of k))) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange
          (moduliRelativeDiagonal (moduliRelativeDiagonal (moduliBaseStructure B))) T t Z p ∧
          MapIsProper (ObjectProperty.homMk ⟨p⟩ : Z ⟶ schemeSpace T) := by
  sorry

end CategoryTheory
