/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.AlgebraicGeometry.RelativeDualizingPair
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
import Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism
import Sheaf.TraceFormula.AlgebraicShriekCalculus
import Sheaf.TraceFormula.AlgebraicShriekRelativePerfect
import Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent

/-! # Rigidity of supplied coherent relative dualizing pairs

Source: Stacks Project, duality.tex, Tags 0E2T, 0E2V and 0E2W.
(blueprint: lem-trf-relative-dualizing-pair-rigidity).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A supplied relative dualizing pair has only scalar derived endomorphisms, and
there is exactly one isomorphism to any other supplied pair preserving its diagonal class.
Source: Stacks 0E2V and 0E2W (blueprint: lem-trf-relative-dualizing-pair-rigidity).

Proof, following the node:
1. Cover X by affine U = Spec A mapping into affine Noetherian V = Spec R in S.
Use lem-trf-affine-relative-dualizing-comparison to obtain a pseudo-coherent A-complex M
of finite R-Tor amplitude. For B = A tensor_R A, its first-factor extension M₁ has
RHom_B(A,M₁) isomorphic to A, and the diagonal class generates its degree-zero Hom module.
Do the same for a second pair.
2. Choose a polynomial presentation P = R[x₁,...,xₙ] onto A and C = RHom_P(A,P)[n].
The lem-trf-algebraic-shriek-calculus and lem-trf-algebraic-shriek-relative-perfect
supply relative perfection and the scalar endomorphism isomorphism for C. Flat base
change identifies C extended along the first coprojection with the shriek image along
the second. Composition with multiplication B → A identifies RHom_B(A,C₁) with A.
The Noetherian finite-type-algebra theorem applies to P, A and B; no regular kernel
of the polynomial presentation is assumed.
3. The lem-trf-algebraic-relative-dualizing-isomorphism identifies M with C. Conjugating
transports the scalar map. Affine pseudo-coherent RHom comparison sheafifies it;
finite relative Tor amplitude bounds M below. Internal Hom commutes with open
restriction. Thus the cone of the global scalar map has zero cohomology on a basis,
hence globally. This proves the first assertion.
4. The algebraic isomorphism and affine derived equivalence give a local isomorphism
between K and L. Its action on the two diagonal generators differs by a unique unit.
Multiply the isomorphism by the inverse unit. The scalar calculation proves uniqueness
of this normalized isomorphism and vanishing of negative self-extensions on every
basis open.
5. On inclusions of basis opens the normalized isomorphisms agree by uniqueness.
Apply lem-trf-derived-basis-bbd-descent with the canonical restriction identifications
of K and those of L adjusted by these local isomorphisms. Its unique-isomorphism
clause produces a global isomorphism with the prescribed local restrictions.
This is basis descent, with no finite-cover or affine-intersection assumption.
6. The multiplication isomorphism for L and the derived-Hom/global-sections identity
identify the global class module with Γ(X,O_X), sending η to 1. The global isomorphism
sends ξ to vη, and v restricts to 1 on the basis. Sheaf uniqueness gives v = 1.
Another class-preserving isomorphism agrees locally; BBD uniqueness makes it equal
globally. This proves existence and uniqueness with the stated normalization.
7. For any open U, pseudo-coherence and the local relative Tor bounds restrict.
The diagonal algebra restricts to the diagonal algebra on U ×_S U; pullback and
internal Hom commute with these open restrictions, preserving the class condition.
The restricted morphism remains separated, flat and locally finitely presented.
The same argument proves the assertions there, as recorded by the next theorem.
For the empty open all module sheaves and derived objects are zero. -/
theorem relativeDualizingPair_rigidity
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    (K : schemeDerivedCategory X)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
      (derivedPullback (pullback.fst f f)).obj K)
    (hK : IsCoherentRelativeDualizingPair f K ξ) :
    IsIso (relativeDualizingScalarMap X K) ∧
      ∀ (L : schemeDerivedCategory X)
        (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f) ⟶
          (derivedPullback (pullback.fst f f)).obj L),
        IsCoherentRelativeDualizingPair f L η →
          ∃! α : K ≅ L, ξ ≫ (derivedPullback (pullback.fst f f)).map α.hom = η := by
  sorry

/-- Both rigidity assertions on every open restriction, without a quasi-compactness condition.
Source: Stacks 0E2T--0E2W and the open-restriction observation in 0E2X
(blueprint: lem-trf-relative-dualizing-pair-rigidity).
Proof: step 7 of relativeDualizingPair_rigidity. Restrict the local representatives
for pseudo-coherence and relative Tor amplitude. Restrict the diagonal and its class
to U ×_S U, using compatibility of derived pullback and internal Hom with opens.
All hypotheses on U → S hold by locality on the source, with the same base S.
Apply steps 1--6 to these supplied pairs. The empty open has the zero module category,
so its scalar map and unique isomorphism satisfy the same assertions. -/
theorem relativeDualizingPair_rigidity_on_open
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (V : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over V))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [Flat f] [LocallyOfFinitePresentation f] [IsLocallyNoetherian S]
    (U : X.Opens) (K : schemeDerivedCategory U.toScheme)
    (ξ : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex (U.ι ≫ f)) ⟶
      (derivedPullback (pullback.fst (U.ι ≫ f) (U.ι ≫ f))).obj K)
    (hK : IsCoherentRelativeDualizingPair (U.ι ≫ f) K ξ) :
    IsIso (relativeDualizingScalarMap U.toScheme K) ∧
      ∀ (L : schemeDerivedCategory U.toScheme)
        (η : DerivedCategory.Q.obj (relativeDualizingDiagonalComplex (U.ι ≫ f)) ⟶
          (derivedPullback (pullback.fst (U.ι ≫ f) (U.ι ≫ f))).obj L),
        IsCoherentRelativeDualizingPair (U.ι ≫ f) L η →
          ∃! α : K ≅ L,
            ξ ≫ (derivedPullback (pullback.fst (U.ι ≫ f) (U.ι ≫ f))).map α.hom = η := by
  sorry

end AlgebraicGeometry
