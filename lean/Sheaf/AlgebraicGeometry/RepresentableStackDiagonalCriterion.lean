module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-!
# Diagonal criterion for representable morphisms of Deligne--Mumford stacks

Source: Stacks Project, stacks-morphisms.tex, Tags 04YQ (1), (3), (5) and
04YS (1)--(3) (blueprint: lem-sfb-representable-stack-diagonal-criterion).

Scheme tests retain the actual projection of the 2-base change. Separatedness of each
algebraic-space base change is the closed-immersion property of its presheaf diagonal.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- The relative diagonal is scheme-representable, monomorphic and locally quasi-finite;
separatedness on all algebraic-space base changes is equivalent to a closed or proper
relative diagonal on all scheme tests.
Source: Stacks Project, stacks-morphisms.tex, Tags 04YQ (1), (3), (5) and 04YS (1)--(3)
(blueprint: lem-sfb-representable-stack-diagonal-criterion).

Proof:
1. The étale atlases of the two DM stacks are smooth, so their Isom sheaves are algebraic
   spaces locally of finite type. A scheme map to the relative self-product is a triple
   `(x₁, x₂, α)`. Its diagonal pullback has objects `(z, a, b)` with `f(b) = α f(a)`.
   Sending this to `β = b a⁻¹` identifies the pullback with the discrete sheaf of
   isomorphisms `β : x₁ ≅ x₂` satisfying `f(β) = α`. The unique arrow between two
   representatives with the same β is `a'⁻¹ a`, and β has representative `(x₁, 1, β)`.
   This description commutes with restriction, so the pullback is the algebraic space
   `U ×_{Isom_Y} Isom_X`.
2. The composite `Isom_X → Isom_Y → U` is locally of finite type. Cancellation for
   algebraic spaces makes the first arrow locally of finite type, hence so is its
   pullback to U, by base change in the finite-type calculus.
3. Representability of f makes every fibre functor faithful: an automorphism killed
   by f is an automorphism in a discrete algebraic-space fibre, so is the identity.
   Thus at most one β lifts α, making the pullback a monomorphism. A locally finite-type
   monomorphism of spaces is separated and locally quasi-finite. A separated locally
   quasi-finite algebraic space over the scheme U is a scheme. Its identity chart gives
   local quasi-finiteness of the resulting scheme projection.
4. If the relative diagonal is closed on scheme tests, the diagonal of every base change
   `A = X ×_Y T → T` is closed on scheme tests: its sections are β with
   `θ₂ f(β) = θ₁`, exactly the diagonal pullback for `(x₁, x₂, θ₂⁻¹ θ₁)`.
   This identification respects restriction, so A → T is separated.
5. Conversely, use the separated space `A = X ×_{Y,f(x₂)} U` and its two sections
   `(x₁, α)` and `(x₂, 1)`. Pulling back its diagonal gives exactly the sheaf of β
   with `f(β) = α`, so every scheme test of the relative diagonal is closed.
6. Each scheme test is already a monomorphism by step 3. The proper-monomorphism
   criterion therefore makes its closed-immersion property equivalent to properness.
   Quantify over all tests and combine this with steps 4--5. -/
theorem representableStack_diagonal_criterion {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor X Y) (hX : IsDeligneMumfordModuliStack X)
    (hY : IsDeligneMumfordModuliStack Y) (hf : IsRepresentableByAlgebraicSpaces f) :
    ModuliSchemeTest (fun _ _ p ↦ Mono p ∧ Scheme.Hom.IsLocallyQuasiFinite p)
      (moduliRelativeDiagonal f) ∧
    ((∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) Y),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z p ∧ AlgebraicSpace.MapToSchemeIsSeparated Z T p) ↔
      ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal f)) ∧
    (ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal f) ↔
      ModuliSchemeTest @IsProper (moduliRelativeDiagonal f)) := by
  sorry

end CategoryTheory
