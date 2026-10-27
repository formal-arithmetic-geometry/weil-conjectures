module

public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore

/-! # Canonical integral finite-extension comparisons

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

The defining comparisons are publicly re-exported from the models module.
This module fixes the maps and predicates independently of their compatibility theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)

/-- Finite-free scalar extension is triangulated and its canonical dualizing and
internal-Hom maps are invertible. No compatibility square is asserted here.
Source: current blueprint lem-coef-integral-finite-extension.proof.md, paragraphs 1-5
(blueprint: lem-sf-integral-finite-extension-invertibility).

Proof: on flat-term K-flat representatives the strict scalar construction is the
Roos total limit of quotient tensor functors. Additive tensor and exact products
preserve the signed cone triangles, so the induced functor is triangulated.
At ramification-multiple levels finite-free coefficient change makes the finite
counit-defined dualizing map invertible; tensoring down to an arbitrary quotient
and finite dualizing change preserves this assertion. These coherent comparisons
form an equivalence of normalized towers. Their total limit is invertible and,
by its finite counit equations and u_existsUnique, equals the specified u.
For Hom choose a finite free basis of the completed target ring over the source.
After restriction of scalars both sides of the evaluation transpose homMap are
finite sums of RHom(K,M). Restriction preserves K-injectives because its left
adjoint is exact, and finite sums commute with the Hom complex. On every basis
component homMap is the identity, so it is invertible. Restriction detects
quasi-isomorphisms. Conjugate with the three completion isomorphisms to obtain
invertibility of v. A basis tests invertibility only; it does not define the maps.
The arguments cover degree one extensions, zero inputs and empty X. -/
theorem comparison_invertibility
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X)) :
    (∃ (_ : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated) ∧
    IsIso (u l E L ι X D hl wE wL) ∧
    (∀ K M : sfIntegralConstructibleCategory l E X,
      IsIso (v l E L ι X a b K.obj M.obj K.property.1 M.property.1)) := by
  sorry

end WeilConjectures.IntegralFiniteExtension
