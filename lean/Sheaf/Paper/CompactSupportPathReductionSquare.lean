/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T9
-/
module

public import Sheaf.Paper.CompactSupportLimitEquationData

/-! # The normalized whole-system reduction square for compact-support paths

Source: the parent proof Steps 3--8, Stacks 07A7, 099N and 0F7B--0F7F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportLimit
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (o : Operations l E) (r : Realizations l E D o)
  {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
  {T : Over (Spec (CommRingCat.of D.k))} (hl : l ≠ D.p)

/-- Reduction intertwines the prescribed completed path with its entire strict
constant-coefficient tower path, before taking a derived limit.
Source: parent proof Steps 3--8; Stacks 07A7, 099N, 0F7B--0F7F
(blueprint: lem-pur-compact-support-path-reduction-square).

Proof: identify completed and constant coefficients by the unit-normalized scalar
comparison rho. For a pullback compositor use the common-quotient K-flat comparison
and the invertible reduction of the completion unit; tensor reassociation identifies
the compositor before any evaluation. For an exchange use the specified proper
counit-tensor mate followed by proper image of the open beta. The strict-tower
realization and open-mate normalization identify both factors under rho. Expansion
is the identity because compact support is the supplied proper/open composite.
For a refinement apply the ringed refinement coefficient square on the diagram
site to the constant-to-quotient ring map. Its clopen projector is identity on the
section and zero on its complement, and scalar restriction preserves both pieces.
The direct-image compositor normalization then identifies the outer proper factors
with systemRefinement and the published integralRefinement inverse. These are
identities of whole strict systems, not consequences of evaluated equalities.
For an inverse invert the reduction square, using functoriality and the stated
isomorphisms. For a composite multiply the two squares and cancel the intermediate
reduction comparison. For the four whiskering constructors use the natural
proper/open comparisons and normalized completed-pullback system substitution;
recursion identifies the word comparisons with the whiskered comparisons. The
intermediate domain in Path.comp supplies all bounds and origins. Induction on
Path proves the displayed square. Identity, zero and empty-site cases are the
functor identity laws; no pullback is asserted to commute with arbitrary limits.
-/
theorem compactSupportPathReductionSquare
    (e t : Expression _ I X T) (ge : e.geometric) (gt : t.geometric)
    (we : IsWord e) (wt : IsWord t) (se : SeparatedWord e) (st : SeparatedWord t)
    (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
    (ie : IntegralDomain l E e K.obj) (it : IntegralDomain l E t K.obj)
    (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K.obj))
    (a : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.evaluate (integralInterpretation l E)).obj K.obj)
    (h : Path l E D o r hl K.obj e t s a) :
    (GeneratorReduction.constantReduction l E T.left).map
        ((GeneratorReduction.H l E T.left).map a) ≫
        (reductionComparison l E D o r t gt ⟨K.obj, ht⟩).hom =
      (reductionComparison l E D o r e ge K).hom ≫ towerMap l E D o K.obj s := by
  sorry

end WeilConjectures.CompactSupportLimit
