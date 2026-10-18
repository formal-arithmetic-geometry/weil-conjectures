/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.RationalizationKaroubi

import Sheaf.Paper.DerivedCompleteIntegralDetailed
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-! # Composition of rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469 (blueprint: lem-weil-scalar-extension-composition).
-/

@[expose] public section

set_option autoImplicit false

universe d u

open CategoryTheory

namespace WeilConjectures

/-- Scalar extension along a tower of finite coefficient fields has a natural
composition isomorphism, compatible with the identity extensions at both ends.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).

Proof: 1. Every rational object is an integral object: no retract is adjoined by
`def-weil-rationalization-karoubi`. The integral objects are derived complete.
`lem-weil-finite-free-completed-scalar-comparison` identifies each of the three
completed extensions with ordinary derived extension over the completed ring sheaves.
`lem-weil-integral-scalar-extension-constructible` makes the second extension applicable.
2. Resolve by a K-flat complex with flat terms (`lem-pc-kflat-resolution`).
`lem-pur-derived-change-of-rings` computes extension termwise, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` preserves these good representatives.
The balanced maps ((p tensor s) tensor t) to p tensor st and p tensor t to
((p tensor 1) tensor t) are inverse chain maps. They commute with restrictions,
differentials and chain maps. Resolve the middle of a roof to extend naturality
to arbitrary derived morphisms, independently of the resolution. Conjugation
by the finite-free completed comparisons gives the integral comparison.
3. The integral comparison is linear in the final coefficient ring. Every rational
morphism is a finite sum of f tensor a. Tensor integral naturality by a and add;
the integral inverse rationalizes to the inverse. Thus the comparison is a natural
isomorphism on the actual raw localized categories.
4. Multiplication p tensor r to rp is the ordinary identity-extension comparison,
with inverse p to p tensor 1. If the first or second inclusion is an identity,
the associator formula is exactly its whiskered unit comparison. The completed
comparisons identify these units with the derived-completeness units. Naturality
of those comparisons cancels adjacent inverse factors. Hence both unit equations
hold before and after rationalization, including E=L=M. 
Complete DAG proof plan:
1. By [def-weil-rationalization-karoubi], $K$ is represented by an integral object $K_0\in
D^b_c(Y,\mathcal O_E)$; no retract has to be adjoined. For $F\in\{E,L,M\}$ write
$R_F=\widehat{\mathcal O}_{F,Y}$. These integral objects are derived complete by
[def-weil-derived-complete-integral-detailed]. Apply
[lem-weil-finite-free-completed-scalar-comparison] to the three extensions $E\subset L$,
$L\subset M$, and $E\subset M$. It identifies each completed scalar extension on a
derived-complete input with ordinary derived tensor by $R_L$ or $R_M$. By
[lem-weil-integral-scalar-extension-constructible] the first extension remains in
$D^b_c(Y,\mathcal O_L)$, so the second comparison applies to that object. Thus the desired
integral comparison reduces to $$  (K_0\otimes^L_{R_E}R_L)\otimes^L_{R_L}R_M\cong
K_0\otimes^L_{R_E}R_M. $$
2. Choose a K-flat resolution $P\to K_0$ with flat terms by [lem-pc-kflat-resolution]. The
change-of-rings computation [lem-pur-derived-change-of-rings] computes the first tensor by
$P\otimes_{R_E}R_L$. Applying [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the identity
topos with ring map $R_E\to R_L$ says that this complex is again K-flat with flat terms, so it
also computes the second tensor. Termwise, the map $$  ((p\otimes s)\otimes u)\longmapsto
p\otimes su,  \qquad p\otimes u\longmapsto(p\otimes1)\otimes u $$ is a pair of inverse balanced
maps, using the sheaf tensor product [def-pur-sheaf-tensor-product]. For example $(p\otimes
s)\otimes u=(p\otimes1)\otimes su$, which checks the less immediate composite. These maps respect
restrictions and commute with the differential because $s,u$ have degree zero. They define
inverse chain maps. The formulas commute with every chain map between K-flat complexes. A derived
morphism can be represented by a roof between such complexes: resolve the middle complex of a
roof by [lem-pc-kflat-resolution]. By [lem-pur-derived-change-of-rings], the quasi-isomorphism in
the left leg remains invertible after either scalar extension. Naturality for the two legs
therefore gives naturality for the roof, and also independence of the chosen resolution.
Conjugate this natural isomorphism by the canonical maps $\chi$ from Step 1 to get the integral
composition comparison.
3. For any integral derived morphism $f$, naturality proved for roofs in Step 2 gives
$c_{K'_0}\circ((f\otimes1)\otimes1)=(f\otimes1)\circ c_{K_0}$. For a chain-map representative
both sides send $((p\otimes s)\otimes u)$ to $f(p)\otimes su$; the roof argument supplies the
equality for arbitrary $f$. The comparison is linear over the final completed coefficient sheaf,
hence in particular over $\mathcal O_E$. By [def-weil-rationalization-karoubi], a rational
morphism is a finite sum of $f\otimes a$ with $a\in E$. The two composite scalar-extension
functors send it respectively to $((f\otimes1)\otimes1)\otimes a$ and $(f\otimes1)\otimes a$ in
the final rationalized Hom group over $M$. Tensor the displayed integral naturality equation by
$a$ and add. Therefore the image of the integral comparison is a natural isomorphism on the
actual rationalized categories, with inverse the image of the integral inverse. This constructs
the displayed isomorphism for every $K$.
4. The multiplication unit maps are $p\otimes r\mapsto rp$, with inverse $p\mapsto p\otimes1$. If
$L=E$, Step 2 sends $((p\otimes r)\otimes u)$ to $p\otimes ru=(rp)\otimes u$, which is precisely
application of the source unit map followed by extension. If $M=L$, it sends $((p\otimes
s)\otimes u)$ to $p\otimes su$, which is the target unit map. Under $\chi_{E/E}$ and $\chi_{L/L}$
these are the identity-extension comparisons because
[lem-weil-finite-free-completed-scalar-comparison] identifies those $\chi$ maps with the
derived-completeness units. If a fourth field is inserted, both iterated maps send $(((p\otimes
s)\otimes u)\otimes w)$ to $p\otimes suw$, so the ordinary tensor comparisons are coherent with
further composition. To check this after conjugation by $\chi$, expand each completed comparison
as the ordinary associator conjugated by its input and output $\chi$ maps. Naturality of $\chi$
moves each intervening map past scalar extension; adjacent $\chi^{-1}\chi$ factors cancel. The
two expanded composites consequently have the same outer $\chi$ maps and the ordinary tensor
composites just computed, proving completed coherence as well. All these equalities remain
equalities after the rationalization of [def-weil-rationalization-karoubi].
-/
theorem exists_rationalScalarExtension_composition
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y : AlgebraicGeometry.Scheme.{u}) :
    ∃ unit : ∀
        (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
        rationalScalarExtension D l hl E Y E (AlgHom.id (Padic l) E) ≅
          𝟭 (rationalConstructibleCategory D l hl E Y),
      ∃ comp : ∀
          (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
          (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
          (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
          (ι : E →ₐ[Padic l] L) (κ : L →ₐ[Padic l] M),
          rationalScalarExtension D l hl E Y L ι ⋙ rationalScalarExtension D l hl L Y M κ ≅
            rationalScalarExtension D l hl E Y M (κ.comp ι),
        (∀
            (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
            (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
            (ι : E →ₐ[Padic l] L),
            comp E E L (AlgHom.id (Padic l) E) ι =
              Functor.isoWhiskerRight (unit E) (rationalScalarExtension D l hl E Y L ι) ≪≫
                Functor.leftUnitor (rationalScalarExtension D l hl E Y L ι)) ∧
        (∀
            (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
            (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
            (ι : E →ₐ[Padic l] L),
            comp E L L ι (AlgHom.id (Padic l) L) =
              Functor.isoWhiskerLeft (rationalScalarExtension D l hl E Y L ι) (unit L) ≪≫
                Functor.rightUnitor (rationalScalarExtension D l hl E Y L ι)) := by
  sorry

end WeilConjectures


namespace WeilConjectures

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The sheafified pure tensor in the ordinary finite free scalar extension.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryTensorSection
    (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) (x : N.val.obj U) :
    ((integralOrdinaryScalar l E L ι Y).obj N).val.obj U :=
  (eqToHom ((integralOrdinaryScalarWitness l E L ι Y).choose_spec.choose N).symm).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralCompletedScalarMap l E L ι Y) N).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralCompletedScalarMap l E L ι Y).hom.app U).hom] x))

variable (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

/-- The uniquely normalized ordinary tensor associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the completed ring inclusions compose since all finite quotient projections
agree on the integer inclusions. Send c⊗(b⊗x) to c*j(b)⊗x, and send c⊗x to c⊗(1⊗x)
for the inverse. The balanced relations prove these formulas well defined and mutually
inverse. They commute with restrictions and module maps. Sheafification gives the
natural isomorphism, and local tensor generation proves its uniqueness. -/
theorem integralOrdinaryScalarComp_existsUnique :
    ∃! a : integralOrdinaryScalar l E L ι Y ⋙ integralOrdinaryScalar l L M j Y ≅
        integralOrdinaryScalar l E M (j.comp ι) Y,
      ∀ (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
        (c : (completedIntegralCommRingSheafUnrestricted l M Y).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralOrdinaryTensorSection l L M j Y _ U c
            (integralOrdinaryTensorSection l E L ι Y N U b x)) =
          integralOrdinaryTensorSection l E M (j.comp ι) Y N U
            (c * (integralCompletedScalarMap l L M j Y).hom.app U b) x := by
  sorry

/-- Tensor associativity, fixed on all pure tensor sections.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryScalarComp :
    integralOrdinaryScalar l E L ι Y ⋙ integralOrdinaryScalar l L M j Y ≅
      integralOrdinaryScalar l E M (j.comp ι) Y :=
  (integralOrdinaryScalarComp_existsUnique l E L ι Y M j).exists.choose

/-- The tensor identity comparison is uniquely fixed by multiplication on generators.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the completed identity inclusion is the identity by its projections. Thus the
balanced map s⊗x↦s*x and inverse x↦1⊗x are natural inverse maps. Sheafification and
local generation give the uniquely specified natural isomorphism. -/
theorem integralOrdinaryScalarUnit_existsUnique :
    ∃! a : integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (integralTowerModules.{u, u} l E Y),
      ∀ (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralOrdinaryTensorSection l E E (AlgHom.id (Padic l) E) Y N U s x) = s • x := by
  sorry

/-- The identity tensor comparison.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryScalarUnit :
    integralOrdinaryScalar l E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (integralTowerModules.{u, u} l E Y) :=
  (integralOrdinaryScalarUnit_existsUnique l E Y).exists.choose

/-- The associator induced on the canonical derived localizations.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryDerivedScalarComp :
    integralOrdinaryDerivedScalar l E L ι Y ⋙ integralOrdinaryDerivedScalar l L M j Y ≅
      integralOrdinaryDerivedScalar l E M (j.comp ι) Y :=
  (Functor.mapDerivedCategoryCompIso (integralOrdinaryScalar l E L ι Y)
    (integralOrdinaryScalar l L M j Y)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarComp l E L ι Y M j)

/-- The ordinary derived tensor unit, through the fixed derived localization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralOrdinaryDerivedScalarUnit :
    integralOrdinaryDerivedScalar l E E (AlgHom.id (Padic l) E) Y ≅
      𝟭 (DerivedCategory (integralTowerModules.{u, u} l E Y)) :=
  Functor.mapDerivedCategoryNatIso (integralOrdinaryScalarUnit l E Y) ≪≫
    Functor.mapDerivedCategoryIdIso _

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- Restriction of the fixed derived associator to the full integral subcategories.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: all three functors preserve the stated full subcategories. Their inclusion is
fully faithful, so the ambient derived associator and its inverse lift uniquely. -/
theorem integralConstructibleScalarComp_existsUnique :
    ∃! a : integralConstructibleScalarExtension D l hl E L ι Y ⋙
        integralConstructibleScalarExtension D l hl L M j Y ≅
        integralConstructibleScalarExtension D l hl E M (j.comp ι) Y,
      ∀ K, (a.hom.app K).hom =
        (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj := by
  sorry

/-- The restricted canonical associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralConstructibleScalarComp :=
  (integralConstructibleScalarComp_existsUnique l E L ι Y M j D hl).exists.choose

/-- Restriction of the fixed derived unit to the full integral subcategory.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: the full inclusion uniquely lifts the ambient derived tensor unit and inverse. -/
theorem integralConstructibleScalarUnit_existsUnique :
    ∃! a : integralConstructibleScalarExtension D l hl E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y),
      ∀ K, (a.hom.app K).hom =
        (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj := by
  sorry

/-- The restricted canonical tensor unit.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def integralConstructibleScalarUnit :=
  (integralConstructibleScalarUnit_existsUnique l E Y D hl).exists.choose

/-- The localized associator, uniquely fixed by the integral tensor associator.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: tensor each component and inverse with one. The integral naturality equation
extends to pure rational tensors by scalar compatibility and to sums by additivity.
Inverse equations persist. Equality of hom components determines a natural isomorphism. -/
theorem rationalOrdinaryScalarComp_existsUnique :
    ∃! a : rationalOrdinaryScalarExtension D l hl E Y L ι ⋙
        rationalOrdinaryScalarExtension D l hl L Y M j ≅
        rationalOrdinaryScalarExtension D l hl E Y M (j.comp ι),
      ∀ K, a.hom.app K =
        1 ⊗ₜ (integralConstructibleScalarComp l E L ι Y M j D hl).hom.app K.obj := by
  sorry

/-- The rational scalar associator with the specified integral normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalOrdinaryScalarComp :=
  (rationalOrdinaryScalarComp_existsUnique l E L ι Y M j D hl).exists.choose

/-- The localized unit, uniquely fixed by the integral tensor unit.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: tensor both components of the integral unit with one. Naturality on pure
tensors, additivity and the integral inverse equations give the unique unit isomorphism. -/
theorem rationalOrdinaryScalarUnit_existsUnique :
    ∃! a : rationalOrdinaryScalarExtension D l hl E Y E (AlgHom.id (Padic l) E) ≅
        𝟭 (rationalConstructibleCategory D l hl E Y),
      ∀ K, a.hom.app K =
        1 ⊗ₜ (integralConstructibleScalarUnit l E Y D hl).hom.app K.obj := by
  sorry

/-- The rational scalar unit with the specified integral normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalOrdinaryScalarUnit :=
  (rationalOrdinaryScalarUnit_existsUnique l E Y D hl).exists.choose

/-- Tensor units and associators obey both unit laws and the pentagon.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: first check the ordinary sheaf tensor generators. Both unit maps multiply
1⊗x to x. Both paths around the pentagon multiply the same three coefficients, so
associativity in the largest completed coefficient ring gives equality. Local tensor
generation gives the natural transformation equalities. Canonical derived localization,
full-subcategory restriction, and tensoring Hom maps with one preserve these equations. -/
theorem rationalOrdinaryScalar_coherence :
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalOrdinaryScalarComp l E E (AlgHom.id (Padic l) E) Y L ι D hl).hom.app K =
        (rationalOrdinaryScalarExtension D l hl E Y L ι).map
          ((rationalOrdinaryScalarUnit l E Y D hl).hom.app K)) ∧
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalOrdinaryScalarComp l E L ι Y L (AlgHom.id (Padic l) L) D hl).hom.app K =
        (rationalOrdinaryScalarUnit l L Y D hl).hom.app
          ((rationalOrdinaryScalarExtension D l hl E Y L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : rationalConstructibleCategory D l hl E Y),
      (rationalOrdinaryScalarExtension D l hl M Y N k).map
          ((rationalOrdinaryScalarComp l E L ι Y M j D hl).hom.app K) ≫
        (rationalOrdinaryScalarComp l E M (j.comp ι) Y N k D hl).hom.app K =
      (rationalOrdinaryScalarComp l L M j Y N k D hl).hom.app
          ((rationalOrdinaryScalarExtension D l hl E Y L ι).obj K) ≫
        (rationalOrdinaryScalarComp l E L ι Y N (k.comp j) D hl).hom.app K) := by
  sorry

/-- The canonical associator of the published rational scalar extensions.
It is ordinary balanced tensor associativity conjugated by the normalized quotient
completion comparisons, so it retains the tensor-generator characterization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalConstructibleScalarComp :
    rationalScalarExtension D l hl E Y L ι ⋙ rationalScalarExtension D l hl L Y M j ≅
      rationalScalarExtension D l hl E Y M (j.comp ι) :=
  Functor.isoWhiskerRight (rationalOrdinaryComparison D l hl E Y L ι).symm
      (rationalScalarExtension D l hl L Y M j) ≪≫
    Functor.isoWhiskerLeft (rationalOrdinaryScalarExtension D l hl E Y L ι)
      (rationalOrdinaryComparison D l hl L Y M j).symm ≪≫
    rationalOrdinaryScalarComp l E L ι Y M j D hl ≪≫
    rationalOrdinaryComparison D l hl E Y M (j.comp ι)

/-- The identity-extension comparison, with its actual completeness-unit normalization.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def rationalConstructibleScalarUnit :
    rationalScalarExtension D l hl E Y E (AlgHom.id (Padic l) E) ≅
      𝟭 (rationalConstructibleCategory D l hl E Y) :=
  (rationalOrdinaryComparison D l hl E Y E (AlgHom.id (Padic l) E)).symm ≪≫
    rationalOrdinaryScalarUnit l E Y D hl

/-- Tensor units and associators obey both unit laws and the pentagon.
Source: blueprint order 1469 (blueprint: lem-weil-scalar-extension-composition).
Proof: first check the ordinary sheaf tensor generators. Both unit maps multiply
1⊗x to x. Both paths around the pentagon multiply the same three coefficients, so
associativity in the largest completed coefficient ring gives equality. Local tensor
generation gives the natural transformation equalities. Canonical derived localization,
full-subcategory restriction, and tensoring Hom maps with one preserve these equations.
For the published completed functors, expand the conjugations by the normalized
quotient completion comparisons. Naturality cancels adjacent inverse comparisons,
leaving the same ordinary tensor equation on both sides. -/
theorem rationalConstructibleScalar_coherence :
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalConstructibleScalarComp l E E (AlgHom.id (Padic l) E) Y L ι D hl).hom.app K =
        (rationalScalarExtension D l hl E Y L ι).map
          ((rationalConstructibleScalarUnit l E Y D hl).hom.app K)) ∧
    (∀ K : rationalConstructibleCategory D l hl E Y,
      (rationalConstructibleScalarComp l E L ι Y L (AlgHom.id (Padic l) L) D hl).hom.app K =
        (rationalConstructibleScalarUnit l L Y D hl).hom.app
          ((rationalScalarExtension D l hl E Y L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : rationalConstructibleCategory D l hl E Y),
      (rationalScalarExtension D l hl M Y N k).map
          ((rationalConstructibleScalarComp l E L ι Y M j D hl).hom.app K) ≫
        (rationalConstructibleScalarComp l E M (j.comp ι) Y N k D hl).hom.app K =
      (rationalConstructibleScalarComp l L M j Y N k D hl).hom.app
          ((rationalScalarExtension D l hl E Y L ι).obj K) ≫
        (rationalConstructibleScalarComp l E L ι Y N (k.comp j) D hl).hom.app K) := by
  sorry

end WeilConjectures
