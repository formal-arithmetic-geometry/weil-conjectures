/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

public import Sheaf.Paper.NativeProperScalarMateData

/-! # Presentation of the native proper scalar mate

Source: Bhatt--Scholze, Lemma 6.8.2; the formal-properties paragraph of the
current blueprint scalar direct-image proof.
(blueprint: lem-sf-native-proper-scalar-mate-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.PurCompactSupport.properComparison
  AlgebraicGeometry.Scheme.pbcDerivedRestrict
  AlgebraicGeometry.Scheme.reductionDerivedChange
  CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarCondensedComposite

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AlgebraicGeometry.ProEtale

attribute [local instance] nativeScalarModuleClosed nativeScalarModuleSymmetric
  nativeScalarModuleFlatResolution nativeScalarModuleLeftColimits nativeScalarModuleRightColimits
  nativeScalarModuleTensorFour nativeScalarModuleGoodTensorLeft nativeScalarModuleGoodTensorRight
  nativeScalarIntegralExact

/-- Completion, internal/section transport, and scalar transitivity identify the
native scalar mate with the successive integral-to-field and field-to-closure mates.
This is a comparison of arrows for arbitrary morphisms and arbitrary complexes.
Neither properness nor boundedness, nor invertibility of either mate, is assumed.

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; the formal-properties
paragraph of the current blueprint scalar direct-image proof; the presentation/pasting step of
lem-sf-native-proper-scalar-mate-bounded-below-restricted.
(blueprint: lem-sf-native-proper-scalar-mate-presentation).

Proof in words:
1. Use the normalized continuous integral coefficient realization and the inverse
limit of finite quotient projections to identify the completed ring for the size
model Coefficient E with the section ring of the pulled condensed integers of E.
The algebra equivalence Shrink.algEquiv is bicontinuous by finite dimensionality
over the complete base field. Uniqueness of the extending absolute value identifies
the integer rings and their finite quotients, compatibly with the fixed embedding.
Transporting modules along this ring isomorphism and applying the
internal/section equivalence gives e. These additive equivalences are exact.
2. The normalized locally finite coefficient-ring realization identifies the pulled
condensed algebraic-closure ring with the native ring. The internal/section module
equivalence followed by this ring isomorphism gives d, again additive and exact.
3. The completion identification, integral localization inclusion, and finite-field
inclusion compose to a.map: the finite quotient projections give the integral
normalization, the localization fixes the integral inclusion, and the finite-field
normalization fixes the rational inclusion. Thus ha applies to this presentation.
The normalized inverse-image maps agree as well: after taking adjoints they are
precomposition of functions. The direct-image comparisons therefore commute with
the coefficient identifications.
4. Construct these equivalences at every scheme, and transport the scalar
adjunctions and their units and counits through them.
Balanced tensor associativity identifies extension along the composite with the
two successive extensions. Paste the two restriction/direct-image squares and take
their scalar-adjunction mates. Writing L for integral-to-field extension and F
for field-to-closure extension, the mate of the composite restriction square is
F.map of the first mate, followed by the second mate evaluated at L(M), under the
canonical scalar associator. The pasted-mate counit normalization says precisely
that the resulting arrow is properComparison a g. Its source and target comparison
isomorphisms form the asserted isomorphism in the arrow category. All constructions
use ordinary ambient derived categories. No inversion of these two mates is used;
the argument applies to empty schemes, identity morphisms and zero complexes. -/
theorem native_proper_scalar_mate_presentation
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ∃ (e : pbcModules U ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring U) ≌
        Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj l E.1) U))
      (d : Mod (Sheaf (ProEt.topology V) Ab.{u + 1})
          (condensedRingObj (Profinite.padicAlgClRingObj l) V) ≌
        pbcModules V ((nativeCoefficients l).ring V))
      (he : e.functor.Additive) (hd : d.functor.Additive),
      letI := he
      letI := hd
      ∀ M : DerivedCategory (pbcModules U ((PurCompactSupport.completed l
          (Coefficient.{u} l (PadicAlgCl l) E)).ring U)),
        Nonempty (Arrow.mk ((PurCompactSupport.properComparison a g).app M) ≅
          Arrow.mk (d.functor.mapDerivedCategory.map
            (nativeScalarCondensedComposite l E g
              (e.functor.mapDerivedCategory.obj M)))) := by sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
