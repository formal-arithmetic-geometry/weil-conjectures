# Canonical integral restriction interface extraction

## Reason

The assigned theorem depends on AugmentedIntegralDescent, which imported the assigned
module solely for its restriction definitions. This reverse import prevents using the
stated dependency. Extract the existing interface into ClopenIntegralRestriction and
publicly re-export it from the assigned module. Prove its coefficient comparison and
exactness without using the augmented descent theorem. All theorem names, visibility and non-proof definition bodies are preserved. The ordinary
functor is renamed as explained below to distinguish it from a different derived functor.

## Old

The following block was in Sheaf.Paper.ClopenRoosIntegralDescent:

```lean
/-- The scheme site has its native small model.
Source: the definition of the small pro-étale site
(blueprint: lem-pur-clopen-roos-integral-descent). -/
instance (priority := 4000) clopenIntegralSiteSmall (Y : Scheme.{u}) :
    EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{u} _

/-- Restriction of a constant ring is normalized by the constant presheaf unit.
Source: Stacks 00XZ and 03CO (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenConstantMap {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (A : CommRingCat.{u + 1}) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).obj A ⟶
      clopenRingRestriction j
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv _ _).symm
      (Functor.whiskerLeft (clopenSiteInclusion j).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed coefficient comparison is uniquely fixed by every quotient projection.
Source: Stacks 03CO, 08TC; Bhatt--Scholze 3.5.2
(blueprint: lem-pur-clopen-roos-integral-descent).
Proof: restriction is precomposition, hence preserves sectionwise inverse limits.
The constant-sheaf unit maps are isomorphisms after localization at the open.
Their naturality in quotient reduction gives a cone; its unique limit lift is f.
The inverse limit of the inverse finite comparisons is its inverse. Jointly monic
limit projections give uniqueness, including on the empty scheme. -/
theorem clopenCompletionMap_existsUnique {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    ∃! f : completedIntegralCommRingSheafUnrestricted l E Y ⟶
        clopenRingRestriction j (completedIntegralCommRingSheafUnrestricted l E X),
      IsIso f ∧ ∀ n : ℕ,
        f ≫ ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (completedIntegralCommRingProjectionUnrestricted l E X n) =
          completedIntegralCommRingProjectionUnrestricted l E Y n ≫
            clopenConstantMap j (CommRingCat.of
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  sorry

/-- The limit lift of the normalized finite coefficient comparisons.
Source: Stacks 03CO (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenCompletionMap {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :=
  (clopenCompletionMap_existsUnique l E j).exists.choose

/-- Invertibility follows from the uniquely specified limit comparison.
Source: Stacks 03CO (blueprint: lem-pur-clopen-roos-integral-descent). -/
instance clopenCompletionMapIsIso {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    IsIso (clopenCompletionMap l E j) :=
  (clopenCompletionMap_existsUnique l E j).exists.choose_spec.1

/-- Ordinary module restriction with the canonical completed coefficient transport.
Source: Stacks 04TS and 03CO (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenIntegralRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
  clopenRestriction j (completedIntegralCommRingSheafUnrestricted l E X) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (clopenCompletionMap l E j))

/-- Restriction and the isomorphic scalar transport are additive and exact.
Source: Stacks 04TS (blueprint: lem-pur-clopen-roos-integral-descent).
Proof: restriction is exact on the localized pro-etale site, and scalar transport
along a ring isomorphism is an additive equivalence. Compose these exact functors. -/
theorem clopenIntegralRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenIntegralRestriction l E j).Additive ∧
      PreservesFiniteLimits (clopenIntegralRestriction l E j) ∧
      PreservesFiniteColimits (clopenIntegralRestriction l E j) := by
  sorry

/-- Additivity extracted from exactness. Source: Stacks 04TS
(blueprint: lem-pur-clopen-roos-integral-descent). -/
instance clopenIntegralRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : (clopenIntegralRestriction l E j).Additive :=
  (clopenIntegralRestriction_exact l E j).1

/-- Left exactness extracted from exactness. Source: Stacks 04TS
(blueprint: lem-pur-clopen-roos-integral-descent). -/
instance clopenIntegralRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (clopenIntegralRestriction l E j) :=
  (clopenIntegralRestriction_exact l E j).2.1

/-- Right exactness extracted from exactness. Source: Stacks 04TS
(blueprint: lem-pur-clopen-roos-integral-descent). -/
instance clopenIntegralRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (clopenIntegralRestriction l E j) :=
  (clopenIntegralRestriction_exact l E j).2.2

/-- Unbounded ordinary restriction, descended degreewise through quasi-isomorphisms.
Source: Stacks 015F (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenIntegralDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] := (clopenIntegralRestriction l E j).mapDerivedCategory

/-- The canonical shift comparison of exact derived restriction. Source: Stacks 015F
(blueprint: lem-pur-clopen-roos-integral-descent). -/
instance clopenIntegralDerivedRestrictionShift {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] : (clopenIntegralDerivedRestriction l E j).CommShift ℤ :=
  inferInstanceAs ((clopenIntegralRestriction l E j).mapDerivedCategory.CommShift ℤ)

/-- Degreewise exact restriction on ordinary cochain complexes. Source: Stacks 015F
(blueprint: lem-pur-clopen-roos-integral-descent). -/
abbrev clopenIntegralComplexRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  (clopenIntegralRestriction l E j).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restrict strict towers degreewise, including their transition maps and strict maps.
Source: Stacks 08TC (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenIntegralStrictRestriction {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (clopenIntegralRestriction l E j)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Restriction on the other standard encoding of strict towers of complexes.
Source: Stacks 08TC (blueprint: lem-pur-clopen-roos-integral-descent). -/
abbrev clopenIntegralComplexTowers {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (clopenIntegralComplexRestriction l E j)

/-- The actual strict reduction tower, functorial in its input complex.
Source: Bhatt--Scholze 3.5.2 (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenStrictReductionFunctor (X : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E X n)
    (unrestrictedIntegralTransition l E X)).flip

/-- The actual derived reduction tower, functorial in all derived morphisms.
Source: Bhatt--Scholze 3.5.2 (blueprint: lem-pur-clopen-roos-integral-descent). -/
def clopenDerivedReductionFunctor (X : Scheme.{u}) :=
  (Functor.ofOpSequence (X := fun n ↦ sfDerivedReductionRestricted l E X n)
    (sfDerivedReductionTransition l E X)).flip

```

## New

The declarations are in Sheaf.Paper.ClopenIntegralRestriction, publicly imported by
Sheaf.Paper.ClopenRoosIntegralDescent. Only the proofs of
clopenCompletionMap_existsUnique and clopenIntegralRestriction_exact are filled.
The former is the inverse-limit comparison, uniquely normalized on quotient projections;
the latter composes exact open restriction with an additive scalar equivalence.
AugmentedIntegralDescent now publicly imports ClopenIntegralRestriction instead of its
consumer. The six ordinary-functor references in that consumer are renamed; all other lines stay unchanged.
The ordinary clopenIntegralRestriction is renamed clopenIntegralModuleRestriction in this
interface and both ordinary consumers. Its body and arguments stay identical. The declaration
with the old name in ClopenStrictSystemComparison remains unchanged: it is a completed
constructible derived pullback, taking P : PurityFiniteSetting and j : Xi ⟶ X over P.field.k.
The renamed functor takes l : ℕ and an open immersion of arbitrary schemes and operates
on ordinary module sheaves. Their domains, codomains and mathematical constructions differ.
This is precisely the exception allowed in the return of 265e2b9d020.
No target signature or mathematical definition changes.

The renamed signature is:

```lean
def clopenIntegralModuleRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    scalarReductionSource l E X ⥤ scalarReductionSource l E Y :=
  clopenRestriction j (completedIntegralCommRingSheafUnrestricted l E X) ⋙
    SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (clopenCompletionMap l E j))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ClopenRoosIntegralDescent | C3 | Re-exports the interface; uses renamed ordinary functor. |
| Sheaf.Paper.AugmentedIntegralDescent | unclaimed (previously T5) | Imports interface; six name substitutions. |

`tools/downstream.py Sheaf.Paper.ClopenRoosIntegralDescent --uses clopenIntegralRestriction`
returned exactly the two modules above (the consumer has six uses).
A textual scan of both Lean roots distinguishes the ordinary calls from the constructible
derived calls using their argument types. Only these two modules use the ordinary definition.
The other clopenIntegralRestriction is in the SAME namespace, defined by
ClopenStrictSystemComparison; its constructible derived categories and completed pullback
make it a different operation. The earlier namespace claim was wrong. Its consumers
ClopenExceptionalScalarDescent and FiniteClopenExceptionalRestriction keep using it.
Both ordinary consumers are adapted in this delivery; the derived consumers retain the
original public declaration in ClopenStrictSystemComparison.

The original consumer import would close the cycle
`ClopenRoosIntegralDescent → AugmentedIntegralDescent → ClopenRoosIntegralDescent`.
Changing its first public import and its six references to the renamed ordinary functor
repairs the dependency and the interface name.
The delivery preserves the current shared consumer, including the proofs landed during this
session, and changes only its first public import and those six functor references. No target meaning changes.

## Status

landed 20261025T201537-L-2571216 2026-10-25 (merge of deliver/C3/Sheaf.Paper.ClopenRoosIntegralDescent)
