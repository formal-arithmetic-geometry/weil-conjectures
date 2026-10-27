# Sheaf.Paper.PurityDivisorClass proof context

## Reason

The theorem uses the existing uniquely normalized family, so the family declarations
are placed before it. New proof-only imports provide the smooth Cartier geometry,
ideal multiplication, and the three strict compatibility lemmas. All existing
signatures and attributes remain verbatim. The existing public imports remain;
NormalizedCartierForget becomes a public import because DivisorChern uses its
proved-by-construction logical predicate.
File-local sequential elaboration avoids simultaneous expensive localization
conversions. No exported option, instance, notation, or target meaning changes.
The Chern predicate now applies the generic `divisorChernSpecification` to exactly
its previous hom, ordinary realization, Chern value and comparison. Unfolding the
generic predicate beta-reduces to the previous existential conjunction. No data,
hypothesis or conclusion changes. The helper contains no choice and no proof hole.
The new compatibility theorem and existing definition share this logical predicate,
preventing repeated expansion of the same derived Hom realization during kernel
checking. This is an equivalent definition presentation, not a split of the proof
or the existing module. All target meanings are preserved; no semantic target
review needs reopening.
The category, abelian and derived-category instance wrappers of the supported-Hom
interface are locally reducible, as in their defining module. The underlying
localization construction, single functors and Ext hom equivalence are locally
irreducible. These commands control conversion during elaboration only; they
change no definition body or exported attribute.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

The main theorem appeared before the already proved general-family construction.
The previous Chern definition was:

```lean
/-- Ordinary Kummer normalization and its equality with forgetting the supported
class, through the identical site comparison. Source: blueprint lem-pur-divisor-class,
final paragraph (blueprint: lem-pur-divisor-class). -/
def DivisorChern (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  ∃ (c₁ : Abelian.Ext (P.constantEtale T) (P.frameTwistEtale T 1) 2)
    (α₁ : P.FunctorialCupOrdinaryH false T 2 1),
  HEq c₁.hom α₁ ∧
  HEq (Etale.ordinaryFiniteClass P.Coefficient T (P.frameTwistEtale T 1) 2 c₁.hom)
    (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a)) ∧
  P.functorialCupForget true i 2 1 (P.divisorProEtale i (C.homClassOf i hI)) =
    P.functorialCupOrdinaryCompare T 2 1 α₁

```

## New

```lean
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupHasDerived functorialCupAbelian functorialCupCategory
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Abelian.Ext.homEquiv
  functorialCupOrdinaryCompare functorialCupCompare functorialCupForget
  functorialCupChangeSupport functorialCupPullback

attribute [local irreducible] DivisorChern DivisorLocalEquations DivisorAdditive
```

The three compatibility predicates are locally irreducible during the final proof
and are explicitly unfolded at their uses. The private Chern helper applies the isolated ordinary compatibility directly.

The ordinary Hom and realization maps are named once as
`divisorOrdinaryHom P T := fun c1 ↦ c1.hom` and
`divisorOrdinaryRealization P T := ordinaryFiniteClass ...`. These are the exact
previous functions, with no new choice. The generic predicate uses these names
in both the compatibility theorem and existing definition, preventing repeated
expansion of their identical large structural-instance arguments.

The new logical predicate and its specialization are:

```lean
def divisorChernSpecification {E L : Type*} {H H' : Type vH} {K K' : Type vK}
    (hom : E → H) (ordinary : H → K) (chern : K')
    (supported : L) (compare : H' → L) : Prop :=
  ∃ (c : E) (β : H'), HEq (hom c) β ∧ HEq (ordinary (hom c)) chern ∧
    supported = compare β

def DivisorChern (P : PurityFiniteSetting.{u}) {T D : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (C : P.DivisorEtaleClasses T)
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible) : Prop :=
  divisorChernSpecification
    (P.divisorOrdinaryHom T)
    (P.divisorOrdinaryRealization T)
    (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a))
    (P.functorialCupForget true i 2 1 (P.divisorProEtale i (C.homClassOf i hI)))
    (P.functorialCupOrdinaryCompare T 2 1)
```

The existing proved general-family declarations appear first. The main theorem
and proved private Chern-combination helper then use them. New imports are private.

## Users

`tools/downstream.py Sheaf.Paper.PurityDivisorClass --uses DivisorChern` reports
16 downstream modules; only the item itself directly mentions this declaration.
The item and all downstream modules are listed below. No consumer changes meaning,
and no consumer needs adaptation because the existing signatures and mathematical data are identical; the Chern
predicate unfolds to precisely its previous body. The additive public import exposes
only the new compatibility theorem and generic predicate.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurityDivisorClass | C6 | One hole decomposed; original definitions and signatures retained. |
| Sheaf.Paper.CartierClassAgreement | B7 | No interface or definition change; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | No interface or definition change; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | B5 | No interface or definition change; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | No interface or definition change; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | No interface or definition change; no adaptation. |

## Status

landed 20261025T180532-L-4000619 2026-10-25 (merge of deliver/C6/Sheaf.Paper.PurityDivisorClass)
