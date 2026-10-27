# Sheaf.Paper.FiniteProjectiveModelPullback proof scopes

## Reason

Complete the six existing theorem proofs without changing any public signature,
public import, or non-theorem body. The static preflight conservatively flags new
`open`, `universe`, `variable`, and local `attribute` commands as an interface change.
The added commands support proved private adjunction helpers and control unfolding
of the sheafified tensor construction. They install no global instance or global
reducibility attribute. Every original public definition is preserved verbatim.

## Old

The original scope commands, verbatim:

```lean
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FiniteProjectivePullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
```

There was no private `ScalarAdjunction` namespace and no added local reducibility
attribute. The existing public declarations contained six theorem holes.

## New

The original scope commands remain verbatim. The additional scope commands are:

```lean
open scoped TensorProduct ChangeOfRings

attribute [local irreducible] SheafOfModules.changeOfRingsMapOfUniverses

namespace ScalarAdjunction
open SheafOfModules
open scoped TensorProduct ChangeOfRings
universe a b r
variable {D : Type a} [Category.{b} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} [HasSheafify K CommRingCat.{r}]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
```

The namespace ends after its proved private adjunction construction. The generic
variables are scoped to that namespace, and do not enter existing signatures.
The following local attributes occur later at their respective proof boundaries:

```lean
attribute [local irreducible] ordinaryIntegralModulePull ordinaryIntegralDirectRingMap
  SheafOfModules.changeOfRingsOfUniverses SheafOfModules.changeOfRingsHomOfUniverses
  constantSheaf HasDerivedCategory.standard

attribute [local irreducible] limit
attribute [local semireducible] constantSheaf

attribute [local irreducible] constantSheaf

attribute [local irreducible] SheafOfModules.scalarExtensionSection
```

A later performance repair adds proved private wrappers for the already existing
commutative-ring and abelian-group sheafification, weak sheafification, locally
bijective units and commutative-ring forgetful sheaf-composition instances. They
are activated only locally:

```lean
attribute [local instance] proofCommSheafify proofAbSheafify proofAbWeakSheafify
  proofAbLocallyBijective proofCompose
```

The wrappers are theorem proofs of existing propositions. They provide a direct
instance lookup instead of repeating the generic typeclass search profiled in the
first successful compile. They add no hypotheses to a public declaration.

These are local elaboration settings. The semireducible setting permits the scalar
unit calculation before `constantSheaf` is folded again. The private generic
adjunction explicitly receives sheaf-composition compatibility to avoid repeatedly
searching for that structure. The naturality lemmas explicitly bind their site and instance parameters and
name `scalarPerfectExtensionFunctor` in their morphism binders, distinguishing
this universe-aware construction from the older private `tensorFunctor` definitions.
The returned duplicate `proofCommWeakSheafify` wrapper is removed; Mathlib's existing
instance derives weak sheafification from the locally registered full one. Existing global instance attributes and all original options are unchanged.
There are no profiling, trace or debug settings in the delivered file.

## Users

`tools/downstream.py Sheaf.Paper.FiniteProjectiveModelPullback` reports zero Lean
modules downstream in the current shared snapshot. A search of both library roots
finds no occurrence of `FiniteProjectivePullback` outside the item module. The DAG
parent still has an unfinished proof and is preserved; zero current importers is
not used to withdraw any node or module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProjectiveModelPullback | N2 | Six proofs filled; public signatures, imports and definitions unchanged. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | C7 | Future DAG consumer; no existing Lean import or signature is affected. No adaptation. |

No consumer adaptation is needed or delivered. The returned repair compiled in 42.8 seconds; its sole line-length warning was
corrected before delivery. The independent reader can check the public
signatures and definition bodies against the base and the local scope of every
new attribute.

## Status

landed 20261023T231852-L-3653189 2026-10-23 (merge of deliver/N2/Sheaf.Paper.FiniteProjectiveModelPullback)
