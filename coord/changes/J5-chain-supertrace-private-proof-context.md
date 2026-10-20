# Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace private proof context

## Reason

The complete proof of `DerivedCategory.chain_supertrace` uses private finite-frame,
module-duality, chain-duality, and derived-pairing helpers. Their local section variables
and namespace openings are flagged conservatively as interface commands by preflight.
They introduce no exported declarations, instances, notation, or attributes. All seven
original public declarations retain their exact signatures and visibility, and all six
original public definitions retain their original bodies. Both public imports stay
unchanged. No target statement or definition changes.

## Old

The original file has no helper sections or extra namespace openings. Its original
coefficient variables and derived-category variable are:

```lean
variable {A : Type u} [CommRing A]
variable [HasDerivedCategory.{u} (ModuleCat.{u} A)]
```

## New

Those original variable commands are unchanged. The following contexts are added for
proved private helpers only:

```lean
open TensorProduct

section
variable {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ} (ξ : Fin n → Module.Dual A M)
  (m : Fin n → M) (h : ∀ q, ∑ j, ξ j q • m j = q)
include h
-- Fully proved private contraction and triangle lemmas.
end

section
variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]
-- Fully proved private evaluation-transport lemma.
end

open Functor.LaxMonoidal Functor.OplaxMonoidal
```

Two private noncomputable pairing definitions each locally disable only the
`warn.classDefReducibility` warning, preserving their default semireducibility. Explicit
projection lemmas expose their evaluation and coevaluation; the constructions and their
triangle proofs are complete. This avoids expensive instance unfolding. The option is
scoped with `in` to each private definition and is not exported.

The private `chainTraceDualIso` definition is marked `@[irreducible]`. Its fully proved
`chainTraceDualIso_hom_f` and `chainTraceDualIso_inv_f` component lemmas expose the two
computations used by the evaluation and coevaluation formulas. This prevents incidental
unfolding of the chain isomorphism construction, without changing its actual data. The
attribute applies only to a private declaration.

Private abbreviations `chainTraceComplexMonoidal` and `chainTraceDerivedMonoidal` cache
the existing inferred monoidal structures. They are registered using `attribute [local
instance]` only inside the helper sections. Those sections end before either subsequent
public declaration. The theorem proof also installs the abbreviations as local `let`
instances. The original public signatures and the six public definition bodies therefore
contain no private helper. These abbreviations select exactly the original instances;
they do not construct alternative tensor products or coherence maps. A generic proved
private sum lemma and explicit identity-map comparisons avoid expensive simplification
through the full complex and localization structures. No compile or heartbeat limit is
raised. The delivery checks validate compilation and the axiom scan of the final packet.

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace
--uses DerivedCategory.chain_supertrace` reports zero downstream modules and the item
itself as its sole textual declaration user in the current shared source. An independent
import search likewise finds no direct importer. No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace` | J5 | Completes the sole original hole; all public declarations and definitions unchanged. |

## Status

landed 20261020T132017-L-1401820 2026-10-20 (merge of deliver/J5/Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace)
