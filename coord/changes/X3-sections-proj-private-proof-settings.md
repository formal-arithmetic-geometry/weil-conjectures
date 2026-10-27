# AlgebraicGeometry.sections_morphism_to_proj_polynomial_ring

## Reason

The complete proof uses private local constructions with section variables, a scoped
namespace opening, and scoped elaborator transparency settings. Static preflight requires
a change record for these commands. The mathematical statement and public imports are
unchanged; this record documents the proof environment rather than a statement repair.

## Old

The theorem's full signature is unchanged byte-for-byte. Its body was `:= by sorry`.
There was no `Construction` section, no section variables, and no `open Scheme.Modules`.
The following existing local instance attribute stays verbatim:

```lean
attribute [local instance] MvPolynomial.gradedAlgebra
```

## New

The new `Construction` section contains:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Scheme.Modules

variable {A : Type u} [CommRing A] {m : ℕ} {Y : Scheme.{u}} {M : Y.Modules}
  (s : Fin (m + 1) → Γ(M, ⊤)) (U : Fin (m + 1) → Y.Opens)
  (hs : ∀ k, IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U k ≤ ⊤)).op (s k)))
  (g : Y ⟶ Spec (.of A))
```

A later section variable is `variable (hU : ⨆ k, U k = ⊤)`. All these commands end at
`end Construction`. Every declaration in that section is private, explicitly constructed
or fully proved, and has no `sorry`. No private helper appears in a public signature or
in the body of a public definition. In particular, the projective morphisms are real
polynomial-evaluation and open-cover gluing constructions, not arbitrary choices from
unproved existence statements.

The original theorem alone receives the same two transparency settings with `in`, so
those settings are declaration-scoped. Its body is now completely proved. No public
signature, definition, instance, notation, attribute, or import changes. The three added
and five removed imports are private proof imports, listed in the report.

## Users

`python3 -B tools/downstream.py Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing
--uses AlgebraicGeometry.sections_morphism_to_proj_polynomial_ring` reports precisely the
two downstream modules below. Neither contains a textual application of the theorem:
both currently import the statement for their still-unfinished arguments. Their statements
continue to see the same public imports and theorem signature. No adaptations are needed.
The claim files for both downstream modules are absent in this checkout, hence both are
unclaimed here. No downstream file is modified by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing` | X3 | Completes its proof with private helpers and scoped commands. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteMapAffineLine` | unclaimed | No signature or import-interface change; no adaptation. |
| `Sheaf.AlgebraicGeometry.Modules.VeryAmpleDisjointUnion` | unclaimed | No signature or import-interface change; no adaptation. |

The existing node updates only its proof route, proof dependencies, proof origin, and
withdraws the obsolete nonvanishing-section `tool_uses` entry. The unit route remains.

## Status

landed 20261023T132334-L-2257095 2026-10-23 (merge of deliver/X3/Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing)
