# CategoryTheory.directImageRoosNormalization

## Reason

The main theorem is proved without changing any existing public declaration,
definition body or signature. Static preflight classifies the added `variable`,
`open`, `section`, `omit` and local `attribute` commands as a visible-command
change and requires this record. They support private proofs only. There is no
statement or definition repair, no altered target meaning, and no consumer
adaptation. No statement review is reopened by these proof-support commands.

The extra universe is used by generic Grothendieck/K-injective helpers. The extra
open namespace resolves triangle constructors in private proofs. The additional
countable-products variable is needed only after the two existing public product
definitions, in the private direct-image calculations. Local instances of the
existing countable-limit proofs avoid repeatedly constructing equivalent product
instances while elaborating. These caches are confined to `PrivateComparisons`,
`PrivateTriangles` and `PrivateSquares`, which contain only private declarations.
The final theorem also caches these instances locally in its proof. The
elaboration option is scoped to its proof rather than its statement. Their result
is `HasLimitsOfShape`, a proposition; they change no chosen data.
All helpers and cache theorems are proved. Four private isomorphism constructions
(`roosSignComponent`, `normalizedProductComparison`, `additiveRoosIso` and
`directIsoCanonical`) are irreducible; their proved equation lemmas provide the
needed computations without repeatedly unfolding their complete constructions.
Their bodies are unchanged by this elaboration optimization.

The private import of
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` is retained because
it realizes a step of the unit route. The supplied `DirectImageData` carries its
normalized comparison, and the proof uses exactly that comparison and its unit
normalization. No unit is bypassed.

## Old

The original module-level support commands, verbatim:

```lean
set_option autoImplicit false

universe u v w uA vA uB vB

open CategoryTheory CategoryTheory.Limits Opposite
```

After `productMap`, the original module has no further countable-products
variable and no private proof sections: its theorem ends with `:= by sorry`.
The six public definitions/structures and the main theorem statement remain
verbatim; only the theorem proof is replaced.

## New

The corresponding commands, verbatim:

```lean
set_option autoImplicit false

universe u v w uA vA uB vB g

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
```

The additional variable occurs after the existing public `productMap`:

```lean
variable [HasCountableProducts B]
```

The private proof sections scope the elaboration option and finite-biproduct
instance locally (the main theorem also has a scoped elaboration option):

```lean
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Abelian.hasFiniteBiproducts
```

The three private comparison/triangle/square sections additionally use:

```lean
attribute [local instance 1050] nat_products
attribute [local instance 1100] cochain_nat_products
```

The new `omit` commands remove unused parameters only from private theorems.
No new public declaration, public import, notation, instance or simp attribute is
introduced. The file, including the retained unit-route import, compiled with
the unmodified delivery axiom probe using `lcompile.py` in 50.8 s. The probe checked
81 declarations and reported no forbidden axioms; delivery rechecks the packet.

## Users

`tools/downstream.py Sheaf.CategoryTheory.DirectImageRoosNormalization --uses
 directImageRoosNormalization LimitData DirectImageData ordinaryInclusion
 RoosTriangleData alpha productMap` reports zero downstream Lean modules and
only the item itself among the name hits. All six original public structures and
definitions were compared with the current shared source and are textually
identical. The main theorem's signature was also compared and is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.DirectImageRoosNormalization` | J4 | Original hole proved; public interface unchanged. |
| `Sheaf.Paper.CompletedDirectImageLimits` | N3 | DAG consumer with unfinished proof, not a current Lean importer; unchanged interface remains available, no adaptation. |

No other module is delivered or adapted. No target statement or definition used
by a target changes.

## Status

landed 20261021T101146-L-18525 2026-10-21 (merge of deliver/J4/Sheaf.CategoryTheory.DirectImageRoosNormalization)
