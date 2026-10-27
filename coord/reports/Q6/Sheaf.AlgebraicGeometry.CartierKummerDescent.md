## What changed

Proved uniqueness of simultaneous Cartier Kummer realizations in
`Sheaf.AlgebraicGeometry.CartierKummerDescent`. The parent theorem now combines
existence with a complete uniqueness proof, without changing its signature.
The proof establishes epimorphy of the supported quotient from the ordinary
open-closed short exact sequence; inverse image preserves that epimorphism.
The quotient normalization therefore fixes the source isomorphism, and
`adicPurityRootComparison_existsUnique` fixes the Tate isomorphism. Cancelling
precomposition by the source isomorphism in Ext and applying function
extensionality identifies the two families.

The new module `Sheaf.AlgebraicGeometry.CartierKummerRealizationExistence`
contains precisely the remaining existence and exponent-independence obligation.
It omits the parent's uniqueness assertion, which is discharged by the delivered
proof, so this is a strict mathematical decomposition. Its docstring and node
record the canonical-class/modulus route and its edge cases. The source-library
boundary, all existing signatures, and all target statements are preserved.

## Proved and sorry left

The original hole in `AlgebraicGeometry.Etale.cartier_kummer_descent` is replaced
by a complete proof from the existence component and the proved private lemma
`realization_unique`. The private lemmas `supported_unit_epi`,
`mapped_supported_unit_epi`, and `ext_precomp_injective` are completely proved.
One hole is added, in `AlgebraicGeometry.Etale.cartier_kummer_realization_exists`
(node `lem-amb-cartier-kummer-realization-existence`). There are zero textual
holes in the item module, one hole closed and one added: net zero, a decomposition,
not a completed proof of existence. No other new hole or data definition is added.
The two delivery modules compiled together successfully with lcompile.py.

The earlier full construction candidate and its isolated source, transition,
and Ext experiments remain only in the sandbox scratchpad. They are not delivered
or counted as proofs. The complete candidate did not pass the full compile limit.
The present delivery preserves the completed uniqueness argument and names the
remaining mathematical component, rather than claiming the candidate is verified.

## No longer needed

No original public import is removed, and no module is withdrawn. The parent
proof directly needs the new existence node, normalized root-comparison uniqueness,
and the ordinary open-closed short exact sequence. Construction-only dependencies
remain attached to the new existence node: the canonical Cartier class and its
source comparison, finite Tate descent, ordinary supported boundary uniqueness,
scalar-map generators, and the Cartier modulus theorem. They are not pruned from
the project.

Exploratory private imports of `CartierReductionModulus`,
`GeoCartierSourceComparison`, `OrdinarySupportedCartierKummer`,
`WeilConjectures.AlgebraicGeometry.Curve.KummerTransition`, and
`SupportedKummerScalarMaps` are absent from the delivered parent because its
uniqueness proof does not use them. The superseded direct DAG dependencies
`lem-cbc-proetale-extension-zero-comparison`,
`lem-sf-proetale-open-closed-sequence`, `def-sf-comparison-derived-pullback`,
`lem-amb-kummer-any-base`, and `sk-lem-geo-cartier` are not directly used by this
route. Their declarations remain available and may still be used transitively.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly described the compile service as disk-full.
The service now runs Lean; that earlier environmental fault is resolved.
The previous zero-textual-hole candidate had not passed a full compile and is
not reported here as a proof. The existing normalized root-comparison uniqueness
and ordinary open-closed sequence suffice to prove the entire uniqueness component.
No statement dispute, definition repair, forced consumer adaptation, or change
to the unit route is involved.

## New nodes

`lem-amb-cartier-kummer-realization-existence` records only existence of a
simultaneous realization, including independence of exponent. Its proof plan
retains the canonical Cartier construction and modulus argument from the parent.
The parent now proves uniqueness itself. The new node has the same chapter and
unit as its parent and a Lean attachment to the new module. No change record is
needed because no existing signature or definition is changed.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
