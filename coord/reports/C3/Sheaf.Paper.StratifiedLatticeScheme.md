## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.exists_stratifiedLatticeScheme` in
`Sheaf.Paper.StratifiedLatticeScheme`, preserving all existing public declarations,
definitions, hypotheses, universes and conclusions.

The proof identifies reconstructed coefficient rings with continuous coefficient rings.
It proves naturality of the coefficient comparison using the inverse-image adjunction,
and transports lattice pairs along the resulting coefficient square. Naturality of the
module-sheafification unit proves the exact image formula, which transports all three
clauses of the lattice-class presentation. Finite free charts transport along the
coefficient isomorphism, so the existing local classification gives every requested
constant-coset chart.

The representability argument uses the existing size-reduction construction, refines
the supplied cover to a precoverage family, and applies the declared affine presentation,
coproduct fpqc effectivity and representing-sheaf theorems. Composing their representing
bijections with the size-change bijections gives the required natural isomorphism.
Surjectivity of the lattice-class presentation applied to the inverse image of the
identity supplies the universal pair, and the inverse identities prove its equation.
The argument works for rank zero and empty bases without additional hypotheses.

All added helpers are private and proved. All added imports are private proof imports.
Updated the item's node proof, proof dependencies and proof origin to match this assembly.
No other Lean modules or existing public declarations were changed. The preflight
classifies the additional `open scoped ChangeOfRings` and attributes on new private
helpers as interface commands; their precise, private-only effect is recorded in
`coord/changes/stratified-lattice-scheme-private-proof-commands.md`.

Validation: the final lcompile.py run passed with no errors or warnings in 30.0 seconds.
Delivery checks run next. Static comparison confirms
that all seven original definitions and the theorem signature are unchanged, with
zero `sorry` tokens and no lines longer than 100 characters. Development profiling
identified expensive adjunction unfolding; proved private application lemmas and an
irreducible private transport definition reduced the checked file to 48 seconds
without raising limits. All diagnostic settings were removed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratifiedLatticeScheme`.
The item has zero remaining `sorry` occurrences. Added zero holes and split off zero
statements. This is a proof from existing declared dependencies, not a decomposition.

## No longer needed

The proof does not use `lem-sfb-embedded-lattice-coefficient-comparison`
(`Sheaf.Paper.EmbeddedLatticeCoefficientComparison`). It needs only the coefficient
square from that larger result, and proves the square directly by adjunction naturality.
The localization and pair-to-embedded-lattice classification clauses of that node are
unnecessary for the target's already stated pair presentation. The exact image transport
needed here is proved using the existing coefficient-transport construction.
This prunes that dependency from this node only; no library declaration is withdrawn.

Removed these original private imports, whose arguments are supplied by the declared
assembly dependencies or are not used directly:

- `Sheaf.Paper.ContinuousCoefficientRealizations`
- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`
- `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent`
- `WeilConjectures.AlgebraicGeometry.FpqcDescentEtale`
- `WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.CategoryTheory.Sites.Precoverage`

The affine-chart, coproduct effectivity, separatedness, etaleness and fpqc gluing
arguments remain through their declared assembly theorems. The original private
imports of `Sheaf.Paper.PadicIntegersInvertEll` and
`Sheaf.AlgebraicGeometry.WeaklyEtaleStability` are retained because the preflight
classifies them as unit-route imports. No unit step is bypassed,
no source-library declaration is removed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original split asked for a large embedded-lattice coefficient comparison even
though this target is already formulated using lattice pairs. Its stronger localization
and image-bijection conclusions are unnecessary for this statement. The smaller
coefficient square and image-preserving transport suffice. The prescribed affine
coproduct and fpqc descent route is retained.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
