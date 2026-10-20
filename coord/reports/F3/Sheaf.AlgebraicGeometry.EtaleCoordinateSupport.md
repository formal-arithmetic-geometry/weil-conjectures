## What changed

Completed all six original proof holes in
`lean/Sheaf/AlgebraicGeometry/EtaleCoordinateSupport.lean`, preserving every existing
statement, definition, visibility, universe and docstring. Added the proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek` for the existing
closed-support adjunction and support-kernel API.

The support kernel is additive by cancellation of its monic inclusion. Its supported
stalk is additive by composition. Injective preservation follows by comparison with
the existing closed-support adjunction and the exact closed direct image.

Private, fully proved helpers construct support pullback by the kernel universal
property, using the factorization of the inverse-image complement through the original
complement. A supported global section factors through the sheaf-support kernel;
pullback and passage to the geometric stalk then construct its supported germ.
Monicity gives naturality and uniqueness. The same support pullback constructs the
unique supported-stalk restriction.

For the final restriction square, the ordinary germ composition equation follows from
the pullback adjunction units, their composition law, and the stalk colimit equations.
Canceling the supported-stalk inclusion proves composition for supported germs.
The derived square follows by right-derived uniqueness: the normalized base-change
maps satisfy their unit factorization equations, the exact composition comparison
satisfies its localization factorization equation, and unit naturality reduces the
square to the already proved ordinary equation. Every private helper is proved;
there are no new public declarations or auxiliary modules.

The retained complete proof was rechecked against current sources. The two private
kernel-inclusion proofs now use explicitly typed kernel lifts rather than broad
unfolding. All 18 existing public declaration signatures are unchanged. The first
part, including the optimized inclusion proofs, compiled in 11.0 seconds; the
full retained proof also passed a profiling compile in 22.4 seconds. Explicit
arguments to the three final factorization lemmas reduced the final theorem's type checking from 8.26 seconds to 0.44 seconds in the profiling checks;
the resulting complete file compiled in 40.3 seconds with no Lean diagnostics.
The earlier delivery compile with the axiom audit passed server preflight
(review class AUTO); the final packet is checked again before pushing. No
whole-library build was run by this worker.

## Proved and sorry left

Closed six of six original holes (all in node
`def-pur-etale-coordinate-support`):

- `AlgebraicGeometry.Etale.coordinateSupportSheaf_additive`.
- `AlgebraicGeometry.Etale.coordinateSupportedStalk_additive`.
- `AlgebraicGeometry.Etale.coordinateSupportSheaf_preservesInjectives`.
- `AlgebraicGeometry.Etale.coordinateGlobalToStalk_existsUnique`.
- `AlgebraicGeometry.Etale.coordinateStalkRestriction_existsUnique`.
- `AlgebraicGeometry.Etale.coordinateDerivedGlobalToStalk_restriction`.

Sorry left: none. Holes added: zero. Statements split off: zero. The module contains
zero `sorry`s and no definitions contain postponed proofs or arbitrary witness choices.
The existing canonical definitions still choose the unique maps specified by their
now proved existence-and-uniqueness theorems.

## No longer needed

None. No existing imports, nodes or modules are pruned. The proof implements the
existing sheaf-support, normalized-germ and derived restriction route, using the
published kernel, geometric-stalk, adjunction and derived-functor APIs. All original
public imports remain necessary for the existing statements and definitions.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The earlier sandbox report described
only four completed holes; it is superseded by this complete six-hole proof.
Associativity and the definitional identifications between a composite's action on
bounded-below homotopy categories and the successive actions required explicit
factorization equations and carefully placed conversions. No statement or definition
repair was needed. The unit route is unchanged.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
