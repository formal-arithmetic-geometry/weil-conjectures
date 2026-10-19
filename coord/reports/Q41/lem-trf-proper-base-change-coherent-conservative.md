## Worker report

The module `Sheaf.TraceFormula.ProperBaseChangeCoherentConservative` states
`AlgebraicGeometry.OrientedNearbyCycles.proper_baseChange_coherent_conservative`.
It uses Mathlib's `AlgebraicGeometry.IsLocallyNoetherian`, `CompactSpace`,
`LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`, `IsNoetherian`,
`IsProper`, and `Surjective`, the project's `VanishingTopos` and `squareMorphism`,
and the repaired declarations in `CategoryTheory.CoherentToposRepair`.
The repair packages the coproduct and finite-limit structures existentially, avoiding
universe metavariable search for large sheaf categories while preserving the clauses
of `def-trf-coherent-topos`. Its `IsCoherentVanishingTopos`,
`IsCoherentVanishingSquare`, and `IsConservativeVanishingSquare` helpers package the
proof arguments required by the underlying predicates.

The hypotheses are rendered as follows. The Noetherian scheme `S` is
`[IsLocallyNoetherian S] [CompactSpace S]`; the finite-presentation morphism is
`(f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
[QuasiSeparated f]`; and the proper surjective base map is
`(p : T ⟶ S) [IsProper p] [Surjective p]`. No nonemptiness hypothesis is added.

The conclusion clauses are rendered in order:

1. `IsNoetherian T` states that `T` is Noetherian.
2. `LocallyOfFinitePresentation (pullback.snd f p)`, together with
   `QuasiCompact (pullback.snd f p)` and `QuasiSeparated (pullback.snd f p)`, states
   that the base-changed morphism `f_T : X_T ⟶ T` has the finite-presentation
   components recorded by the scheme conventions. `pullback.snd f p` is exactly
   the structure map of `X_T` to `T`.
3. `IsCoherentVanishingTopos f` and
   `IsCoherentVanishingTopos (pullback.snd f p)` state coherence of both vanishing
topoi.
4. `IsCoherentVanishingSquare f (pullback.snd f p) (pullback.fst f p) p
   (pullback.condition (f := f) (g := p))` states coherence of the induced
   morphism `v : V_{f_T} ⟶ V_f`, with existential source and target coherent-topos
   witnesses.
5. `IsConservativeVanishingSquare` with the same square states conservativity.

The dependency declarations read and used were:

- `AlgebraicGeometry.IsLocallyNoetherian` in Mathlib
  `Mathlib.AlgebraicGeometry.Noetherian` (with its affine-cover characterization).
- `CompactSpace` in Mathlib `Mathlib.Topology.Defs.Filter`.
- `AlgebraicGeometry.IsProper` in Mathlib
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `AlgebraicGeometry.Surjective` in Mathlib
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `AlgebraicGeometry.OrientedNearbyCycles.VanishingTopos` and
  `AlgebraicGeometry.OrientedNearbyCycles.squareMorphism` in
  `Sheaf.Paper.OrientedNearbyCycles`.
- The original `CategoryTheory.IsCoherentTopos`,
  `IsCoherentGeometricMorphism`, and `IsConservativeGeometricMorphism` in
  `Sheaf.CategoryTheory.Sites.CoherentTopos`, together with their packaged repair
  declarations in `Sheaf.CategoryTheory.Sites.CoherentToposRepair`.

I checked the identity base change, empty schemes, and vacuous surjectivity over an
empty base: no extra `Nonempty` assumption is needed. I also checked the direction of
`squareMorphism`: with `f' = pullback.snd f p`, `h = pullback.fst f p`, and `g = p`,
its source is `V_{f_T}` and target is `V_f`, matching the coherent and conservative
morphism predicates.

Searches made before writing the module included the required semantic searches and
repository searches. LeanFinder was queried with “A proper surjective base change
induces a coherent conservative geometric morphism on vanishing topoi” and with
“Proper surjective base change gives a coherent conservative geometric morphism
between vanishing topoi”; both returned only unrelated coherent-topology and
base-change declarations. LeanSearch was queried with “Points of a vanishing topos
lift after a proper surjective morphism of the base” and “The base change morphism on
oriented nearby cycle topoi is coherent and reflects isomorphisms when the base map is
proper surjective”; neither returned the required statement. Loogle queries
`"Sheaf", "Conservative"` and `"Conservative", "Sheaf"` returned no hits. Grep of
Mathlib `CategoryTheory/Sites` for `[Cc]onservative|[Cc]oherent` and for
`vanishing.?topos|oriented.?product|coherent.?topos`, plus `rg` over the project's
`WeilConjectures` and `lean/Sheaf`, found no duplicate statement or definition.

The initial `scompile.py` attempts exposed the unusable ambient-coproduct interface
and a geometric-morphism witness-order issue; both were repaired. The final prescribed
compile of the repair module followed by the item module succeeds with no errors or
warnings. No `STATEMENT-DISPUTED` flag is needed.

## Dependency modules

`def-trf-coherent-topos` is copied into the delivery with its `lean` record repaired to
`Sheaf.CategoryTheory.Sites.CoherentToposRepair`. The recorded interface was unusable
for this consumer because its ambient `HasCoproducts` universe is an unresolved large
typeclass search on `VanishingTopos`; additionally, its geometric-morphism predicates
require coherent-topos proof arguments. The repair packages coproduct and finite-limit
structures and those proof arguments existentially, and supplies the three vanishing
square helper predicates used by the item. The original node statement and all item
hypotheses and conclusions are otherwise unchanged.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
