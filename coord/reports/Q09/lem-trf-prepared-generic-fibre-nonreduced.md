## Worker report

The module `Sheaf.AlgebraicGeometry.PreparedGenericFibreNonreduced` states
`AlgebraicGeometry.prepared_generic_fibre_nonreduced`, with the whole proof `sorry`.
No definitions or helper statements are introduced. The node is unchanged except for
its `lean` record. There are no statement disputes, new nodes, or dependency repairs.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 0577,
`lemma-not-geometrically-reduced-in-neighbourhood`, especially the reduction morphism
and its induced generic-fibre morphism. The node isolates exactly the sentence that
the generic fibre of the unreduced pullback is nonreduced. The existing DAG proof uses
054Z and the 0576 fibre-locus equality to implement the source's geometric-reducedness
comparison. All three proof steps and their dependencies are in the theorem docstring.

Clause-by-clause correspondence:

- Schemes and finite type morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)` with
  `[LocallyOfFiniteType f] [QuasiCompact f]`. Both parts of finite type are retained.
- Irreducible base and its generic point: `[IrreducibleSpace Y] (η : Y)` and
  `hη : IsGenericPoint η Set.univ`. This does not require Y to be reduced or integral.
- Nonempty open subscheme: `(U : Y.Opens)` and `hU : (U : Set Y).Nonempty`.
  Its canonical scheme and inclusion are `U.toScheme` and `U.ι`.
- Integral prepared base with generic point: `(T : Scheme.{u}) [IsIntegral T]`,
  `(ξ : T)` and `hξ : IsGenericPoint ξ Set.univ`.
- Universal homeomorphism: `(q : T ⟶ U.toScheme)` and
  `hq : (topologically IsHomeomorph).universally q`. This quantifies over arbitrary
  pullback squares, not only the underlying map of q.
- The T-to-Y structure map is exactly `q ≫ U.ι`.
- P and h are exactly `pullback f (q ≫ U.ι)` and `pullback.snd f (q ≫ U.ι)`.
  They are written inline, not supplied as arbitrary objects or maps.
- R is P's reduction using `P.nilradical.subscheme`. Its T-structure map is exactly
  `P.nilradical.subschemeι ≫ pullback.snd f (q ≫ U.ι)`.
- Original generic fibre not geometrically reduced over κ(η):
  `hX : ¬ GeometricallyReduced (f.fiberToSpecResidueField η)`.
- Reduced pullback's generic fibre geometrically reduced over κ(ξ): `hR` applies
  `GeometricallyReduced` to the `fiberToSpecResidueField ξ` of R's T-structure map.
  Thus it is the fibre of the reduction, not an independently chosen reduced object.
- Conclusion: `¬ IsReduced ((pullback.snd f (q ≫ U.ι)).fiber ξ)`, exactly the
  nonreducedness of P_ξ as a scheme, with no geometric adjective added.

Dependency declarations read and used, with recorded modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Irreducible`: `IrreducibleSpace`, `irreducibleComponents`.
  The node's whole-space irreducibility uses the former; the latter is relevant to
  the reduction comparison in the proof.
- `Mathlib.Topology.Sober`: `IsGenericPoint` (closure of the singleton equals the set).
- `Mathlib.CategoryTheory.MorphismProperty.Limits`: `MorphismProperty.universally`;
  `Mathlib.AlgebraicGeometry.Morphisms.Constructors`: `topologically`;
  `Mathlib.Topology.Homeomorph.Defs`: `IsHomeomorph`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField` (the second projection to Spec of the residue field).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: the recorded geometric-property
  interface, importing `GeometricallyReduced` from `Geometrically.Reduced`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`, `IsIntegral`, and scheme sobriety.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.nilradical` (defined in
  IdealSheaf.Basic), `Scheme.IdealSheafData.subscheme` and `subschemeι`.
- Proof-only import `Sheaf.AlgebraicGeometry.ReductionGenericFibre`:
  `AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre`.
- Proof-only import `Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange`:
  `AlgebraicGeometry.geometricReduced_fibre_locus_baseChange`.
- Proof-only import `Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest`:
  `AlgebraicGeometry.geometricallyReduced_iff_isReduced_pullback_algebraicClosure`.

All statement dependency nodes were read, including their full statements, lean records
or Mathlib matches; the declarations and docstrings were read in the pinned sources.
All recorded proof modules are imported; no proof import is omitted for a cycle.

Edge cases checked before writing:

- Empty X or empty generic fibre: the empty scheme is geometrically reduced, so the
  hypothesis hX is impossible. No artificial nonemptiness of X or its fibres is added.
- Empty Y or T is excluded by the existing irreducibility/integrality hypotheses;
  U's nonemptiness is explicitly retained.
- U = Y and q the identity are allowed. If no base change is needed, a reduced
  generic fibre whose reduction is geometrically reduced contradicts hX as expected.
- Nonreduced irreducible Y is allowed: T → U may be the reduction. No `[IsReduced Y]`
  hypothesis is introduced, and no reduced-base identification is silently assumed.
- In characteristic p, X = Spec(k[t]/(t^p-a)) for a non-pth-power a and the purely
  inseparable extension adjoining its root gives a nonreduced pullback, with reduced
  reduction. This tests the substantive inseparable case.
- Characteristic zero and perfect fields are not excluded; no separability, flatness,
  noetherianity, or characteristic restriction is added.
- All schemes use the same arbitrary universe u, as in the project's category of
  schemes and canonical pullbacks. There is no independent smaller test-field universe.
  Both autoImplicit and relaxedAutoImplicit are explicitly false.

Searches made (all via the prescribed wrapper with group Q09 and this item):

- `leanfinder`: "If the original generic fibre is not geometrically reduced but after
  a universal homeomorphism the reduction has geometrically reduced generic fibre
  then the pullback generic fibre is not reduced". Eight hits: ring geometric
  reducedness criteria and scheme reducedness/open immersion results; no exact theorem.
- `loogle`: `AlgebraicGeometry.GeometricallyReduced`. Twelve hits: the class, its
  constructor/accessor, base-change stability and reducedness consequences. None is
  the prepared nonreduced generic-fibre implication.
- `grep`: `generic.*reduc|reduc.*generic|reduction.*fiber|fiber.*reduction`, restricted
  to Mathlib/AlgebraicGeometry. Six hits in Geometrically/Reduced, Properties and
  FunctionField; none states the implication. The relevant definitions were read.
- `leansearch`: "The generic fibre after a universal homeomorphism to an integral
  base is nonreduced if its reduction is geometrically reduced but the original
  generic fibre is not geometrically reduced". Eight hits, all ring geometric
  reducedness declarations, with no scheme-level prepared generic-fibre result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: generic/reduced/fibre patterns
  located the recorded reduction comparison and related generic-fibre lemmas.
  The narrower `generic.*fibre.*nonreduced|generic.*fiber.*nonreduced|prepared.*generic`
  found no exact statement. Searching the item id, proposed declaration and proposed
  module in both source roots and `dag/lean_names_upstream.json` found no match.

Validation: the sole delivered module compiles through the required scompile.py wrapper
in both sandbox and actual module contexts, with no diagnostics. The only postponed
proof is the named theorem `AlgebraicGeometry.prepared_generic_fibre_nonreduced`.

## Second reading by Q09

The dispatcher instructs this worker to deliver directly and prohibits starting other
agents; the maintainer supplies the independent review. This section records the
worker's own second pass and does not claim an independent worker reading.

Re-read the node alongside the final signature. Finite type has both required classes;
Y is irreducible but need not be reduced; η and ξ are bound points with whole-space
IsGenericPoint predicates; U is an actual nonempty open; T is integral; q is universally
a homeomorphism. The composite, pullback, second projection and reduction inclusion
are the canonical constructions in every occurrence. hX and hR use the structure maps
of the specified fibres to their residue fields, while the conclusion is ordinary
IsReduced of the unreduced pullback fibre. No clause is missing, no extra hypothesis
or tautological conclusion was added, and no statement correction was needed.
The proof docstring follows all three node proof steps. No mismatch was found.
