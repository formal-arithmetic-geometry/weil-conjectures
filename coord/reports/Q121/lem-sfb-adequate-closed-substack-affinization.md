## Worker report

The module `Sheaf.AlgebraicGeometry.AdequateClosedSubstackAffinization` states
`CategoryTheory.adequate_closed_substack_affinization`, with one `sorry` and no new
definitions. The item statement, proof and proof dependencies are unchanged. Its
statement dependencies gain the two already landed owning definitions
`def-sfb-space-closed-subspace` and `def-sfb-space-module-structure-map`. Their
modules are public imports. `lem-sfb-space-closed-ideal-correspondence` stays in
proof_deps and is a plain proof import, not a statement dependency.

Source checked: Alper, *Adequate moduli spaces and geometrically reductive group
schemes*, published primary PDF
https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf, Lemma 5.2.11, printed
p.510 (PDF page 22), including its final assertion and proof. The source states the
relative-Spec adequate moduli morphism and the adequate homeomorphism to the
scheme-theoretic image. The node requests the underlying universal homeomorphism;
no extra characteristic-zero or integrality clause is imposed.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. Both stacks are actual based categories
  over `Over (Spec (.of k))`, with separate total-category universes `v,w,v',w'`.
  `hX` and `hZ` assert `IsAlgebraicModuliStack`.
- `Y : AlgebraicSpace (Spec (.of k))` is precisely the existing sheaf-based
  algebraic space over k. `φ` is a based functor to its discrete fibred category.
  `hφ : IsAdequateModuliSpace X hX Y φ` includes quasi-compactness,
  quasi-separatedness, the canonical structure-sheaf isomorphism, and the power
  lifting requirement on all algebras on every affine etale base change.
- `i : BasedFunctor Z X` and `hi : ModuliSchemeTest @IsClosedImmersion i` mean an
  algebraic closed immersion, using the same scheme-test predicate as the
  recorded closed-immersion-calculus module. `j` is written explicitly as
  `i.comp φ` throughout, with no alternate morphism parameter.
- `B : Y.QCAlg` asserts the quasi-coherent O_Y-algebra conclusion. The ring
  equivalences `β V` identify its values with the actual
  `moduliDirectImage hZ.1.1 Y (i.comp φ) (moduliStructureSheaf Z hZ.1.1)`.
  The first conjunct makes these equivalences natural in every etale-site arrow;
  the second sends the algebra structure map to `moduliStructureMapApp`.
  Thus this is the same direct-image algebra, with all restrictions, ring
  operations and structural maps, in the small universe used by relative Spec.
  There is no site-universe equality, extra smallness hypothesis, or arbitrary
  chosen map. Existence of a small presentation is part of the conclusion.
- For every `C : RelativeSpecData Y`, `E` is exactly
  `(C.relativeSpec B).obj.left`, and its projection to Y is
  `(C.relativeSpec B).obj.hom`. This uses the dependency's inverse
  anti-equivalence and counit, without a new relative-Spec construction or a
  hypothesis selecting a special algebra.
- `W : ClosedSubspace Y` is an actual closed subspace, retaining its scheme
  structure. For every etale chart V and regular function r, the kernel clause
  states that `moduleStructureMap W.val.arrow` kills r exactly when the unit
  map of B kills r. The ideal of a closed subspace is the kernel of that
  structure map by the closed-ideal correspondence used in the proof. This identifies
  it with `ker(O_Y -> B)` as a sheaf ideal, including nilpotents, rather than
  identifying only its zero locus or radical. Quasi-coherence is supplied by
  the same correspondence for a closed subspace.
- `b` maps Z to E, `e` maps E to W, and the based isomorphism `h` identifies j
  with b followed by E -> Y. The equation `e ≫ W.val.arrow = ...` gives the
  remaining factorization. `IsAdequateModuliSpace Z hZ ... b` is the full
  adequacy conclusion for b, using the recorded predicate.
- The chart-evaluation conjunct specifies b canonically. Given V, a chart q
  of E over V, and any source object z mapping to q, the value of `β V s`
  on the corresponding comma object of j is the pullback of the counit
  section on q along the actual scheme map
  `moduliChartSchemeMap ... z`. The comma arrow uses `h` and the actual
  functor induced by E -> Y. This fixes the evaluation map on all objects,
  rather than allowing an arbitrary adequate map over Y. `.down` only
  removes the structure-sheaf's canonical ULift.
- The next conjunct says that any closed subspace D through which j factors
  contains W: `W.val ≤ D.val`. The factorization into W was already provided
  by b and e. This is precisely the equivalent scheme-theoretic-image clause,
  using subobject order, not merely topological containment.
- The last clause quantifies over every algebraic space `W'` over k and every
  `f : W' ⟶ W`. Its source point space is the actual `moduliTwoFiberProduct`
  of e and f, with the dependency's `moduliSmoothPointTopology`. It produces
  a `Homeomorph` equal pointwise to `moduliPointMap (moduliTwoFiberSnd ...)`.
  Hence it asserts the canonical projection is a homeomorphism after every
  algebraic-space base change, not just that the spaces are homeomorphic.
- No reducedness, finite type, Noetherian, inertia, or characteristic binder
  occurs. All universes are explicitly declared; auto-implicit variables are off.

Dependency declarations used (all source signatures and relevant docstrings read):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`:
  `CategoryTheory.IsAdequateModuliSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `EtaleSite`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `moduliDirectImage`, `moduliStructureSheaf`, `moduliStructureMapApp`,
  `ModuliPushforwardIndex`, `moduliChartSchemeMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`:
  `RelativeSpecData`, `RelativeSpecData.relativeSpec`, `counitAlgebra`,
  `StructureAlgebraModel.projection`; its public algebra dependency supplies
  `QCAlg`, `CommAlgebraSheaf`, `commStructureSheaf`.
- `Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets`:
  `moduliSmoothPointTopology`, with the existing `ModuliPoints`,
  `moduliPointMap`, actual 2-fibre products and projections.
- `Sheaf.AlgebraicGeometry.StackClosedImmersionCalculus`:
  its `ModuliSchemeTest @IsClosedImmersion` interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace`:
  `AlgebraicGeometry.AlgebraicSpace.ClosedSubspace` (owning definition node
  `def-sfb-space-closed-subspace`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap`:
  `AlgebraicGeometry.AlgebraicSpace.moduleStructureMap` (owning definition node
  `def-sfb-space-module-structure-map`).
- As a proof dependency,
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealCorrespondence`:
  `closed_ideal_correspondence`, for its kernel-ideal characterization.

Recorded proof dependencies already stated are imported: the shared stack-algebra,
relative-Spec and point-topology modules publicly; the owning closed-subspace and
structure-map definition modules publicly; closed-ideal correspondence, affine-chart
calculus and `Mathlib.RingTheory.RingHom.Flat` as plain proof imports. The remaining proof
nodes have neither a Lean record nor a Mathlib match at this reading, so no
nonexistent module is imported. None is needed to form the statement.

Edge cases checked before writing and on rereading:

- Empty Z gives the zero algebra, empty E and empty W. Empty source/test point
  spaces and the homeomorphism of empty spaces remain permitted.
- Z = X gives the full image and the original adequate moduli map. The zero
  kernel and the full closed subspace are allowed.
- For identity adequate moduli on a scheme, an arbitrary nonreduced closed
  subscheme gives its actual quotient algebra and ideal. The kernel equality
  preserves nonradical ideals; the statement does not reduce W.
- In positive characteristic the map E -> W need not be an isomorphism. The
  theorem asks only for homeomorphism after base change, and puts no bound on
  lifting powers. Characteristic zero is included too.
- Arbitrary nonflat W' -> W are quantified over; the identity test is included.
- Independent total-category universes are preserved through the sectionwise
  ring equivalences, including large equivalent stack presentations.

Searches for existing statements and notions:

- `msearch.py leanfinder`, query "A closed substack of an adequate moduli space
  has adequate affinization universally homeomorphic to its scheme theoretic
  image": eight scheme-level affine/closed-immersion hits, no adequate stack
  result.
- `msearch.py loogle`, query `IsAdequateModuliSpace, moduliDirectImage`: zero
  hits; these are project declarations, not Mathlib declarations.
- `msearch.py grep`, query `adequateModuli|adequate_moduli|adequatelyAffine`
  in Mathlib AlgebraicGeometry: zero hits.
- `msearch.py leansearch`, query "closed substack adequate moduli space relative
  spectrum universal homeomorphism": eight hits about scheme closed subschemes,
  universal closedness and properness; no matching theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index for
  the item id, `adequate_closed_substack_affinization`, adequate/closed and
  adequate-moduli patterns: no existing declaration of this statement. Source
  searches of algebra, relative-Spec, closed-ideal and point-topology modules
  found the interfaces above, which are reused.

No statement dispute or source correction. No new nodes or dependency repairs.
The node's only changes are its Lean record and the additional landed statement
dependencies. All writes are confined to this sandbox and authorized wrappers.

Validation after repair: prescribed `scompile.py` passed both sandbox module mode
(13.2 s) and library module mode (5.1 s), with no errors or unexpected warnings.
The repaired delivery is also checked by the prescribed delivery dry run.

## Second reading by Q121

Author's second reading, with the original node and final module open; independent
maintainer review follows delivery. The two algebraic stacks, field, algebraic
space, adequate morphism and closed immersion match the hypotheses individually.
The two β equations are essential: a bare family of ring equivalences would lose
restriction and structural-map compatibility. The evaluation formula also prevents
an automorphism of E over Y from changing the meaning of the canonical b. The
closed image is fixed by equality of sheaf kernels, and its minimality clause is
in scheme-structured subobject order. The final Homeomorph is explicitly the
second-projection point map on the actual 2-fibre product; it covers every W',
including empty and nonflat tests. No additional mathematical hypothesis was
introduced. No mismatch found in this second reading; the statement was not
corrected. The public imports and stmt_deps name the two owning definition nodes; the
closed-ideal-correspondence theorem is retained only as a proof dependency.


## Repair of returned delivery 5a95e9e11d33

The maintainer identified one H2 theorem-stmt_dep fault: the theorem
`lem-sfb-space-closed-ideal-correspondence` was added to stmt_deps even though
the signature uses only `ClosedSubspace` and `moduleStructureMap`, which have
their own definition nodes. Read both owning nodes and the full declaration
signatures and docstrings in their modules. Replaced that statement dependency
with `def-sfb-space-closed-subspace` and `def-sfb-space-module-structure-map`.
Replaced its public import by the two owning modules as public imports; retained
`AlgebraicSpaceClosedIdealCorrespondence` as a plain import and kept the theorem
in proof_deps. Updated lean.note and all affected report passages.

Compared the retained delivery with current main before editing: only lean and
stmt_deps differed. Reconstructed the node from current main, preserving all other
fields, and applied the repaired Lean record and these two definition dependencies.
The theorem signature and body are byte-identical to the returned version. The
wrapper performs the authorized current-base refresh and delivery bookkeeping.

Second reading of the repair: the statement's W binder uses exactly ClosedSubspace
from AlgebraicSpaceClosedSubspace, and the sectionwise kernel clause uses exactly
moduleStructureMap from AlgebraicSpaceModuleStructureMap. No witness constructed
by closed_ideal_correspondence occurs in the signature. Its proof use is retained
in docstring step 2 and as a plain import. This addresses the complete return;
the mathematical statement and its hypotheses are unchanged.
