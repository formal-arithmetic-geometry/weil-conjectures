## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeFppfDescent` states
`AlgebraicGeometry.finiteLocallyFree_fppf_descent`. Its proof is `sorry`, as required
in stage 2; no definitions or proofs are added. The statement is the conjunction
of pullback stability, effective descent with fixed degree, and unique descent of
isomorphisms. Together these give exactly the fppf stack assertion in the node.

Clause-by-clause correspondence:

- The scheme `S` is `S : Scheme.{u}`. An arbitrary S-scheme is `T : Over S`;
  all local schemes acquire their S-structure by composition with `T.hom`.
  The explicit universe `u` is the universe of schemes in the size convention;
  the family index lies in `Type (u + 1)`, matching the existing descent interface
  and the larger chosen universe, with no finiteness or nonemptiness assumption.
- The nonnegative integer degree is `d : ℕ`, including zero.
- An object of the node's groupoid is `Z : Over T.left` with
  `Z.hom.IsFiniteLocallyFreeOfDegree d`; its arrows are `Z ≅ W` in the slice.
  This uses the recorded definition directly, rather than defining another
  finite locally free predicate or another carrier for the same groupoid.
- The first conjunct quantifies over every such `Z` and every `g : T' ⟶ T.left`,
  and asserts `(pullback.snd Z.hom g).IsFiniteLocallyFreeOfDegree d`.
  This is preservation of objects by the actual scheme fibre product.
  Preservation of arrows is supplied by `(Over.pullback g).mapIso`, which appears
  explicitly in the last clause. The already defined `Over.pullback` is a functor;
  `Over.pullbackId` and `Over.pullbackComp` give its canonical comparisons. No
  arbitrary base-change map or assumed comparison replaces the construction.
- For every covering family, the second conjunct quantifies over `I`, `U`, `f` and
  assumes `Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T.left`. This is precisely
  flatness, local finite presentation, and joint surjectivity; there is no
  quasi-compactness or surjectivity requirement on individual members.
- The given `Z_i/T_i` and overlap isomorphisms with cocycle are represented by
  `D : SchemeCoverDescentDatum f`. Here `D.localScheme i` is `Z_i/T_i`,
  `D.data.hom` is the transition on all test overlaps, `D.data.hom_comp` is the
  cocycle, and `D.representation` gives the actual local represented schemes.
  The generic descent-data transitions are isomorphisms (`DescentData.iso`).
  Yoneda identifies this existing encoding with the node's scheme overlap maps.
  Its identity normalization follows from the invertible cocycle and imposes no
  extra hypothesis. `∀ i, (D.localScheme i).hom.IsFiniteLocallyFreeOfDegree d`
  asserts precisely that each given local object belongs to the degree-d groupoid.
- The existential `Z : Over T.left` and `Z.hom.IsFiniteLocallyFreeOfDegree d`
  give the global object of the SAME degree. The maps `q i` and the assertions
  `IsPullback (q i) (D.localScheme i).hom Z.hom (f i)` give isomorphisms from
  each `Z_i` to the fibre product `Z ×_T T_i` (equivalently their inverses in the
  node's displayed direction). The following equality on every test point says
  transition from i to j preserves its image under `q`; this is precisely that
  these isomorphisms induce the specified overlap isomorphisms. This formula is
  the existing `SchemeCoverDescentDatum.IsEffective` formula with the realizing
  object retained so its degree can be asserted. Bare effectivity alone would
  not retain that assertion, so it has not been substituted for this clause.
- The last conjunct quantifies over two global objects `Z`, `W`, with both
  degree-d hypotheses, and an isomorphism `e i` between their canonical pullbacks
  in `Over (U i)`. Pairwise compatibility is stated on
  `(Z ×_T U_i) ×_Z (Z ×_T U_j)` by equality of the composites into `W`.
  This is the usual overlap `Z ×_T (U_i ×_T U_j)`. Both maps have the same
  base coordinates, so equality into `W` is equivalent, by the fibre-product
  universal property, to the full canonical overlap compatibility of `e i`
  and `e j`. Thus the hypothesis neither strengthens nor weakens compatibility.
- `∃! b : Z ≅ W, ∀ i, (Over.pullback (f i)).mapIso b = e i` is exactly existence
  and uniqueness of the global T-isomorphism inducing the prescribed local ones.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (actual structure and morphism signatures read).
- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  explicit `universe u`, `Scheme.{u}`, and `Type (u + 1)` implement it here.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` and `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
  The latter extends the former and requires `fiberDegree s = d` at every point,
  and the former extends finite, flat and locally of finite presentation.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the fibre-product universal property.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`. The precoverage definition and documentation were read.
- Added the already landed node `def-trf-scheme-cover-descent-datum` to stmt_deps,
  using `Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum`:
  `SchemeCoverDescentDatum` and its geometric `IsEffective` formula. Both their
  signatures and full docstrings were read. No existing node is restated.
- `Mathlib.CategoryTheory.Comma.Over.Pullback`: `Over.pullback`, `Over.pullbackId`,
  `Over.pullbackComp`; all relevant definitions and docstrings were read.

Proof imports include the recorded family-coproduct encoding, affine fpqc
object descent, descent of finite/flat/locally finitely presented morphisms,
and Mathlib permanence, rank, coproducts and representable descent. The docstring
follows every one of the node's seven proof steps and names the nodes they use.
No import cycle is introduced. Statement dependencies use public imports;
proof-only imports are plain imports.

Sources checked directly: `literature/stacks-project/descent.tex`,
`lemma-affine` (Tag 0245), `lemma-descending-property-finite-locally-free`
(Tag 02VO), and `lemma-fpqc-universal-effective-epimorphisms` (Tag 023Q).
These prove affine effectivity, degree-preserving fpqc locality, and unique
representable descent respectively, exactly as the node uses them.

Edge cases checked before writing:

- `d = 0`: allowed with no positivity/surjectivity assumption on local covers;
  the empty finite cover of a nonempty base is included.
- Empty index: no `Nonempty I` is required. Joint surjectivity forces `T` empty,
  and a scheme mapping to it is empty; existence and uniqueness still hold.
- Empty covering members: no individual member is required to be nonempty.
- Infinite covering index and non-quasi-compact base: no finite-index,
  `Small.{u} I`, coproduct existence, or compactness hypothesis is imposed.
- Empty base and arbitrary degree: the pointwise fibre-degree condition is
  vacuous, consistently with the existing degree definition.
- Identity cover and the same global object on both sides: the displayed
  compatibility is satisfied by the canonical pullbacks of its identity, and
  uniqueness retains possible automorphisms through the specified local maps.
- Nonreduced fibres are measured by the existing fibre algebra dimension,
  rather than cardinality of the underlying finite set.

Searches for existing statements (msearch outputs retained in searches.jsonl):

1. LeanFinder: `Finite locally free schemes of fixed degree form an fppf stack
   with effective descent and unique descent of isomorphisms`.
   Eight hits: finite morphism composition, affine-space finite presentation,
   and descent of properties of existing morphisms; none gives object effectivity
   and compatible-isomorphism descent of fixed-degree covers.
2. Loogle: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree,
   CategoryTheory.DescentData`. No hits; the first identifier is project-specific
   and unknown to the public Loogle index.
3. Mathlib grep through msearch:
   `(FiniteLocallyFree|finite locally free).*(descent|stack)|descent.*(FiniteLocallyFree|finite locally free)`
   in AlgebraicGeometry. Zero hits.
4. LeanSearch: `Effective descent finite locally free schemes of constant rank
   fppf covering`. Eight hits on finite morphisms, covers, flat descent and
   free loci; no exact statement.
5. Local `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
   `SchemeCoverDescentDatum`, finite-locally-free descent/stack patterns, and
   the proposed name. Found the existing family datum and related general
   affine descent interfaces, but no fixed-degree stack theorem. The node id
   does not occur in upstream `WeilConjectures`; the proposed full name has no
   occurrence in Mathlib, upstream, Sheaf, or `dag/lean_names_upstream.json`.
6. DAG search for `SchemeCoverDescentDatum` and fixed-degree fppf stack wording
   found `def-trf-scheme-cover-descent-datum` and its consumers. Reused that
   definition. No new definition node or dependency repair is needed.

No statement correction or STATEMENT-DISPUTED issue is needed. The item's
statement, proof and proof dependencies are unchanged; stmt_deps only gains
one already landed definition used by the statement. The Lean record contains
exactly the theorem signature from the file, with explicitly bound universes
and variables and no file-local notation or instance.

Validation: scompile.py compiled the module in both sandbox and final library
names with no messages (6.1 seconds and 5.0 seconds). The final compile and
prescribed delivery dry run are recorded below after execution.

## Second reading by Q80

This is the worker's second pass over the actual node and file; the maintainer
performs the independent review as prescribed in the dispatcher brief. No
additional agent was started.

Re-read each clause: `S`, `T : Over S`, and `d : ℕ` preserve the base and zero
case. The first conjunct uses the canonical second fibre-product projection.
`hcov` is the actual fppf family predicate; `D.localScheme`, `D.data.hom`, and
`D.data.hom_comp` retain local objects, given transitions, and their cocycle.
The existential global object includes the degree hypothesis on that same
object; each `IsPullback` gives the required local isomorphism and the displayed
transport equality enforces the prescribed transitions. The final clause
compares isomorphisms in the correct slice, imposes the ordinary pairwise
compatibility after the canonical overlap identification, and concludes a
unique isomorphism with exactly the original pullbacks.

The expanded geometric formula was compared with the recorded IsEffective
signature line by line: only the global degree assertion is added, as the
item requires. Checked that the compatibility domain uses projections to Z,
not projections to T_i (which would give the wrong fibre product), and that
composing to W does not lose a base-coordinate condition, since the local
isomorphisms already lie in Over U_i. No mathematical mismatch found. The
only second-pass edit was adding the explicit Mathlib QuasiSeparated proof
import so that every recorded permanence module is present.

Final validation: the final file compiled cleanly through scompile.py in both
names (14.7 seconds and 5.6 seconds). The required deliver2.py --no-push run
printed `OK (dry run): commit eb55480cee1 passes the preflight and compiles;
nothing pushed`. The delivery changes only the three prescribed files.
