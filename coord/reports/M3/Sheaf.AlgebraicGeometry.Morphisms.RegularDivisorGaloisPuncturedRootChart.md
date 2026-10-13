## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_punctured_root_chart`
with a complete Lean reduction to two strictly smaller mathematical statements.
The signature and all four public imports are unchanged. Added two private-to-importers
proof imports, and updated the original node's proof, proof_deps and proof_origin.

The first new module, `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorGaloisRootSplitting`,
asks only for a single root extension splitting the torsor on a pointed affine etale
neighborhood. Its equation is the actual image of the original f under its ring map.
It does not ask for an isomorphism from the torsor to a product of root algebras.
The second, `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicCharts`, classifies
an arbitrary scheme factoring through D(g) whose pullback to one punctured root cover
has a supplied splitting. It has no Galois cover, group order, ambient L/U, or beta
hypothesis; its proof is the intermediate cyclic-orbit step after ramification has
already been killed.

The original module constructs the factorization through D(g) from beta using
pullback.lift and the universal property of the open immersion. It applies the second
lemma, composes the two pointed etale neighborhoods, and constructs the final
isomorphism by pullback.congrHom and pullbackLeftPullbackSndIso. The morphism
compatibility is proved by their second-projection identities.

Read the unit sk-prop-input-spreading, including its trait paragraph and its quotation
of 0EYG as a classical input. This reduction follows the proof of that input and changes
no unit or chapter route. Sources read directly:
[09EB](https://stacks.math.columbia.edu/tag/09EB),
[0EYG](https://stacks.math.columbia.edu/tag/0EYG),
[0BRM](https://stacks.math.columbia.edu/tag/0BRM),
[0EYE](https://stacks.math.columbia.edu/tag/0EYE), and
[05N9](https://stacks.math.columbia.edu/tag/05N9).

The three delivered modules compile together through lcompile.py, without warnings.
No data definitions, instances, public import visibility, or existing signatures changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_punctured_root_chart`
(node `lem-sbc-regular-divisor-galois-punctured-root-chart`). Its proof contains no sorry.

Added two holes, each exactly a named public theorem with proof `:= by sorry`:

- `AlgebraicGeometry.Scheme.GaloisCover.regular_divisor_root_splitting`
  (node `lem-sbc-regular-divisor-galois-root-splitting`).
- `AlgebraicGeometry.Scheme.root_split_cover_cyclic_charts`
  (node `lem-sbc-root-split-cover-cyclic-charts`).

This is a decomposition, not a sorry-free proof: one hole closed and two holes added,
net -1. The factorization and assembly are proved in Lean. No sorry remains in the
assigned module, and no sorry is placed inside any definition or private helper.

Boundary checks on the new statements: n must be positive and a unit, which makes the
root morphism faithfully flat and etale over D(g). The explicit factorization is necessary:
without it, arbitrary components supported on V(g) would be invisible to the root
splitting hypothesis and invalidate the cyclic classification. No connectedness or
surjectivity is assumed for the second lemma. Empty covers use d=m=0; the empty product
ring has empty spectrum. For n=1 the splitting is an ordinary splitting over D(g).
Off the divisor the finite etale cover splits etale locally, with exponent 1 and unit
equation (the second lemma may use h=1). A zero base has no point y, so the pointwise
assertion is vacuous. At a divisor point regularity of the quotient and the nonzerodivisor
hypothesis ensure the strictly local equation is prime. No excellence, smoothness,
trait hypothesis, or chosen arbitrary witness is required by either statement.

## No longer needed

None. The original node had no proof dependencies and the original module had no
proof-only imports to prune. Its public imports are needed by its unchanged statement.
Both new proof imports are used. No claim is made that any other target-reachable
module has become unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node contained a substantial three-step proof but had empty uses and
proof_deps throughout. The shorter-route search found no ready classification theorem:
LeanFinder returned finite etale algebra decompositions over fields and Kummer field
extension ingredients; Loogle returned no result for AdjoinRoot with IsRegularRing;
grep found no single-root splitting or root-split classification declaration.
The second reading also found the existing
`GaloisCover.regular_divisor_prescribed_punctured_root_chart`: it classifies a Galois
torsor at a point on the divisor and remains sorry. It does not directly state either
new lemma (one returns a single-root splitting, the other has no Galois hypothesis),
and its point-on-divisor hypothesis excludes the off-divisor case of this item.
The earlier claim that no classification declaration exists was too broad; the
search results for the two new statements remain negative. LeanSearch
was unavailable (Internal Server Error). Consequently there was no named Lean result
to apply for either of the two substantive parts of the argument. These are now explicit
separate items rather than hidden glue. The original mathematical statement was not
changed or disputed.

## New nodes

`lem-sbc-regular-divisor-galois-root-splitting` records the subargument of 0EYG which
passes to a strict henselization, adjoins one root killing all tame ramification, extends
by purity and splits there, then descends that splitting to a pointed etale neighborhood.
Its theorem returns the ring map a and uses g=a(f); support factorization is constructed
in the assigned module, rather than included as a new hole. It shares the original
node's chapter and unit and has a complete source-based proof in its docstring.

`lem-sbc-root-split-cover-cyclic-charts` records the intermediate root-extension
classification after a single-root splitting has been supplied. Finite etale descent
first recovers a finite etale cover of D(g); strictly locally the root cover is a connected
cyclic torsor, whose finite orbits give intermediate e-th root covers. It includes the
finite product packaging and off-divisor case. Its docstring spells out this argument
and its edge cases. It shares the original node's chapter and unit.

No interface change record or forced adaptation was needed.


## Second reading by M3

1. **Visible interfaces — PASS.** Compared the assigned module with the repository
   using diff, and compared its theorem signature as literal bytes: unchanged.
   No existing definition, instance, visibility or public import changed. The only
   existing-node changes are proof, proof_deps and proof_origin. No change record
   or forced adaptation is required. The two added imports are plain proof imports.

2. **Proof and axioms — PASS as a decomposition.** Compiled all three modules in
   import order through lcompile.py: clean, about 3–4 seconds per file. Inspected
   the factorization through D(g) and both pullback-pasting identities from the top
   downward. The assigned theorem has no sorry; each new module has exactly one
   named public theorem whose entire proof is `by sorry`. There are no definitions
   or forbidden declarations/attributes. Scratch copies with #print axioms for
   all three theorems report precisely propext, Classical.choice, Quot.sound and
   sorryAx. No arbitrary witness is installed as the data of a definition.

3. **Split statements and searches — PASS.** Read both signatures, docstring
   proofs and nodes against [0EYG](https://stacks.math.columbia.edu/tag/0EYG),
   [09EB](https://stacks.math.columbia.edu/tag/09EB),
   [0BRM](https://stacks.math.columbia.edu/tag/0BRM) and the cited descent tags.
   IsRegularRing includes Noetherianity, so the regular-divisor argument applies.
   Invertibility of |G| rules out inseparable residue degrees and wild indices.
   Reapplying the stabilizer argument to the strict-henselian G-torsor permits
   n=|G|. For cyclic classification, n>0 makes the root algebra finite free of
   positive rank; n invertible makes its restriction to D(g) finite etale and
   faithfully flat. The explicit support factorization excludes hidden components
   on V(g). At a divisor point the strict-local base, its divisor quotient and
   its root ring are domains; thus the cyclic torsor is connected, and its descent
   cocycle gives constant permutations. Checked n=1, the trivial group, d=0,
   the zero ring (no point y), a unit equation and points outside the divisor.
   Repeated LeanFinder and Loogle searches using different terms and rg in the
   library. Hits give field Kummer theory, not either new theorem. The existing
   prescribed-chart theorem is recorded above; its stronger chart conclusion and
   extra point hypothesis do not duplicate either new signature. Neither new hole
   can be closed in a few minutes using the available declarations. The reduction
   is genuine: it constructs the support factorization and assembles the two base
   changes; it is not a renamed application of the original statement.

4. **Route and pruning — PASS.** All imports serve their signatures or the two proof calls (the assigned
   module has four public imports and two plain imports). No original proof
   dependency or proof-only import was removed, so No longer needed is complete.
   Read sk-prop-input-spreading and its realized record: its quoted regular-divisor
   tame input remains on the trait route; no unit statement, step or realized
   field changes. The prescribed-chart theorem handles only divisor points; using
   it alone does not discharge this item's pointwise statement or either split
   statement. No shorter complete reduction was found. Count remains one hole
   closed, two holes added, net -1: decomposition, not a sorry-free proof.

5. **Nodes and Lean — PASS.** All three lean.statement fields match their theorem
   signatures byte for byte. The assigned node's four steps follow the two lemma
   calls, constructed factorization and pullback assembly; proof_deps is exactly
   the union of uses. Both new nodes have the required source, proof, origin,
   searches, created, blueprint, chapter, unit and Lean records, and their named
   holes have source-based complete natural-language proofs. Their statements are
   strictly separate mathematical parts of the argument.

**Second-reading changes:** clarified the single-root docstring and node proof to
choose n=|G| and justify divisibility again after strict henselization; clarified
how connectedness and the descent cocycle give a finite cyclic set in the cyclic
classification docstring and node; added independent search records to the new
nodes; corrected the report's overly broad missing-classification claim; added
this review. No Lean statement, import or proof body was changed.
