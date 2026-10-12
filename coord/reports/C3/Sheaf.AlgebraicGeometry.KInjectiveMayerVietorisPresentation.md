## What changed

Replaced the invalid earlier attempt with a decomposition of the unchanged
`AlgebraicGeometry.schemeKInjective_mayerVietoris_presentation`.

`KInjectiveMayerVietorisData` constructs the restriction/direct-image adjunctions,
the direct-image complexes, their units, the overlap restrictions as mates of
restricted counits, and the biproduct arrows. It proves the iterated-unit identity
and the zero composite using naturality and the adjunction triangle identity.
Every object and arrow is explicitly constructed; no data is chosen from an
unproved existence theorem. It imports HomologicalComplexAbelian for the
complex biproduct and short-complex structures, rather than the derived
short-exact triangle module.

`KInjectiveMayerVietorisExact` states exactness of this fixed diagram for a cover
and a complex with injective terms. `KInjectiveMayerVietorisComparisons` states
comparison isomorphisms for its three fixed terms, compatible with the U,V units
and the two fixed overlap restrictions. It needs K-injectivity, but neither a
cover nor termwise injectivity. Each new module has one named remaining theorem.

The presentation proof combines the termwise comparisons through Q.mapBiprod
and biprod.mapIso, verifies its first arrow by the two projections, verifies
its second arrow by the two injections and preservation of negation, and supplies
the fixed diagram's short exactness. Public imports and the existing theorem
signature are unchanged. Proof imports and its node's proof route are updated.

Read Stacks cohomology.tex, lemma-exact-sequence-j-star (08BV) and the proof of
lemma-mayer-vietoris (01EB), in the available mirrored literature tree. The
canonical construction is the direct-image sequence of 08BV. The unit
`sk-thm-picard-duality` has empty realized statement/step attachment lists; its
existing derived Mayer--Vietoris route is retained, not replaced by a different
triangle argument.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.schemeKInjective_mayerVietoris_presentation`
(node `lem-pc-kinjective-mayer-vietoris-presentation`).

Added two strictly smaller holes, exactly the two proof obligations remaining:

- `AlgebraicGeometry.schemeMayerVietorisComplex_shortExact`
  (`lem-pc-kinjective-mayer-vietoris-exact`).
- `AlgebraicGeometry.schemeOpenModuleImageComplex_comparisons`
  (`lem-pc-kinjective-mayer-vietoris-comparisons`).

This is a decomposition, not a sorry-free proof: 1 upper hole closed, 2 lower
holes added. The item itself contains no sorry. The data module has no sorry:
`schemeOpenModuleImage_unit_restriction`, `schemeMayerVietoris_zero`, the private
generic unit/mate calculation, and all construction obligations are proved.
The two new named holes have complete proof docstrings and DAG records.

Edge checks: exactness requires the cover and termwise injectivity, and asserts
nothing about arbitrary complexes B,C. The comparison lemma needs no cover and
speaks only about the fixed J_U,J_V,J_intersection. Empty opens give the zero
restriction/direct-image term; repeated opens give the diagonal and difference
sequence. For differently chosen adjunctions, the right-adjoint automorphisms
postcompose the comparisons and conjugate the overlap maps by the same factors.
The zero complex is included in both lemmas without additional hypotheses.

## No longer needed

Removed direct proof imports from the presentation:
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
`Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`, and
`Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`.
The first two are the proof dependencies of the new comparison and exactness
items, respectively. SchemeDerivedDirectImage remains supplied by the unchanged
public DerivedOpenRestrictionMaps import. Consequently none of these modules
is globally pruned. Their old DAG proof dependencies now live on the appropriate
lower items; the presentation uses only the concrete diagram and the two new
lemmas. No unit statement or unit proof step is pruned.

The redundant proof import `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
is also omitted: the proof compiles using the existing public imports.

The invalid earlier `exists_schemeKInjective_mayerVietoris_data` and
`exists_schemeKInjective_mayerVietoris_comparisons` are entirely discarded.
Neither was a repository declaration. Their arbitrary existential data and
false universal comparisons are not used or delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier comparison theorem was false: it quantified over arbitrary B,C,f,g
with no relation to open restriction/direct image. It is replaced by comparisons
only for explicitly constructed complexes and maps. The earlier short exact data
existence lemma also did not characterize its witnesses, so it could not feed
such a comparison lemma. No arbitrary witness is chosen in this delivery.

The earlier nodes had empty lean.statement fields and placeholder prose. The
new records contain self-contained statements, actual Lean signatures, complete
proof steps and dependency unions, sources, and recorded Mathlib searches.
Every original interface is unchanged. No forced adaptation or statement change
is required. The earlier second reading is not reused or represented as current.

Mathlib search found generic MayerVietorisSquare short exactness, the exactness
criterion for complexes, restriction adjunctions and biproduct comparison lemmas;
none directly states this module's theorem. The generic biproduct and adjunction
lemmas are used. LeanSearch returned Internal Server Error for all three new-node
queries; these genuine unavailable searches are recorded without a match verdict.
Loogle/LeanFinder and source grep were performed successfully.

## New nodes

`def-pc-kinjective-mayer-vietoris-data`: the explicit restriction/direct-image
short complex, in KInjectiveMayerVietorisData, with its zero composite proved.

`lem-pc-kinjective-mayer-vietoris-exact`: short exactness of that fixed diagram,
in KInjectiveMayerVietorisExact; no derived-category or K-injectivity hypotheses.

`lem-pc-kinjective-mayer-vietoris-comparisons`: derived comparisons and the four
individual arrow identities, in KInjectiveMayerVietorisComparisons; no cover or
termwise injectivity hypotheses. The higher theorem assembles their biproduct
identities in a complete Lean proof.

No change records are needed: no existing statement, definition, visibility,
or public import is changed.

## Second reading by C3

1. Compared the presentation with the repository using diff. Its existing theorem
   signature is byte for byte unchanged, as are its docstring and public imports.
   The other three modules and nodes are new. No existing definition or target
   statement changes, so no change record or forced adaptation is needed. PASS.
2. Compiled all four modules in import order with lcompile.py. Independently
   compiled scratch copies with #print axioms for every public declaration.
   Every declaration of the data module uses only propext, Classical.choice and
   Quot.sound. The presentation and the two named lower theorems additionally
   use sorryAx, as expected for this decomposition. There are exactly two local
   sorry occurrences, both the complete bodies of the reported named theorems.
   No forbidden declarations or hollow definitions occur. PASS.
3. Read both split-off signatures, proof docstrings and DAG nodes, and checked
   Stacks cohomology.tex at lemma-exact-sequence-j-star,
   lemma-restrict-K-injective-to-open and lemma-mayer-vietoris in the mirrored
   literature tree. Exactness is for the fixed sectionwise restriction diagram,
   with precisely the cover and degreewise injectivity needed for gluing and
   surjectivity. Comparisons are for the three fixed terms and four fixed arrows;
   they use K-injectivity and make no exactness assertion. The adjunction-change
   formula conjugates each overlap map by the same right-adjoint isomorphisms
   used to postcompose the object comparisons. Empty opens give zero terms;
   U=V=top gives diagonal/difference; zero complexes give zero diagrams. Neither
   lower theorem restates the presentation. Independent LeanFinder, Loogle and
   Mathlib grep searches with different queries, plus searches of lean/, found
   generic ingredients but no duplicate of either fixed-diagram theorem. The
   generic MayerVietorisSquare short complex concerns sheafified representables,
   so it does not directly close the module-sheaf diagram. PASS.
4. Read the proof from the presentation downward: explicit data, short exactness,
   comparisons, then biproduct assembly using the projections and injections.
   Removed the redundant AdditiveFunctor proof import and compiled a scratch
   copy without it successfully. Other new public imports provide signature
   definitions or category instances. The three old direct proof imports and
   their four old proof-dependency nodes are all accounted for under No longer
   needed: lower items carry the needed obligations and DerivedOpenRestrictionMaps
   remains in the unchanged public interface. No module is globally pruned.
   Checked sk-thm-picard-duality's realized fields: its statement and step
   attachment lists are empty; the existing derived Mayer--Vietoris route stays.
   Neither remaining hole is a quick application of an existing result: they
   require sectionwise diagram identification or derived-adjunction coherence.
   This is one upper hole closed and two lower holes added, not a net proof gain.
   PASS as a decomposition.
5. Compared node statements and dependency unions with Lean. The presentation's
   proof route matches its concrete construction and the two actual theorem
   applications. The two lower nodes describe the exact Lean obligations and
   have sources, proof steps, searches and creation records. Repaired the data
   node's empty proof route by recording the adjunction/mate calculation and
   zero-composite construction, and its corresponding dependency and origin.
   Stored the three new nodes' Lean signatures verbatim with their source line
   breaks. PASS after these documentation repairs.

Second reading changed only the redundant presentation proof import, the three
new nodes' signature formatting, the data node's proof/dependency/origin record,
and this report. It added no holes and changed no mathematical statement.
