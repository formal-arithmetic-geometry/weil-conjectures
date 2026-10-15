## What changed

Proved `PrincipalWLocalization.StrictWCover.properties` without changing its signature,
using the point description, contraction properties, and retained-localization properties.
The proof constructs the closed-point lift explicitly, transports strict henselianity along
the supplied canonical local-ring bijection, and derives faithful flatness from flatness
and spectrum surjectivity.

Two fully proved private helpers convert principal ind-Zariski presentations into
ind-etale presentations and prove maximality of primes lying over maximal ideals under
an ind-etale map. The latter uses the source library's separable-image theorem and
Mathlib's integral-domain-over-a-field criterion. This avoids the planned detour through
weakly etale field algebras. Composition and flatness also use the proved source library.

Added proof imports `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic` and
`WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale`. Updated the item's DAG proof and
proof dependencies to describe the actual argument. Public imports are unchanged.

## Proved and sorry left

Closed: `PrincipalWLocalization.StrictWCover.properties`
(node `lem-weil-pbc-strict-w-cover`), the module's only original hole.
Added holes: none. Remaining holes in delivered modules: none. No split-offs.
Both private helpers are completely proved. The imported statements
`PrincipalWLocalization.points`, `CommRingCat.etaleContraction_properties`,
`PrincipalWLocalization.Retained.properties`, and
`PrincipalWLocalization.isIndPrincipalZariski` remain their existing downstream obligations;
the delivery does not claim to have proved those dependencies.

Validation: the single module compiles cleanly through `lcompile.py` in approximately
three seconds. No global build was run. The arguments include the zero ring: whenever
a quotient field is used, a prime ideal already supplies its nontriviality. The principal
presentation conversion includes the empty finite product. No arbitrary algebra or map
is selected from an unproved existence theorem.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.WeaklyEtaleField`;
- `Sheaf.RingTheory.IndEtaleStability`.

Removed direct proof dependencies `lem-weil-pbc-weak-etale-field` and
`lem-weil-pbc-ind-etale-stability`. The maximality proof needs neither base change nor
the weakly etale field classification. Composition and weak etaleness instead use proved
source-library declarations. These modules can still be reached through other imports;
this is pruning of this item's proof edges, not a claim of global unreachability.
All remaining direct imports are used by the statements or proofs.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction was needed. The planned proof was longer
than necessary: the existing source-library separable-image theorem handles maximality
without introducing the fibre algebra. The unit's statement and all its realized steps
are preserved. The referenced literature files are absent from this checkout, so the
source paragraph was read at https://stacks.math.columbia.edu/tag/097X instead.

## Second reading by F3

1. **Interfaces: pass.** Compared the sole delivered Lean module with the repository
   version using `diff -u`. The existing declaration `properties`, its parameters,
   universes, five conjuncts, and visibility are unchanged byte for byte. No definition
   changes, adapted modules, new public declarations, or change records occur. The two
   added helper theorems are private and proved. Public imports remain unchanged; both
   newly added imports serve the proof only and use plain `import`.

2. **Proof and axioms: pass.** Independently compiled the module through `lcompile.py`
   with no warnings or errors (2.9 seconds). Read the complete proof and both helpers;
   scanned the delivered code for holes and forbidden declarations, finding none.
   A scratch copy with `#print axioms` confirms that both private helpers use only
   `propext`, `Classical.choice`, and `Quot.sound`. The same holds for the upstream
   separable-image theorem, ind-etale composition, ind-etale weak-etaleness instance,
   and strict-henselian ring-equivalence transport. The main theorem additionally
   uses `sorryAx` through the four existing imported obligations listed above;
   no new hole or arbitrary witness used to define data was introduced.

   Read [Stacks 097X](https://stacks.math.columbia.edu/tag/097X), first proof paragraph:
   its properties (1), (3), (7), (9) are exactly the five Lean conjuncts, with (1)
   separated into faithful flatness and ind-etaleness. The first paragraph constructs
   this algebra from A alone; the extra map A to B in the full Stacks statement is
   only needed for the subsequent construction of D. Checked each use of the imported
   statements: `points` supplies closedness and the diagonal closed-point lift;
   `etaleContraction_properties` supplies faithful flatness, ind-etaleness and strict
   henselianity at maximal ideals; `Retained.properties` supplies the actual canonical
   local-ring bijections, w-locality and diagonal closed points. Inverting its
   homeomorphism in `hstrict` makes the second coordinate a maximal prime of E, so
   the direction of `of_ringEquiv` is correct. In `hsurj`, the equality returned by
   `hlocal` identifies the contraction of the chosen closed point with q; composition
   then gives its image x in Spec A. The final faithful-flatness criterion has its
   flatness instance from ind-etaleness and its surjectivity from this same lift.

3. **Split statements and edge cases: pass.** There are no split-offs. Reviewed the
   private helpers too: finite products of principal localizations, including the
   empty product, are etale; the same filtered presentation therefore gives ind-etaleness.
   For the maximality helper, q prime makes S/q a nonzero domain, and maximality of
   its contraction makes R/m a field. The scalar towers use the canonical quotient
   maps. The upstream separable-image theorem applies to q's residue field as a local
   R/m-algebra, and the injective quotient-to-residue-field map reflects integrality.
   Mathlib's integral-domain-over-a-field criterion therefore proves maximality.
   For a zero source or target ring there is no prime q requiring these field
   structures; the main proof's spectrum arguments also allow the empty spectrum.
   Independently searched `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib by variants
   of maximality, integrality and ind-etaleness. Additional logged searches were
   Loogle `IsIntegral, IsField` (no hits) and LeanFinder for zero-dimensional fibres
   of ind-etale morphisms (etale-locus results, no direct replacement). The integral
   going-up maximality lemma requires an integral extension and does not replace
   this argument for an arbitrary ind-etale extension.

4. **Route and pruning: pass.** The proof opens the original hole and assembles the
   existing point, contraction, and retained-localization statements. The shorter
   maximality argument uses a proved upstream separability theorem; composition and
   flatness likewise use proved upstream declarations. Both removed proof dependencies,
   `lem-weil-pbc-ind-etale-stability` and `lem-weil-pbc-weak-etale-field`, and their two
   direct imports are listed under `No longer needed`; no other old dependency was
   removed. Checked `dag/units/sk-thm-properbasechange.json`: its statement and all
   `realized` step nodes are preserved. The argument still follows the specified
   w-localization, contraction, retained-localization route. Pruning is limited to
   this item's direct edges, as the report states.

5. **DAG: pass.** Compared the node JSON with the repository: only `proof`,
   `proof_deps`, and `proof_origin` change. The statement, statement dependencies,
   source, Lean signature record, chapter and unit remain unchanged. The five steps
   describe the implemented closed-locus/maximality argument, canonical local-ring
   transport, explicit closed-point lift, and composite flatness argument. Their
   `uses` union equals `proof_deps` exactly. Read the declarations and Mathlib matches
   of the old dependencies; the two removed ones are precisely the unused detour.
   There are no new nodes requiring additional metadata or searches.

Second-reading changes: appended this independent review and recorded the additional
searches and scratch axiom check. No Lean or DAG repair was needed. The delivered result
closes one existing hole and adds zero holes; it does not claim the four imported
obligations are closed.
