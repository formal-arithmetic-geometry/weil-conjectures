## What changed

Proved `AlgebraicGeometry.strictHenselizationMapExists` in
`Sheaf.Paper.StrictHenselizationMapExists`, with its signature unchanged.
The proof extends the affine limit cones to all pointed etale neighbourhoods,
pulls neighbourhoods back along g, and uses the resulting cone's limit lift.
Its marked-point equations give the prescribed residue equality; locality follows
from `isLocalHom_of_comp`. Both private helpers are completely proved or constructed.
The affine-to-full cone transport and pointed pullback construction adapt the existing
private proofs in `Sheaf.AlgebraicGeometry.StrictHenselizationSchemeFunctoriality`;
that module is not imported, and its weaker public existence theorem does not supply
the marked-point equation needed here. No public declaration or definition changes. The second reading also removes one
unused public import; both direct importers have independent access to its API.
Updated the item's proof, proof_deps and proof_origin to this route, and updated the
proof docstring. The import removal is documented in
`coord/changes/strictHenselizationMapExists-unused-public-import.md`; no consumer
adaptation is needed.

Validation: the delivered module compiles cleanly with `lcompile.py` (about 3 seconds)
after removing the unused proof imports. A separate scratch copy with
`#print axioms AlgebraicGeometry.strictHenselizationMapExists` compiled in 4.4 seconds
and printed exactly `[propext, Classical.choice, Quot.sound]`.
`deliver3.py C1 Sheaf.Paper.StrictHenselizationMapExists --no-push` printed
`OK (dry run)` for commit `113a15d1ce`: compilation and preflight passed except for
the second reading, which the independent reader writes. Nothing was pushed.
The unit `sk-thm-p1` and its realized statements and steps are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.strictHenselizationMapExists`
(node `lem-weil-pbc-strict-henselization-map-exists`), the module's sole original hole.
Holes added: none. Holes left in the delivered module: zero. Split-offs: zero.
This is a complete proof, not a decomposition into new holed lemmas.
The compiled theorem's axiom set contains no `sorryAx`.

## No longer needed

Removed imports (the Henselian public import was removed by the second reader):

- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`.
- `WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`.
- `WeilConjectures.Mathlib.RingTheory.Henselian` (unused public import).
- The redundant direct `Sheaf.AlgebraicGeometry.StrictHenselization` import
  (already publicly imported by the structural-map interface).

The proof no longer needs the old dependency nodes
`lem-weil-pbc-strict-henselization-local-structure`,
`thm-weil-pbc-weak-etale-strict-local`,
`def-weil-pbc-henselian-terminology`, `def-weil-open-immersion`,
`def-weil-geometric-point`, `def-weil-residue-field`, or
`def-weil-pbc-relative-separable-closure` as proof steps. The last three notions
remain in the unchanged statement, so their statement dependencies remain intact.
No etale section, localization, weakly-etale bijectivity, or diagonal-rigidity lemma
is needed. The unused public `WeilConjectures.Mathlib.RingTheory.Henselian` import was also
removed in the second reading; no declaration from it is needed. The proof still uses the small
diagram API from `Sheaf.AlgebraicGeometry.StrictHenselization`.
This lists dependencies removed from this item's proof, not a claim that those modules
are unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

The old plan was unnecessarily long: it constructed sections of etale schemes over
the strict local source using Olivier's theorem and proved compatibility by rigidity.
The full pointed-neighbourhood limit already supplies a canonical compatible family
at every pulled-back neighbourhood. Keeping each cone's marked-point equation makes
the required residue compatibility follow by limit extensionality. Neither strict
henselianity nor the hypotheses hOmegaS/hOmegaT are needed in this proof; their
original binders are retained. The source's functoriality and inverse-limit route,
and all unit-level statements and steps, are preserved.

Searches run with msearch.py: LeanFinder for induced strict-henselization maps returned
residue-field and stalk APIs, not the desired theorem; Loogle for IsLimit.hom_ext
reported an unknown identifier; grep for strictHenselization.*[Mm]ap returned no hits.
Direct rg of both library roots found the existing scheme-map construction above.
No new node is required: private helpers implement the recorded limit/initiality API,
and all proof steps are fully formalized.


## Second reading by C1

1. **Statements and interfaces: PASS.** Compared the complete delivered module and node
   with the shared repository. The signature of
   `AlgebraicGeometry.strictHenselizationMapExists`, from `theorem` to `:= by`, is byte
   for byte identical. In particular, the geometric-point compatibility, both algebra
   structures and their embedding equations, both local-ring instances, both residue
   equivalences and all pointed-neighbourhood equations remain. All three conclusions
   remain: locality, the structural square, and equality of ring maps to Omega.
   The two added helpers are private. No existing definition or target changes.
2. **Kernel proof and data: PASS.** Independently compiled the delivered file and a scratch
   copy with `#print axioms`. The theorem uses only `propext`, `Classical.choice`, and
   `Quot.sound`; there are no forbidden declarations or sorry tokens. The full cone is
   constructed by affine-spectrum transport and initial extension. The pullback functor's
   object is explicitly the scheme pullback, with its point explicitly `pullback.lift`.
   The ring map comes from the uniquely determined limit lift via `Spec.preimage`.
   No data are selected from an unproved mere-existence statement. The use of `.some`
   selects an `IsLimit` structure, whose fields are uniquely determined by its universal
   property, rather than an unspecified geometric object.
3. **Split statements and small cases: PASS.** No split-offs or new public statements,
   no holes added, and the one original hole closed. Checked the identity-base case:
   pointed pullback legs recover the canonical cone and its marked point. The argument
   applies to arbitrary base morphisms and does not assume affineness of either base.
   The chosen neighbourhood in the structural-square argument exists by cofilteredness;
   an empty indexing category is not tacitly assumed nonempty. Locality follows from
   the local residue composite, using field-map locality and `isLocalHom_of_comp`.
4. **Shortest route, imports and unit: PASS after cleanup.** Read the existing private
   cone/pullback construction and public `exists_strictHenselizationSchemeMap` in
   `StrictHenselizationSchemeFunctoriality`; its public conclusion omits the pointed
   equation, so applying it alone does not prove this item. The delivered refinement
   proves that equation during construction. Read `StrictHenselizationCanonicalMap`:
   it depends on `StrictHenselizationFunctoriality`, which imports this item, and hence
   is not an available shorter route. An independent LeanFinder query about compatible
   geometric points and induced strict-henselization maps returned only stalk/residue
   APIs, not this theorem; direct rg confirmed these existing interfaces. No duplicate
   public interface is introduced. Verified every removed old proof dependency appears
   in `No longer needed`. Read `dag/units/sk-thm-p1.json`, including `realized`: this
   item is below its realized statements and steps, and none of those is bypassed.
   Removed the unused public Henselian import after a scratch compile without it passed.
   The two direct importers independently import the Henselian API (one through its
   public canonical-map/functoriality imports); checked their original sources against
   the delivered module in a scratch compilation overlay.
5. **DAG agreement: PASS.** Only `proof`, `proof_deps`, and `proof_origin` differ in the
   node. Their four steps follow the code: extend the pointed affine cone, pull back
   neighbourhoods and lift the cone, prove the structural and pointed equations, and
   pass through Spec faithfulness to the local ring map. `proof_deps` is exactly the
   union of the steps' `uses`. The node statement, statement dependencies, Lean record,
   source, unit and chapter are unchanged. No new node is required. The unused public import removal has the change record
   `coord/changes/strictHenselizationMapExists-unused-public-import.md`, added after
   the first second-reader dry run required an export-change record.

Changes by the second reader: removed the unused public import
`WeilConjectures.Mathlib.RingTheory.Henselian`, updated the import-pruning report,
added the import-removal change record required by preflight,
and added this independent reading. The proof terms and node metadata were correct
and are retained. Holes closed: `AlgebraicGeometry.strictHenselizationMapExists` (1).
Holes added: none (0); holes remaining in this module: none (0).
