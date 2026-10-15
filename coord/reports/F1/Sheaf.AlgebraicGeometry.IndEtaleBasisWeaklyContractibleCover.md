## What changed

Proved `AlgebraicGeometry.Scheme.AffineProEt.exists_weaklyContractible_cover` with its
signature unchanged. The proof constructs a singleton cover using
`exists_isWContractibleRing`, proves membership in the affine ind-etale basis and its
precoverage, then transports full-site section lifts to basis-site sheaves through the
restriction equivalence. The fully proved private helper
`surjective_evaluation_of_full_site` writes out the counit/naturality argument.

Only the item's Lean module changes. Its node now records this shorter route. Two new
DAG nodes attach the exact already-proved source APIs; no new Lean module or unproved
statement is introduced. The sole proof import is
`WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`.
The unit record was read: this supporting node realizes none of the unit's own statement
or steps, and the proper-base-change unit route is unchanged.

Validation: the item compiles without warnings in 2.6 seconds. After compiling the item
into the sandbox overlay, `#print axioms` on its public theorem shows exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The original sole direct importer
compiles unchanged against that overlay in 2.1 seconds. No extra axiom, definition,
instance, target change, or consumer adaptation is introduced.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.AffineProEt.exists_weaklyContractible_cover`
(node `lem-weil-pbc-ind-etale-basis-wcontractible-cover`).

Added 0 holes; split off 0 unproved statements. No `sorry` remains in any delivered Lean
file. This is a proof, not a decomposition. Both new source attachments are already
proved and appear in the allowed-axiom closure of the delivered theorem.

## No longer needed

Removed imports:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `Sheaf.RingTheory.IndPrincipalZariski`
- `Sheaf.RingTheory.IndEtaleStability`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`
- `Mathlib.CategoryTheory.MorphismProperty.Limits`
- `Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.RingTheory.BoundedWContractibleExtension`

The following former proof-dependency edges are removed from this item's node:

- `def-pc-scheme`
- `def-weil-etale-morphism`
- `def-weil-flat-morphism`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-size-convention`
- `def-weil-weakly-etale-morphism`
- `lem-weil-pbc-affine-scheme-qcqs`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-open-immersion-etale`
- `lem-weil-pbc-scheme-coproduct-family`
- `lem-weil-pbc-wcontractible-cover-section`
- `lem-weil-pbc-wcontractible-ring-extension`
- `lem-weil-pbc-weakly-etale-composition-base-change`

Their modules are not needed through this item, subject to uses elsewhere. In particular
`Sheaf.RingTheory.BoundedWContractibleExtension`,
`Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`,
`Sheaf.RingTheory.IndEtaleStability`, and `Sheaf.CategoryTheory.SiteCoveringAxioms`
are no longer proof imports here. The underlying basis and site definitions, and the
restriction equivalence, remain needed. No source/module is deleted, and no unit statement
or realized step is bypassed. Removal of a direct import does not assert that the module
is absent from all transitive imports or from the whole targets' closure.

## Where the brief, the DAG or earlier work was wrong

The planned five-step basis clopen-refinement/gluing proof is valid but unnecessary here.
The library already proves the ring construction in the same universe and full-site weak
contractibility, while the recorded basis lemma already supplies the actual restriction
equivalence. Its inverse preserves epimorphisms, and explicit counit naturality transfers
surjectivity. Thus the basis result can reuse these proofs without restating or proving
cardinality, covering-coproduct, or basis-gluing theory.

The proof uses an existential witness only inside a theorem proof; no public definition
chooses an arbitrary witness from an unproved existence theorem. Empty U and the zero-ring
case are included by the source construction and the same singleton/counit argument.

Searches were made with msearch.py (LeanFinder, Loogle, grep and LeanSearch) and source rg.
LeanSearch returned Internal Server Error; this is recorded as unavailable, without an
absence verdict. No Mathlib match was found by the available searches. Whole-blueprint
searches for w-contractible, 0983 and 0990 returned no duplicate blueprint statement;
source declaration searches found no existing node attached to either exact API.
The existing full-site affine extension node packages weaker existential information:
it does not retain ind-etaleness. The existing ring-retraction evaluation node has a
splitting hypothesis, rather than the geometric IsWContractibleRing hypothesis used here.
They are not used as if their proofs were additional statements.

## New nodes

`lem-weil-pbc-source-wcontractible-extension` attaches
`exists_isWContractibleRing` in
`WeilConjectures.RingTheory.ProEtale.WContractible`. It retains ind-etaleness, faithful
flatness and the geometric w-contractibility needed for the cover and evaluation. It is
already proved; no work is handed to another worker.

`lem-weil-pbc-source-affine-wcontractible-evaluation` attaches
`AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso` in
`WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`. It gives full-site local
section lifting for the geometric hypothesis, in every section universe, and is already
proved. The private transport helper supplies the basis-site conclusion.

Change record: `coord/changes/ind-etale-basis-wcontractible-cover-imports.md`.

## Second reading by F1

1. **Interfaces — pass.** Read the full repository/sandbox diff. The sole existing
   declaration, `AlgebraicGeometry.Scheme.AffineProEt.exists_weaklyContractible_cover`,
   has a byte-identical signature, including `[IsAffine S]`, the object and section
   universes, precoverage membership, and evaluation of every sheaf epimorphism.
   The only added declaration is the proved private transport helper. No definition,
   public instance, target, or other group's module changes. The two removed public
   imports are declared in the change record. Independently compiled the sole direct
   importer, `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint`,
   unchanged against the freshly compiled delivery: clean, 2.3 seconds.
2. **Proof and axioms — pass.** Compiled the delivered module cleanly (2.8 seconds).
   A scratch copy with `#print axioms` independently checked the public theorem,
   `surjective_evaluation_of_full_site`, `exists_isWContractibleRing`, and
   `ProEt.isWeaklyContractible_of_iso`: each uses only `propext`, `Classical.choice`,
   and `Quot.sound`; none uses `sorryAx`. Scanned the complete delivered Lean set:
   no `sorry`, forbidden declaration, or hollow definition. The ring witness is
   eliminated within this theorem proof, never used to define exported data.
3. **Split statements and edge cases — pass.** There are zero split-off unproved
   statements. Read both new source-attachment nodes against the actual declarations
   and their source proofs. `exists_isWContractibleRing` retains ind-etaleness,
   faithful flatness, geometric w-contractibility, and the same object universe.
   `isWeaklyContractible_of_iso` works in every section universe; its hypothesis
   is the spectrum isomorphism and the geometric ring class, not a splitting
   assumption silently substituted for that class. Neither source API has an existing
   DAG attachment (searched every node's primary and additional declarations).
   The existing full-site extension theorem omits ind-etaleness from its conclusion,
   so cannot construct this basis cover. Checked zero rings and empty schemes: all
   construction and transport declarations have no nontriviality or nonemptiness
   assumption; the singleton cover and counit identities remain valid. The helper
   quantifies over arbitrary sheaves and epimorphisms and imposes no existence of
   sections. Fresh LeanFinder, Loogle, and Mathlib grep searches using dense-subsite,
   restriction, surjectivity, and counit terminology found the generic comparison
   equivalence already used, with no shorter contractibility-transport theorem.
4. **Route and pruning — pass.** Read the full-site spectrum theorem, ring extension
   construction, weak-contractibility predicate, and the actual basis restriction
   equivalence in `Comparison.Affine`. Ind-etale composition constructs the basis
   object; faithful flatness and affine quasi-compactness give the singleton cover.
   The helper lifts an epi through the inverse equivalence, applies full-site
   weak contractibility, and evaluates counit naturality and its inverse identity;
   the orientations and evaluated objects agree. Both remaining imports are needed,
   with the source weak-contractibility module correctly a plain proof import.
   Compared old/new `proof_deps`: all 13 removed edges appear in `No longer needed`,
   and all 16 removed imports are listed. Read `dag/units/sk-thm-properbasechange.json`:
   this node realizes neither the unit statement nor a unit step, and no realized
   route is changed. No claim is made that removed direct imports disappear from
   the whole targets' transitive closure.
5. **DAG agreement — pass.** The existing node changes only `proof`, `proof_deps`,
   and `proof_origin`; its mathematical statement and Lean record are unchanged.
   Its four proof steps describe the code, and the union of their `uses` is exactly
   `proof_deps`. Checked every cited node exists. Both new nodes attach already
   proved source APIs, record their source proofs, searches, creation provenance,
   ancestor route, chapter, unit, and existing Lean declarations; they introduce no
   Lean statements or proof obligations and do not restate this item's conclusion.

Second reading changed only this report by adding the independent review and validation
above. The Lean proof, node records, and change record needed no repair. Holes closed:
`AlgebraicGeometry.Scheme.AffineProEt.exists_weaklyContractible_cover` (1 of 1);
holes added: none; split off: none.
