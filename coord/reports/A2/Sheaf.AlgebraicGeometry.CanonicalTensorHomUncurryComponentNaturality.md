## What changed

Proved `AlgebraicGeometry.schemeTensorHomUncurryComponent_natural` with its existing
signature and docstring unchanged. Added the proof-only import
`Sheaf.Algebra.Homology.HomComplexProjections` and updated the existing node's proof,
proof dependencies and proof origin to match the Lean proof.

Three proved private helpers implement the original two-step argument:
`comp_projection` reassociates the projected input;
`uncurry_natural` proves the sheaf tensor-Hom naturality calculation using its three
existing naturality identities and braiding naturality;
`hom_uncurry_natural` combines the projection formula and that calculation on an
arbitrary ringed site. The public theorem specializes the last helper to the
scheme and its fixed K-injective resolution. Keeping the calculation general avoids
repeated unfolding of scheme coercions and the chosen resolution during rewrites.

The entire delivered module compiles through `lcompile.py`, without errors or warnings.
No definition, existing signature, visibility or public import changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.schemeTensorHomUncurryComponent_natural`
(node `lem-pc-tensor-hom-uncurry-component-naturality`).

Remaining holes in the item's module: none. Added holes: none. This is a proof,
not a decomposition into additional unproved statements. All three private helpers
are proved. The added projection API is an existing proved theorem.

## No longer needed

No original imports removed and no original dependency nodes or modules pruned.
The original two-step component calculation is retained. The new proof-only import
supplies the small, already-proved projection API for the same Hom-complex construction.
No totalization, differential, localization or flatness modules are needed as additional
proof dependencies. No claim is made that any original transitive dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The earlier sandbox attempt had not compiled and
its report correctly recorded no validated closure. It repeatedly unfolded the large
chosen constructions while rewriting the scheme-specific goal. The present proof
instead proves the calculation for a general ringed site and specializes it once;
this resolves the elaboration failure without changing any definition or statement.
The node's original route and the unit's route are preserved.

## Second reading by A2

1. Compared the complete delivered module against the repository version. PASS:
   the existing public declaration's signature, docstring, visibility, and public
   import are unchanged. Restored the single extra space before `:= by` so the
   existing signature is byte for byte identical. Only three proved private
   helpers, a proof-only import, and the original hole's proof are added.
2. Compiled the module locally with `lcompile.py`, with no errors or warnings.
   Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.schemeTensorHomUncurryComponent_natural`: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   PASS: no remaining or added holes, forbidden declarations, or hollow
   definitions. The helpers only use the existing chosen projection family;
   they introduce no new public data construction or arbitrary witness.
3. PASS: no statements were split off and no new unproved statements were added.
   Read all three private helper proofs: categorical reassociation, tensor-Hom
   naturality followed by braiding naturality, and their composition are valid
   without extra hypotheses on degrees or maps. Identity and zero maps and
   arbitrary integer degrees require no special exclusions.
4. PASS: searched the repository for alternative uncurrying/naturality APIs and
   Mathlib through `msearch.py grep` with braiding and tensor-Hom terms.
   The proof already uses the existing sheaf tensor-Hom equations and generic
   braiding naturality; generic monoidal-closed uncurrying alone does not expose
   this chosen Hom-complex projection. Both imports are needed: the public model
   supplies the statement's definitions, the plain projection import supplies
   its proof API. All three original dependency nodes remain used; no old node
   or module is omitted from `No longer needed`. Read the unit record
   `sk-thm-picard-duality`: its realized arrays are empty, and this local
   calculation does not bypass or change a unit statement or step.
5. PASS: compared the node JSON with the repository and read its dependency
   declarations. Only `proof`, `proof_deps`, and `proof_origin` changed; the
   added existing projection node matches the actual API used. The two proof
   steps correctly describe the component projection and braided uncurrying
   calculations, followed by specialization to the fixed scheme resolution.

Second reading changed only the extra signature whitespace and added this review
record. One original hole is closed, zero holes are added, and nothing is pruned.
