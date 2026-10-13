## What changed

Added a `STATEMENT-DISPUTED` comment immediately before
`AlgebraicGeometry.schemeDerived_mayerVietoris_directImage`. No signature, import,
definition, proof, or DAG route was changed. The existing naturality proof compiles.
The dispute concerns the canonical comparison interface, not the availability of
proof dependencies that contain `sorry`.

## Proved and sorry left

Holes closed: none. Holes added: none. Split off: none.

The one pre-existing hole remains:
`AlgebraicGeometry.schemeDerived_mayerVietoris_directImage`
(node `lem-pc-derived-mayer-vietoris-functorial`).
`AlgebraicGeometry.schemeDerived_mayerVietoris_naturality` was already proved on
arrival; it is not counted as work of this delivery.

## No longer needed

None. No imports or nodes were removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the three equations for `cU.hom`, `cV.hom`, and `cUV.hom`
choose comparison isomorphisms by `Classical.choice` applied to the proposition
`Nonempty (F ≅ G)`. Such a proposition does not characterize an isomorphism by
compatibility with units, restrictions, or localization. Its proof is irrelevant;
the witness used to prove `Nonempty` cannot be recovered from `Classical.choice`.
In particular, a theorem proved by constructing a canonical witness and then
returning `⟨witness⟩` does not give a canonical specification of the chosen data.
Natural isomorphisms can have nontrivial automorphisms, so uniqueness cannot be
assumed. In an additive category over a field of characteristic different from
two, both the identity and its negative are natural automorphisms of the identity
functor, whereas the square from the identity arrow to itself with components
identity and negative identity does not commute.

The exact loss occurs in
`Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`:
`AlgebraicGeometry.RingedSpace.exists_derivedModuleDirectImageComposition` returns
an isomorphism **and** its right-derived-unit equation; `derivedDirectImageComposition`
returns only `Nonempty` and discards that equation. The composition witness is not
specified by the theorem's resulting type. Likewise
`schemeDerivedDirectImage_openRestriction` returns only `Nonempty`; its docstring
calls the comparison canonical, but its signature does not specify that property.

The DAG's direct-image steps require that the displayed comparisons are the ones
realized by the chain-level restriction of the representative map `q`. That
identification is not supplied by the current choice expressions. A new theorem
asserting those squares for these unconstrained choices would assume the missing
canonical specification; I have not introduced such a theorem with `sorry`.
The existential freedom in the eight adjunction/boundary binders might conceivably
absorb some comparison automorphisms, so this delivery does **not** certify a
counterexample to the full scheme theorem or claim a Lean refutation. It records
a precise interface dispute requiring review before the prescribed reduction can
be certified as true.

Suggested repair: expose actual canonical scheme comparison constructions,
characterized by the right-derived units (the ringed-space composition theorem
already supplies the required characterization), and the explicit derived
open-restriction comparison with its computation equation. Replace the choice
expressions by those constructions. Do not weaken the triangle isomorphism or its
component identities. This requires an interface repair; none is attempted here.

Searches used the three prescribed `msearch.py` modes. LeanFinder returned generic
Mayer--Vietoris square and mapping-cone naturality results, no scheme direct-image
comparison theorem. Loogle found no `Triangle.isoMk`. Grep found Mathlib's
`DerivedCategory.triangleOfSESδ_naturality`, already used by the existing naturality
proof. Repository searches found no other implementation of the direct-image
clause. The generic triangulated-functor result proves preservation of
distinguishedness; it does not identify these chosen component isomorphisms.

Local compilation of the original module succeeded in 48.2 seconds. The dry run
of an unchanged module correctly rejected it as no progress; this delivery instead
uses the explicit statement-dispute path, with no claimed hole closure.

Earlier validation attempts (before this retry) failed with the 60-second local
compiler timeout, despite separate successful compiles. Nothing was pushed.

On this retry, inspection of the launcher showed that shared compiler-slot waiting
happens before the 60-second compiler timeout starts. The retry ultimately printed `OK (dry run)` for commit `27e53a4c27`: the module
compiled and passed preflight except for the second reading, which the second reader
writes. Nothing was pushed. Total command elapsed time alone did not establish a
compile timeout.
The comparison-interface dispute was independently checked against both current
comparison modules and the ringed-space unit-characterized composition theorem.
No full scheme counterexample or new proof is claimed.

## Second reading by C1

1. **Statements and accidental changes.** Compared the delivered module byte for
   byte with the repository version. The declarations of
   `schemeDerived_mayerVietoris_naturality` and
   `schemeDerived_mayerVietoris_directImage`, their imports, and all signatures
   are unchanged. The only change is the documented `STATEMENT-DISPUTED` comment
   before the pre-existing direct-image `sorry`. Verdict: pass.

2. **Proof and axioms.** Compiled the delivered module with the prescribed
   launcher; it compiled successfully. The naturality declaration has no new
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The sole
   remaining `sorry` is the named direct-image theorem, already recorded above.
   Verdict: pass for the proved declaration; the direct-image hole remains open.

3. **Statements and split-offs.** No statement was added or split off, so there
   are no new truth or strength obligations. The dispute is technically specific:
   the selected `Classical.choice` comparison isomorphisms are only witnesses of
   `Nonempty` and do not carry the unit/restriction equations needed by the
   direct-image triangle squares. Verdict: pass; the issue is correctly recorded
   as an interface dispute rather than hidden behind a new `sorry` theorem.

4. **Pruning and dependencies.** The naturality proof uses the existing imports
   and declarations, and no import or proof dependency became unused. The direct-
   image node remains split with its original route and proof dependencies. Verdict:
   pass; no pruning was available.

5. **Unit route and DAG agreement.** The unit `sk-thm-picard-semicon` route and
   the node `lem-pc-derived-mayer-vietoris-functorial` are unchanged. The DAG still
   records naturality as proved and direct-image functoriality as split, matching
   the Lean file. Verdict: pass.

Changed only the module's dispute comment and this second-reading report section;
no proof, statement, import, node, or definition was changed.
