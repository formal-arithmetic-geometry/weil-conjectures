## What changed

The existing declaration `AlgebraicGeometry.formalFunctions_finite_quotient_comparison`
keeps its signature, visibility and docstring verbatim. Its proof obtains a canonical
quotient-system isomorphism and pullback maps, then applies the finite pullback germ
lemma at each level. Both new proof imports are plain `import`.

Repaired the two new split statements. `FormalFunctionsFiniteQuotientIso` now asserts
existence of b and r with both the quotient factorization and the canonical pullback
formula; it asserts no Theta property. `FormalFunctionsFiniteQuotientMaps` now proves
Theta for one level from that formula and the local germ condition, without an
isomorphism or a quotient system. Removed the spurious `True` existential component.

Added `FormalFunctionsFinitePullback`, reusing the explicit construction from the first
worker's scratch file: pullback.lift defines the finite immersion into X'; its projection
equality is proved; the pinned tensor adjunction defines its h-map; the existing
moduleCohomologyFMap defines its additive cohomology pullback. There is no hole in any
new definition. The choices of adjunction use exists_tensorPullbackAdjunction, whose
statement pins its unit sectionwise and therefore its Hom equivalence. This is not
an arbitrary witness of mere existence.

Updated the existing node's proof, proof_deps and proof_origin; repaired the new nodes'
statements, verbatim Lean records, proofs, searches, dependencies, provenance and unit
(sk-thm-p1, rather than the nonexistent unit-weil-pbc-formal-functions). No existing
statement or definition changes. The change record is
`coord/changes/formal-functions-finite-quotient-split.md`.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.formalFunctions_finite_quotient_comparison`
(node `lem-weil-pbc-formal-functions-finite-quotient-comparison`).
The item itself contains no sorry. This is a decomposition, not a complete proof.

Added two holes, each the whole proof of a public named theorem:

- `AlgebraicGeometry.formalFunctions_finite_quotient_iso`, node
  `lem-weil-pbc-formal-functions-finite-quotient-iso`.
- `AlgebraicGeometry.formalFunctions_finite_quotient_maps`, node
  `lem-weil-pbc-formal-functions-finite-quotient-maps`.

The new projection identity `AlgebraicGeometry.formalFunctionsFiniteι_snd` is fully
proved by pullback.lift_snd. The three new definitions contain real constructions.
No other holes are added. Locally, one original hole closed minus two added is -1;
no positive ledger progress is claimed. The target theorem still depends on sorryAx.

All four delivered modules compile with no warnings through lcompile.py. Scratch
copies printed axioms for every delivered declaration. The finite immersion, its
projection theorem and its h-map use only propext, Classical.choice and Quot.sound.
The additive cohomology pullback additionally uses sorryAx from existing cohomology
infrastructure. The two split theorems and the composed item use only those same
three standard axioms and sorryAx. No axiom, unsafe, opaque, implemented_by, extern,
explicit sorryAx or kernel-check bypass appears in delivered source.

## No longer needed

No modules are pruned and no existing public imports are removed or privatized.
The original FormalFunctionsLocalStalkComparison, CoherentFormalModule and ideal-sheaf
imports are retained for the unchanged signature. The first worker's additional public
proof import was replaced by two plain imports; the existing public API is unchanged.

Every original direct proof dependency listed below is no longer a direct dependency
of the item's composed proof. They remain part of the canonical construction or of
the two split arguments, so none is claimed globally unnecessary:

- `def-nagata-extended-ideal`
- `def-pc-fibre-product`
- `def-pc-module-pullback`
- `def-weil-pbc-coherent-formal-module`
- `def-weil-pbc-module-cohomology-fmap`
- `lem-weil-pbc-affine-morphism-cohomology-edge`
- `lem-weil-pbc-closed-immersion-unit-quotient`
- `lem-weil-pbc-module-cohomology-fmap-basic-properties`
- `lem-weil-pbc-module-cohomology-fmap-functorial`
- `lem-weil-pbc-module-pullback-quasi-coherent`
- `lem-weil-pbc-quotient-base-change-closed-immersion-ideal`
- `pqf-def-affine-morphism`

The new direct proof_deps are exactly the two split lemma nodes. The quotient-system
node retains the original geometric, quotient, affine edge and naturality route.
The germ node retains the h-map composition/restriction route and adds the existing
open-choice existence and local-spectrum properties needed to instantiate its local
germ hypothesis. The canonical definition node records the explicit h-map construction.
The realized unit nodes in dag/units/sk-thm-p1.json remain untouched.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (first worker's discarded, uncommitted maps signature): requiring
Theta compatibility for every system isomorphism b is false. Take f=id on Spec Q,
F=O and p=0. The maximal ideal is zero, all finite levels identify with Q and the
quotient projections are identities. Multiplication by -1 at every level is a natural
system isomorphism. Its prescribed r sends 1 to -1, while Theta requires the pullback
of the germ of 1 to be 1. The new maps lemma no longer quantifies over b; canonical
pullback is specified independently and enforced by the new iso lemma.

The first worker's two node files had empty dependencies and generic proof sketches,
a nonexistent unit and invalid blueprint provenance, and their searches did not give
an adequate independent reading. The existing node did not record the actual Lean
proof. All were corrected. The report had overstated pruning by calling the local
comparison import unnecessary, although the statement still needs its definitions.

Independent searches used msearch.py with new semantic queries, a Loogle pullback
pattern, and two source-grep patterns. LeanSearch was unavailable (HTTP internal
server error), recorded without claiming a search verdict. LeanFinder found scheme
quotient/pullback facts and ordinary presheaf germ identities; these do not prove
higher cohomology quotient identification or the derived germ formula. Loogle found
pullback.lift_snd, used for the projection identity. Searches of lean/ and the upstream
checkout found the existing h-map functoriality and open-choice machinery, but no
statement already supplying either new specialized comparison.

Stacks Tags 02OD, 089W and 01FB were read from their official web pages because this
read-only clone lacks literature/stacks-project/coherent.tex. The node proofs mark the
expanded argument as agent-written and cite those precise pages; no chapter or unit
route is changed.

## New nodes

`def-weil-pbc-formal-functions-finite-pullback` records the explicit finite immersion,
its proved projection equation, the adjunction-pinned h-map and its additive
cohomology pullback in `Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback`.
Its Lean record includes the four construction declarations.

`lem-weil-pbc-formal-functions-finite-quotient-iso` records only the canonical
quotient-system isomorphism and the two formulas for its finite pullback maps.
Its docstring and node expand the closed-immersion, scalar and naturality arguments.

`lem-weil-pbc-formal-functions-finite-quotient-maps` records the one-level germ
compatibility for a map whose underlying function is canonical finite pullback.
Its docstring and node specify local open choices, equality of the germ
representatives, the unit square and cohomology composition/restriction.

Change record: `coord/changes/formal-functions-finite-quotient-split.md`.

## Second reading by P3

1. Compared the delivered item with the repository using diff and parsed declaration
   tables. Verdict: the existing statement is byte-for-byte identical, including every
   hypothesis, let binding, existential and both compatibility conclusions; visibility
   and docstring are also identical. Only its proof and two private proof imports change.
   The other modules contain new declarations, recorded in the change record.
2. Compiled all four modules in import order using lcompile.py, then compiled scratch
   copies with #print axioms for every declaration. Verdict: clean compilation;
   exactly two named public whole-proof sorries; no hollow definitions or forbidden
   constructs. The allowed standard axioms and the remaining sorryAx are listed above.
3. Read the split statements from the top down and tested degree zero over a field,
   level n=0, arbitrary n, zero coefficients, and empty fibre. Verdict: the original
   arbitrary-b maps statement is false, repaired as documented above. In the repaired
   field case b and r are the canonical identity maps, and the germ lemma is composition
   of section pullbacks. Zero coefficients or an empty fibre give zero maps; no map is
   required to be surjective. Both new statements are true and strictly smaller parts
   of the argument: the iso lemma has no Theta or a, the germ lemma has no b or quotient
   system. Read their full docstring/node proofs and repeated independent Mathlib,
   upstream and library searches; no duplicate comparison was found.
4. Checked existing imports, original proof_deps and the realized fields of sk-thm-p1.
   Verdict: this is a reduction below the unit level along the existing formal-functions
   route, not a unit bypass. No pruning or complete-proof progress is claimed. All old
   direct proof dependencies are accounted for above and retained by the lower arguments.
   New signatures use public imports; new proof dependencies use plain imports.
5. Read all four delivered node files against their Lean declarations. Verdict:
   parent proof_deps are exactly the two applied lemmas; new proof_deps equal the union
   of each proof's uses; referenced ids exist; new signatures in lean.statement match
   Lean; all nodes have the parent's chapter and unit, correct blueprint ancestor/via,
   recorded searches and sources. No existing node statement, stmt_deps, unit record
   or target changes. The canonical construction's data is explicit; the adjunction
   existence theorem determines the unit used downstream.

Changes made by the second reader: replaced the false arbitrary-isomorphism split with
canonical pullback factorization plus one-level germ compatibility; added the explicit
pullback construction module and node; fixed proof imports, natural-language proofs,
node metadata and parent proof records; replaced the inaccurate report and change record.
