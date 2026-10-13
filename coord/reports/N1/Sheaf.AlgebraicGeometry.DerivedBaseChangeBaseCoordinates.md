## What changed

Proved `AlgebraicGeometry.exists_derivedBaseChange_base_coordinates` by changing the
common codomain S first and the base-source Sprime second. The statement and its public
import are identical. The proof imports two new proved modules privately:
`Sheaf.AlgebraicGeometry.DerivedBaseChangeCodomainIso` and
`Sheaf.AlgebraicGeometry.DerivedBaseChangeDomainIso`.

Each new module proves one coordinate transport from the selected coherent pullback
comparisons and the pinned derived adjunctions. Proved private categorical lemmas handle
counit cancellation for the common-base change and the composite Hom equivalence for the
base-source change. Proved private coherence lemmas handle pullback associativity and
naturality of equality transports. The item then composes the two comparison isomorphisms
and substitutes their mate equations. The nodes follow these actual Lean proofs.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_derivedBaseChange_base_coordinates` (one of one holes).
No holes are added and no sorry remains in any delivered module.

The two new public theorems are also proved:

- `AlgebraicGeometry.exists_derivedBaseChange_codomain_iso`, node
  `lem-pc-derived-base-change-codomain-iso`.
- `AlgebraicGeometry.exists_derivedBaseChange_domain_iso`, node
  `lem-pc-derived-base-change-domain-iso`.

These proofs depend on existing declarations from the library; this does not assert that
their transitive dependencies are all free of sorry. The existing pinned mate definition
and derived-pullback composition structure are used without alteration. No data definition,
axiom, or arbitrary witness choice was introduced.

Both new statements retain arbitrary commutative squares, arbitrary unbounded derived
objects, and the same universes. Identity isomorphisms, empty schemes and zero objects
were checked in the argument: every step is an adjunction identity, naturality or
composition coherence and excludes none of these cases. The common-base proof constructs
an equivalence from actual c and i comparisons and adjointifies it; the base-source proof
uses the actual pinned adjunction for e.inv and its invertible unit.

## No longer needed

No import was removed. The old direct proof-dependency entries
`def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition` are replaced in the parent node
by the two coordinate lemmas; both old nodes remain used through those lemmas.
No existing node or module is pruned: the canonical mate definition
and its derived-pullback composition infrastructure remain necessary, through the two new
proved lemmas. The original simultaneous two-coordinate calculation is replaced by two
one-coordinate calculations and elementary composition; no unit step is bypassed.
The unit record has no realized node attached to this technical coordinate law, and the
higher Picard route is unchanged.

The separate derived-direct-image composition modules, the upper-left-coordinate
transport module and their associated nodes are not used by this proof. They were not
imports or dependencies of this item, so this is not counted as pruning them from the
project. Both direct-image comparisons needed here are constructed as right-adjoint mates
using Mathlib's conjugateIsoEquiv.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The parent proof plan describes the simultaneous mate comparison;
the proof uses two coordinate calculations instead. Mathlib's mate and right-adjoint
uniqueness infrastructure is sufficient together with the stated canonical composition
coherence; no new unproved theory is required.

The local Stacks source is absent on this machine; read the actual online statements at
Tags 08HY, 0D5S and 0D5T. LeanSearch returned Internal Server Error; LeanFinder, Loogle
and source grep were available. The expensive step in trial elaboration was matching
selected derived-pullback comparisons. Making the coherence calculation a proved private
lemma with a generic comparison parameter avoids unfolding those constructions. No tool
was bypassed or edited, and no existing definition was changed.

## New nodes

`lem-pc-derived-base-change-codomain-iso` is proved in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeCodomainIso`. It changes only the common
codomain, with fprime and gprime fixed. It constructs the source comparison from an
explicit coordinate equivalence and its invertible counit, then compares the transposes
under the unchanged fprime adjunction. The two private lemmas are fully proved.

`lem-pc-derived-base-change-domain-iso` is proved in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeDomainIso`. It changes only Sprime, with f
fixed. It constructs b by conjugating the comparison for fB followed by e.inv, and a
by inserting the pinned adj e.inv unit before applying c e.inv g. Naturality and the
composite Hom equivalence prove the equation. The two private lemmas are fully proved.

Each node records its source, complete proof in words, verbatim Lean statement, parent
blueprint ancestry and searches. No change record is needed: no existing statement,
definition, visibility or public import was changed, and no downstream module was adapted.

## Second reading by N1

1. **Interface preservation — pass.** I diffed the existing base-coordinate module against
   the repository version. Only its proof body and two plain proof imports changed;
   its existing docstring, universes, visibility, parameters, and theorem signature
   are byte-for-byte unchanged. No existing definition, statement, public import,
   or downstream module is changed. Each of the three node `lean.statement` fields
   matches its Lean signature verbatim.

2. **Proof and axioms — pass.** All three modules compile cleanly through `lcompile.py
   --all` (44.5, 52.7, and 3.7 seconds). A scratch copy with `#print axioms` for
   `exists_derivedBaseChange_base_coordinates`,
   `exists_derivedBaseChange_codomain_iso`, and
   `exists_derivedBaseChange_domain_iso` prints exactly `propext`, `Classical.choice`,
   and `Quot.sound` for each. No delivered module contains `sorry`, forbidden
   declarations, hollow definitions, or kernel-check bypasses. I read the generic
   private transport proofs: the codomain proof uses `conjugateEquiv_counit` to
   cancel the inserted inverse counit after moving it by naturality; the domain
   proof uses `Adjunction.comp_homEquiv` and Hom-equivalence naturality to identify
   the mate with the inserted unit followed by direct image. The square comparison
   helpers derive their equations from the selected associativity law and
   `eqToHom_naturality`. Both final proofs unfold the very same selected comparisons
   and pinned adjunctions as `schemeDerivedBaseChangeMap`, rather than substituting
   other adjunction choices. The axiom check also establishes that these choices
   depend on proved infrastructure in the compiled library, not unproved existence.

3. **New statements and searches — pass.** Neither new theorem is left open; there
   are zero split-off holes. The two proved public lemmas are strictly restricted
   coordinate transports, not the target under another name. I checked every
   parameter against their node statements: all schemes and unbounded objects
   remain arbitrary, the original and transported square equalities are present,
   and no cartesian or flatness assumption is added. For identity coordinates the
   constructions reduce to equivalence units/counits and comparison isomorphisms;
   for empty schemes or zero objects the same categorical identities apply, with
   no inhabitance or nonzero assumption. I independently read Stacks Tags
   [08HY](https://stacks.math.columbia.edu/tag/08HY),
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
   [0D5T](https://stacks.math.columbia.edu/tag/0D5T): these supply respectively the
   unrestricted counit mate description, pullback composition, and right-adjoint
   composition argument. The transport argument is explicitly marked agent-written.
   Independent LeanFinder search for right-adjoint comparison preserving transposes
   found `comp_homEquiv`, naturality, and right-adjoint uniqueness infrastructure;
   Loogle confirmed `conjugateEquiv_counit`, already used here. Source searches of
   Mathlib and `lean/Sheaf`/`lean/WeilConjectures` found no duplicate scheme-coordinate
   transport or immediate replacement. No shorter complete route was found.

4. **Top-down proof, imports, and unit — pass.** The original hole is closed by
   first changing S, then Sprime, then composing the comparison isomorphisms.
   Both new lemmas are used, and their proof imports supply mate conjugation and
   the invertible-unit instance respectively. All proof-only imports are plain
   imports; each public import supplies notions in the public statement. The old
   parent proof dependencies `def-pc-derived-base-change-map` and
   `lem-pc-ringed-spaces-derived-pullback-composition` remain required through the
   two new nodes; none is pruned from the import closure. I checked
   `dag/units/sk-thm-picard-f-representable.json`: its realized statement and sole
   step have empty attachment lists, and this delivery changes neither that
   record nor the Picard chapter/unit route. No unit step is bypassed.

5. **DAG consistency — pass.** The parent proof records the actual calls to the
   codomain and domain lemmas followed by elementary composition. The new nodes
   record the explicit equivalences, conjugate comparison isomorphisms, square
   coherence calculations, and Hom-transpose identities of their code. Each
   `proof_deps` is exactly the union of its proof steps' `uses`; the new nodes
   include source, ancestry, chapter/unit, created/Lean records, and all three
   search kinds. No existing node field outside `proof`, `proof_deps`, and
   `proof_origin` changed.

Second reading changed the pruning report to explicitly name the two old direct
proof dependencies that remain needed transitively, and added this independent
review. No Lean proof or statement needed repair. One original hole is closed,
zero holes are added, and two additional public transport theorems are fully proved.
