## What changed

Proved `AlgebraicGeometry.IsCurve.assertions_iff_of_prime_biproduct_iso`, preserving its
signature and docstring. The proof first establishes constructibility of H using the
existing `Scheme.IsConstructibleSheaf.biproduct` and `Scheme.IsConstructibleSheaf.of_iso`
theorems. It proves `r • 𝟙 (⨁ G) = 0` by biproduct injection extensionality, then transports
annihilation to H by cancelling the isomorphism. These are real Lean proofs, including
for an empty family.

The remaining comparison argument is split into three new modules: unconditional
C1/C2/C5/C7/C8, primary C3, and invertible-order C4/C6. These have strictly smaller
conclusions than the item and receive the already-proved constructibility/annihilation
facts they need. The unconditional statement does not require any prime annihilator.
The item combines their two directions using `assertions_iff`, extracts the individual
component fields, and rebuilds all eight assertion fields in both directions. All four
modules compile cleanly with lcompile.py. Imports added are proof-only.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.assertions_iff_of_prime_biproduct_iso`; the item has no
remaining sorry. This proof is a reduction and still depends on the following three
named theorems, each in its own module, with source and complete proof in its docstring:

- `AlgebraicGeometry.IsCurve.prime_biproduct_unconditional_iff`
  (`lem-pbc-f1-prime-biproduct-unconditional`).
- `AlgebraicGeometry.IsCurve.prime_biproduct_primary_iff`
  (`lem-pbc-f1-prime-biproduct-primary`).
- `AlgebraicGeometry.IsCurve.prime_biproduct_invertible_iff`
  (`lem-pbc-f1-prime-biproduct-invertible`).

Edge cases checked against the informal argument: empty index (zero sheaf and vacuous
right side), a singleton (transport by the coefficient isomorphism), zero coefficient
ring (every coefficient module is zero), characteristic zero (r invertible),
characteristic r (primary automatic; invertible-order exception forces zero), and
positive characteristic different from r (different-primary exception forces zero).
In the latter two exceptional cases Bezout is applied elementwise to r and the other
annihilator; this does not assume a uniform exponent or uniform torsion bound.

## No longer needed

No existing import was removed: the original public import of Assertions is required
by the signature. All four added imports of the assembly module are proof-only and used.

The old direct `proof_deps` absent from the new assembly proof are:

- `def-weil-pbc-etale-cohomology`: removed from this reduction and from all three new
  obligations. Its recorded declaration is derived global sections, whereas the
  predicates use Mathlib's Ext-based `Sheaf.H`. Additivity of `Sheaf.functorH` and
  `Abelian.Ext.addEquivBiproduct` supply the relevant shorter route; no bridge is needed.
- `def-weil-pbc-primary-torsion`: used below in the primary and invertible obligations.
- `lem-weil-pbc-cohomology-pullback-functorial`: used below in the unconditional and
  invertible obligations, through coefficient naturality (also available directly as
  the upstream `Etale.cohomologyMap_map`).
- `lemma-weil-pbc-geometric-stalk-conservative`: used below only in the primary and
  invertible obligations to identify exceptional sheaves as zero.

The second reading additionally removed copied primary-torsion and stalk-conservativity
edges from the unconditional obligation, and constructibility and pullback-functoriality
edges from the primary obligation. None of these removals claims that a module is globally
unreachable: they describe the route of this delivery. No unit-realizing node was removed.

## Where the brief, the DAG or earlier work was wrong

The node's listed dependencies supply definitions, naturality and conservativity but
no theorem directly relating the eight conditional predicates to finite biproducts.
Reading their signatures confirms the missing glue is a real finite-sum comparison
and the exceptional torsion cases, rather than simply applying one of the listed
lemmas. The unchanged node already describes those details. The new obligations make
three parts independently available to stage-3 workers. No target or existing
statement was changed, and no unit step was bypassed: this item is below the unit's
realized nodes and still follows its finite-sum devissage argument.

The cited local literature files are absent on this machine. The primary texts were
read at https://stacks.math.columbia.edu/tag/03SC and
https://stacks.math.columbia.edu/tag/0A5C. The all-schemes/common-prime conditional
comparison is the parent node's agent expansion of that source argument, not a claim
that these Stacks tags state the new generalized lemmas verbatim. LeanFinder, Loogle,
and Mathlib grep searches were run and recorded; LeanSearch returned Internal Server
Error, which is recorded as unavailable rather than as evidence of absence. Local
library searches found no applicable bundled theorem; importing Reductions would
create a cycle through the present item.

## New nodes

`lem-pbc-f1-prime-biproduct-unconditional` isolates componentwise cohomological vanishing,
finiteness, bijectivity and surjectivity for C1/C2/C5/C7/C8, assuming constructibility on
both sides and no common-prime hypothesis.

`lem-pbc-f1-prime-biproduct-primary` isolates only C3. It assumes the common prime kills
H and all components; the item proves the H hypothesis. Its argument distinguishes
characteristic r from distinct-prime stalks, which must vanish by Bezout.

`lem-pbc-f1-prime-biproduct-invertible` isolates only C4/C6. It assumes constructibility
and common-prime annihilation on both sides; the item establishes these for H. Its
argument distinguishes invertible r from characteristic r with zero exceptional stalks.

Each node is in `dag/nodes/sec-proper-base-change/`, and the original node's proof,
proof_deps and proof_origin now match the Lean assembly. There are no change records
because no existing signature or definition was changed.

## Second reading by F1

1. Compared the sole existing module to the repository with `diff -u`. Its complete
   theorem signature and its existing docstring are byte for byte unchanged; only four
   plain imports and the proof body were added. There are no definition changes and
   no change records. The existing node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Each of the three new modules declares exactly the theorem recorded
   verbatim in its corresponding new node. Verdict: no accidental public API change.

2. Independently compiled all four files with `lcompile.py --all`: clean, about four
   seconds each. Read the constructibility proof, injection extensionality calculation,
   cancellation across e, and all eight conjunction projections in both directions.
   They typecheck and do not change any conditional hypothesis. Scratch copies with
   `#print axioms` for each of the four declarations returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Scanned every delivered Lean file:
   the only three sorries are the named split theorems, each exactly `:= by sorry`;
   there is no definition, axiom, unsafe/opaque declaration, extern, or implemented_by.
   Verdict: a checked reduction, with three explicit open obligations, not an
   axiom-free completion of the mathematics.

3. Read the three statements and their proof docstrings against all eight predicate
   definitions in Assertions. The unconditional node covers only C1/C2/C5/C7/C8 and
   needs no prime; the primary node covers only C3 and needs no constructibility;
   the invertible node covers only C4/C6. Each is strictly a part of the item, and
   the item genuinely derives constructibility and the H-annihilator before applying
   them. Reviewed the primary texts at [Stacks 03SC](https://stacks.math.columbia.edu/tag/03SC)
   and [Stacks 0A5C](https://stacks.math.columbia.edu/tag/0A5C). These supply the finite-sum
   devissage context, not verbatim all-scheme equivalences: the latter follow by
   the additive argument stated here and do not require curve or algebraic-closedness
   hypotheses. Checked empty and singleton families, zero coefficient ring, empty X,
   characteristic zero, characteristic r, and a different positive characteristic.
   In characteristic r all r-killed stalks are primary (exponent one); invertible-order
   r-killed stalks vanish by Bezout. For p different from r, a p-primary r-killed
   stalk vanishes elementwise using coprimality of r and p^n; no uniform exponent is
   assumed. In characteristic zero C3 has no prime characteristic to test, and r
   is invertible. In the empty cases the zero sheaf has zero cohomology, so every
   comparison is between zero groups and the right quantifier is vacuous.
   Independently searched the current and upstream curve modules with different
   words (`IsPrimaryTorsionSheaf`, retracts, coefficient isomorphisms, and additive Ext).
   `msearch.py` LeanFinder found additive Ext infrastructure; grep found
   `Abelian.Ext.addEquivBiproduct` in Mathlib. Loogle could not resolve that short name,
   so its response is not evidence of absence. No bundled obligation was found.
   `assertions_of_isIso_comp` uses CurveCoefficientPair and algebraically closed k;
   `Assertions.of_shortExact` has curve hypotheses and Reductions imports the item;
   neither proves these all-scheme statements. Verdict: the obligations are true,
   sourced, genuinely smaller, and not duplicates of those existing declarations.

4. Read sk-thm-p1's `realized` statement and all four step lists, and the parent's
   finite-sum route. This item and the three helpers are below the unit's realized
   nodes; the curve calculations, Kummer route, strict henselian comparison and
   separably closed invariance steps remain in place. Every import of the assembly
   module is used and all new modules' public Assertions import is needed for their
   signatures. The Ext-based route avoids a derived-cohomology bridge. Corrected
   `No longer needed` to enumerate all four old direct dependencies absent from the
   assembly, distinguishing removal from relocation below a split. Verdict: route
   preserved, local pruning made explicit; no globally pruned module claimed.

5. Checked the original node's two proof steps against the actual Lean body and each
   new node's signature, statement dependencies, source, blueprint ancestor, chapter,
   unit, created record, searches, and Lean record. Checked that `proof_deps` is the
   union of step uses. Found copied edges: derived cohomology in every new node,
   primary torsion and stalk conservativity in the unconditional node, constructibility
   and pullback functoriality in the primary node. Removed those irrelevant edges and
   made the Ext-based argument explicit in each plan and docstring. Verdict: records
   now describe the intended argument without those unrelated obligations.

Changed in this second reading: only the three new proof docstrings and node proof plans/
dependencies, plus this report's pruning account and review. The existing Lean proof,
all signatures, definitions, sources, and unit records were preserved. The remaining
three obligations require development of the componentwise cohomology and exceptional
stalk arguments; none is a short direct application of a bundled existing theorem.
