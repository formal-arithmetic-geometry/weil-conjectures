## What changed

The unchanged theorem `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction`
is assembled from existence and uniqueness, in two new proof-only imported modules.
The first reader's assembly is retained. The second reader supplied the missing DAG
nodes and complete localization arguments in the two new theorem docstrings.
No existing definition, declaration signature, visibility or public import changed.
Removed the unused proof-only import
`Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`.
The sandbox's byte-identical copy of the relation module was removed from the delivery.

## Proved and sorry left

Hole closed in the item's module:
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction`.
Its proof still depends on the two open declarations below; it is not sorry-free.

Holes added, each with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction_exists`,
  node `new-lem-sbc-etale-triples-prime-localization-cocone-restriction-exists`.
- `AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_cocone_restriction_unique`,
  node `new-lem-sbc-etale-triples-prime-localization-cocone-restriction-unique`.

This is a decomposition: one upper hole closed, two strictly smaller holes added.
The local net is minus one hole before any effect of import pruning. No claim of
positive ledger progress or a completed mathematical proof is made.

## No longer needed

Removed import `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`:
the Lean assembly uses neither its theorem nor its instances. This module is not
claimed to be globally unreachable; other consumers may still need it.
The original node's `proof_deps` was empty, so no old proof-dependency node is omitted.
No unit realization or chapter route is removed.

## Where the brief, the DAG or earlier work was wrong

The first report claimed that the split-off statements had nodes, but neither node
file was present. The original node's proof and empty `proof_deps` also did not
describe the actual Lean assembly. Both discrepancies were repaired.
The uniqueness docstring's claim about jointly conservative maps was unnecessary
and misleading: compatibility directly identifies both legs with one composite;
no injectivity or cancellation of a localization map is involved.
The original target plan contains no declared construction of a localized pointed
triple. Closing either remaining hole requires formalizing that construction, not
just invoking a generic extensionality lemma. No short closure was found.

## New nodes

`new-lem-sbc-etale-triples-prime-localization-cocone-restriction-exists` isolates
construction of the natural compatible cocone, without asserting uniqueness.

`new-lem-sbc-etale-triples-prime-localization-cocone-restriction-unique` asserts only
equality of two already compatible cocones, without constructing a cocone.

Both inherit the chapter and unit of the parent, carry verbatim Lean signatures,
record searches, and state complete natural-language proofs. The original node
now names these two nodes as the exact dependencies of its assembly.
No change record is needed: no existing statement or definition changed.

## Second reading by S4

1. **Unchanged interfaces: pass.** Compared the two existing sandbox modules by
   `diff` against the repository. The relation module was byte-identical; the item
   differed only in proof-only imports and its proof body. The existing theorem
   signature and docstring remain byte for byte unchanged. There are no adaptations.
2. **Proof and axioms: pass as a decomposition.** All delivered modules compile
   using `lcompile.py`. The item has no `sorry`; the only two new holes are the named
   public existence and uniqueness theorems. No axiom, unsafe, opaque, extern,
   implemented_by or hollow definition was added. Scratch `#print axioms` checks
   cover all three theorem declarations; the main theorem has only the standard
   axioms and `sorryAx`, and both split statements likewise have only the standard axioms and `sorryAx`.
3. **Split statements: pass.** Existence and uniqueness are proper separate parts
   of the argument, neither a renaming of the full ExistsUnique assertion. Their
   mathematical arguments work for arbitrary K, with no separable-closure assumption.
   The kernel of the specified A-pointing is q by hψ and injectivity of ψ; hK ensures
   denominators outside p are nonzero in K. No arbitrary object is defined from an
   unproved existence theorem. Checked the field/identity-localization case, the
   identity global triple, and the zero target ring V; a zero base ring has no p.
   The proof never assumes the localization map of B is injective, so torsion and
   zero divisors do not invalidate it. Each hole has its node and complete docstring.
   Fresh LeanFinder, Loogle, Mathlib grep and project-source searches found no direct
   replacement; LeanSearch was unavailable (Internal Server Error), recorded as such.
4. **Route and pruning: pass.** The retained proof uses the two parts of the original
   localization route. The only discarded import is the unused localization-colimit
   theorem, and there were no old proof-dependency nodes. The unit
   `sk-prop-input-spreading` and its `realized` fields are untouched; this auxiliary
   node is not one of the unit's realized bindings (the existing bindings are empty).
5. **Lean/DAG agreement: repaired, now pass.** Added the missing nodes with all
   stage-3 fields and replaced the parent's stale proof metadata by its actual
   existence/uniqueness assembly, with matching `proof_deps` and `proof_origin`.

Second reading changed: removed one unused import and one redundant delivered copy;
expanded the two new docstrings; supplied two missing nodes; corrected the parent's
proof metadata and the report's hole accounting. The main proof was left intact.

Sources checked: [Stacks 04GW](https://stacks.math.columbia.edu/tag/04GW),
[localization universal property](https://stacks.math.columbia.edu/tag/00CM),
and [etale base change, 00U2 (3)](https://stacks.math.columbia.edu/tag/00U2).
The auxiliary cocone arguments are explicit consequences of these facts, not
verbatim theorems asserted by those tags. Tag 00CR describes principal-localization
colimits and is not used by this assembly.
