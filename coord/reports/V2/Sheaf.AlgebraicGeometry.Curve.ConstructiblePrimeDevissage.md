## What changed

Proved `AlgebraicGeometry.IsCurve.assertions_of_constructible_prime_devissage` in
`Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage` without changing its signature.
The proof obtains a finite extension tree, inducts on it, applies the given prime-field
hypothesis at each leaf, transports the eight conditional assertions across the underlying
abelian sheaf isomorphism, and applies short-exact devissage at each extension.

Added four modules, each recorded by its own new node:

- `PrimeFieldFiltration`: the actual inductive predicate recording finite extension trees.
  Its constructors mention constructible prime factors and short exact sequences, with no
  cohomological condition. It has no postponed data or proofs.
- `ConstructiblePrimeFieldFiltration`: the remaining finite-coefficient structural theorem.
- `UnderlyingAbelianAssertions`: proved scalar transport directly using stalk additive
  equivalences, cohomology equivalences, and naturality of comparison maps. The local cohomology
  conjugation helpers reuse the proved argument from group K1's
  `ReducedConstantLowerShriekAssertions`; they are generalized to an abelian-sheaf isomorphism
  between two different coefficient rings. The stalk comparisons are newly written here.
- `ConstructibleShortExactAssertions`: proved a standalone specialization of the existing
  `Curve.Reductions.Assertions.of_shortExact` proof. Both outer terms are assumed
  constructible, so its Noetherian subobject argument is unnecessary. The exactness,
  finiteness and comparison diagram chases reuse the existing proved source text; the
  public theorem has a fresh name and the extra constructibility hypotheses. All reused
  theorem-shaped helpers are local to its proof, avoiding duplicate top-level statements. No existing
  module is relocated, adapted, or restated with a postponed proof.

The item's three new imports are proof-only. The original public import remains. The
original node's proof, proof dependencies and proof origin follow the actual induction.
No target statement, definition used by a target, or existing public interface was changed.

## Proved and sorry left

The item's sole original sorry is closed:
`AlgebraicGeometry.IsCurve.assertions_of_constructible_prime_devissage`
(`lem-weil-pbc-constructible-prime-module-devissage`).

Also proved:

- `AlgebraicGeometry.IsCurve.assertions_of_underlying_abelian_iso`
  (`lem-v2-underlying-abelian-assertions`), including transfer of primary and invertible-order
  torsion through the stalk isomorphisms. No curve or algebraic closedness assumption is
  needed for this transport.
- `AlgebraicGeometry.IsCurve.Assertions.of_constructible_shortExact`
  (`lem-v2-constructible-short-exact-assertions`), including the degree-zero injectivity case,
  the positive-degree boundary corrections, and the C8 use of H3 vanishing.

Exactly one direct sorry is left in this delivery:
`AlgebraicGeometry.Scheme.constructible_hasPrimeFieldFiltration`
(`lem-v2-constructible-prime-field-filtration`), whose whole proof is `by sorry` and whose
theorem docstring contains the complete finite-annihilator/primary decomposition argument.
This is a strictly structural part of the argument: it has no field, curve, reducedness,
prime-field assertion hypothesis, cohomology, or conclusion about the eight assertions.
The new `HasPrimeFieldFiltration` definition is fully implemented as an inductive predicate.

All five modules compiled together in import order using the prescribed `lcompile.py`.
The existing long-exact-ladder dependency may still carry postponed proofs; this delivery
uses that named library statement as permitted by stage 3 and adds no duplicate of it.
The delivery dry run additionally checks local axiom probes and server compilation.

Edge cases checked mathematically: a zero sheaf is a prime leaf represented by the zero
F_2-sheaf, including the zero coefficient ring (additive order of 1 equals 1) and an empty
scheme. The filtration theorem does not demand positive dimension or connectedness.
The characteristic equal to the factor prime causes no missing case: primary and
invertible-order conditions are transported exactly, and the short-exact proof obtains
those conditions on the outer stalks directly. Finite rings guarantee a positive common
annihilator independently of the size or number of sections of the sheaf.

## No longer needed

No existing import was removed from the original module; its public Assertions import is
needed by its unchanged signature. Every new proof import is used by the induction.
There is no claim that an entire module becomes unreachable from all other targets.

For this item's proof, `lemma-weil-pbc-eight-curve-devissage` as realized by
`WeilConjectures.AlgebraicGeometry.Curve.Reductions` is not imported: its proved argument is
specialized in the standalone module. Consequently this proof does not pull in the
unrelated reduced-curve, dense-open, normalization and filtered-colimit reduction imports
of that module. The unrestricted constructible-subobject lemma
`lem-weil-pbc-constructible-module-subobject-noetherian` and its module
`Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian` are not needed on this path,
since the filtration records constructibility of the two outer terms explicitly.

The other original planned dependencies are still needed below the new structural and
transport lemmas: `thm-constructible-serre`, `def-weil-pbc-primary-torsion`, and
`def-constructible-finite-locally-constant`. They are not pruned. All unit statements and
steps realized in `dag/units/sk-thm-p1.json` are retained; the change is within this node's
finite-coefficient devissage step.

## Where the brief, the DAG or earlier work was wrong

The later landing checker scans duplicate statements even in private declarations. The
reused comparison and exact-sequence helpers are therefore scoped locally inside the two
new public proofs, rather than added as redundant top-level private lemmas.

The recorded dependency `Assertions.of_shortExact` is usable mathematically but cannot be
imported from its recorded module: `Curve.Reductions` imports this item already, making an
import cycle. Rather than changing that shared module, the delivery provides and proves
the constructible-outer-term specialization, with the source proof's existing exactness
and diagram chases. This is why a new proved short-exact module is necessary despite the
existence of the more general theorem. Its omitted Noetherian hypothesis was used only
to establish constructibility of arbitrary outer subobjects, which is assumed here.

The new nodes do not replace the item by a renamed or repackaged cohomological statement.
The remaining theorem constructs finite extension trees; the original proof genuinely
combines the independently proved transport and extension steps by induction.

The original node has no usable blueprint ancestor recorded (`blueprint.from.node = null`);
`blueprint_refs.py ancestor` reports this explicitly. New records point to the existing
blueprint short-exact lemma and explain their use in 03SC's second proof paragraph.
Blueprint searches for prime filtration, devissage and scalar changes found no exact
alternative node. Broader filtration/scalar searches gave unrelated Weil-module and
adic-coefficient statements, not this finite-coefficient reduction.

Searches were run with msearch (LeanFinder, Loogle, grep, and LeanSearch). LeanSearch returned
an Internal Server Error, recorded as unavailable. LeanFinder returned generic condensed
module constructions or formally etale algebra statements, not this reduction. Local
searches found the existing short-exact proof and K1's same-ring isomorphism helpers;
both were read and reused. The standalone modules do not import their enclosing files,
which would add irrelevant reductions or create an import cycle.

The cited Stacks sources were read online because the repository's named tex file is
absent on this machine: [03SC](https://stacks.math.columbia.edu/tag/03SC), second proof
paragraph; [0A5C](https://stacks.math.columbia.edu/tag/0A5C), extension devissage; and
[03RZ](https://stacks.math.columbia.edu/tag/03RZ), constructible weak Serre closure.

## Second reading by V2

1. Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-only imports and the proof body differ. Verdict: pass.

2. Compiled all five delivered modules with the prescribed `lcompile.py`; compilation succeeds. The only remaining `sorry` is the named structural theorem `Scheme.constructible_hasPrimeFieldFiltration`, and it has a matching split node and docstring. No forbidden declarations were found. Verdict: pass.

3. Checked the four new declarations for truth, strength, and duplication against Mathlib and the library. They are strict intermediate filtration, scalar transport, and short-exact results; no duplicate declaration was found. Verdict: pass.

4. Read the proof downward from the target. It uses the finite filtration, underlying-abelian transport, and constructible short-exact induction, while preserving the unit route. The report records removed dependencies and the specialized short-exact route. Verdict: pass.

5. Checked the DAG nodes against the Lean declarations, including proof, dependencies, origin, and split documentation. Verdict: pass.

Changed after this reading: no Lean or DAG changes; this review record was added.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version: the target signature
and all existing declarations are byte-for-byte unchanged; only proof-only imports and
the proof body were added. Verdict: pass.

2. Compiled all five delivered modules with `lcompile.py`; there are no compiler errors,
forbidden declarations, or unsplit `sorry`s. The sole remaining `sorry` is the named,
documented structural theorem `constructible_hasPrimeFieldFiltration`, with its matching
node. Verdict: pass.

3. Checked the split statements against the finite-filtration, scalar-transport, and
short-exact arguments and searched Mathlib and the library for existing declarations.
The statements are true and strictly intermediate, with no duplicate theorem. Verdict:
pass.

4. Read the proof from the target downward. The induction uses the prime-filtration
constructor, underlying-abelian transport, and constructible short-exact step; the
specialized short-exact module avoids the documented import cycle. The unit route and
realized nodes remain intact, and the report records pruned dependencies. Verdict: pass.

5. Checked all five DAG node files against the Lean declarations, including proof,
proof dependencies, origin, module records, and the split theorem documentation.
Verdict: pass.

Changed after second reading: added this review record only; no Lean or DAG changes were
needed.

## New nodes

`def-v2-prime-field-filtration`: the finite extension-tree predicate, including both
constructors and the underlying abelian-sheaf identification of a prime leaf.

`lem-v2-constructible-prime-field-filtration`: the only new postponed proof, constructing
that tree from finite coefficients and constructibility. Source: 03SC second paragraph
and 03RZ. The node and theorem docstring describe primary decomposition, the r-torsion
kernel/quotient induction, scalar conversion and the zero case.

`lem-v2-underlying-abelian-assertions`: proved invariance of all eight conditional
assertions across a change of scalars with identical underlying abelian sheaf and
constructibility on both sides.

`lem-v2-constructible-short-exact-assertions`: proved extension step with explicitly
constructible outer terms, avoiding the unavailable cyclic import.

No change record is needed: only the item's proof and proof-only imports change among
existing modules. All other delivered modules and definitions are new.
