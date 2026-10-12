## What changed

Replaced the sole hole in `exists_generic_finite_algebra_splitting` by a compiling proof
from the existing generic separable splitting, finite separable spreading, and purely
inseparable spreading declarations, together with two new intermediate modules:
`Sheaf.AlgebraicGeometry.SpreadGenericProductDomains` and
`Sheaf.AlgebraicGeometry.RefineFiniteDomainSplitting`. Both new imports are proof-only.
The existing theorem's signature and visibility are unchanged. No existing dependency
interface or definition was changed, and no forced adaptations are included.

The proof forms the generic fibre using `FractionRing A`, applies the field splitting,
spreads the separable field extension, spreads its specified generic product to domain
factors, proves injectivity of each factor map using its compatible fraction fields,
applies the existing purely inseparable spreading theorem separately to each factor,
and takes a common localization. The extra scheme finiteness clauses follow directly
from each factor's module finiteness using Mathlib's spectrum-map criterion.

All three modules compile together through `lcompile.py --all`. The main module also
compiles individually against the sandbox's compiled intermediate modules. Lines are
at most 100 characters; all modules use the module system and disable auto-implicit
variables. There are no new definitions or data chosen by an unproved existence theorem
inside a definition. Existential witnesses are eliminated only in the proof of a proposition.

## Proved and sorry left

Closed: `exists_generic_finite_algebra_splitting`, node
`lem-weil-pbc-generic-finite-algebra-splitting` (one original hole).

Added and still sorry:

- `exists_spread_generic_product_domains`, node
  `lem-weil-pbc-spread-generic-product-domains`, in
  `Sheaf.AlgebraicGeometry.SpreadGenericProductDomains`.
- `exists_refinement_of_finite_domain_splitting`, node
  `lem-weil-pbc-refine-finite-domain-splitting`, in
  `Sheaf.AlgebraicGeometry.RefineFiniteDomainSplitting`.

No sorry remains in the assigned module. This is a decomposition: one upper hole closed,
two strictly smaller holes added, net minus one hole, and not an unconditional proof.
The existing imported dependencies retain their own holes; they were not modified.

The first new lemma assumes an actual generic product equivalence and an actual finite
etale model; it does not establish any purely inseparable or universal-homeomorphism
property. The second assumes an actual finite domain product and actual localizations
where each factor is a universal homeomorphism; it only combines and transports them.
Neither is a renamed or repackaged version of the assigned theorem.

## No longer needed

No original module or node is pruned. Removed the unused
`Mathlib.FieldTheory.PurelyInseparable.Basic` import from the new idempotent-spreading module.
All three original proof-dependency imports are applied by the proof. Both new
imports are applied. No existing module or DAG node is pruned. The unit record
`sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps`; the finite-algebra
route recorded for this item is preserved throughout.

Second reading narrowed the geometry import in each new module from
`Mathlib.AlgebraicGeometry.Morphisms.Finite` to
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: their statements use surjectivity
and topological morphism properties, not scheme finiteness. The original module keeps
its finite-morphism import because its statement explicitly uses `IsFinite`.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies did not expose two substantive glue steps in the old plan:
spreading the specified generic idempotents while descending all localizations to the
original domain, and combining finitely many factorwise localizations while preserving
the reduced product and replacing an iterated localization by a single `A[1/d]`.
These are now explicit intermediate statements rather than hidden inside the main proof.

No false statement or target-signature error was found. The new statements were checked
on the zero algebra/empty product, one factor, a field base, and the characteristic-zero
case where the purely inseparable extensions are identities. In the common-localization
lemma, injectivity of the original factor maps is explicit, preventing a factor supported
only on a closed subset from disappearing after shrinking. In the idempotent-spreading
lemma, torsion is killed before embedding into the generic fibre; reducedness alone does
not imply torsion freeness. Small-universe factors are obtained from finite presentations,
not by assuming the large-universe extension fields are already small.

LeanFinder and grep found no exact shorter route; Loogle's tensor-product name query did
not resolve that identifier. LeanSearch returned Internal Server Error for each new lemma;
its unavailability is recorded without an absence verdict. Search records cover the
pinned Mathlib, both project roots and the blueprint/DAG searches for idempotents and
localization. Existing finite-etale locus and localization-product results did not state
either new lemma in one application.

The blueprint source path recorded in the original DAG is absent from this machine's
repository. The existing item's complete numbered proof and docstring supplied the
spreading argument; both new proofs are marked agent-written and spell out this argument.
WANTED: the source file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md`,
proof steps 4--9, for comparison with the two new spreading/localization nodes.

## New nodes

`lem-weil-pbc-spread-generic-product-domains`: specified generic product and specified
finite etale model spread to a product of finite domain factors with specified fraction
fields, after one principal localization of the original base. The module docstring gives
the torsion-killing, idempotent-lifting, denominator-descending, and universe-transport
argument, including the empty-product case.

`lem-weil-pbc-refine-finite-domain-splitting`: the finite family of given principal opens
is replaced by their product, its numerator is descended to the original base, and the
factor maps and reduced product are transported by localization and base change. The
number of factors is preserved. The docstring specifies the ring constructions and the
iterated-localization identification.

No change record is needed: all existing interfaces are unchanged. The existing item's
node is updated only in `proof`, `proof_deps`, and `proof_origin`.

## Second reading by D3

1. Compared the delivered original module with the repository using `diff -u`.
   Its sole existing declaration's signature, visibility and docstring are byte-for-byte
   unchanged. Only two proof-only imports and the proof body were added. No definition
   or existing dependency interface changed. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py --all`, including
   after the import repairs. All compile without errors or non-sorry warnings. A scratch
   module directly importing all three and printing each declaration's axioms reports
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for each. There are
   exactly two explicit holes, both the reported named new theorems with complete
   docstring arguments; there are no definitions or forbidden declarations. Existential
   witnesses are used only inside the original proposition's proof. Verdict: pass as a
   decomposition, not as an axiom-free proof of the target.
3. Checked both new statements against their natural-language proofs. The first kills
   torsion before lifting the generic idempotents and descends the denominators to the
   original base using integrality. The second uses the product of the given nonzero
   elements and retains all factors; injectivity prevents a domain factor becoming zero.
   Empty products, zero/torsion algebras, field bases, a single factor, and identity
   purely inseparable extensions produce the expected conclusions. Neither new statement
   supplies the other's step or restates the original result. Independent LeanFinder
   queries about generic idempotents and common principal opens, and a new pinned-Mathlib
   grep, found components but no exact replacement. Also inspected upstream
   `Etale/FiniteSplitting.lean`, `Localization/Away/Idempotent.lean`, and the finite
   scheme splitting interface: geometric-point idempotents do not supply a finite
   surjective base model with the required domain and fraction-field conclusions.
   Verdict: true, necessary proper intermediate steps; neither can be closed in a few
   minutes from those interfaces.
4. Read the reduction from generic splitting through separable spreading, domain
   spreading, factorwise purely inseparable spreading, and common localization. It
   applies all three original proof dependencies, so the old dependency pruning list
   is complete (none). The unit's `realized.statement` and `realized.steps` are empty;
   its recorded finite-algebra route is preserved. Narrowed the geometry imports of
   both new modules to `UnderlyingMap`. Verdict: pass.
5. Checked every delivered node against its Lean declaration and proof. The two new
   node signatures match their Lean signatures verbatim and have the required source,
   creation, search, blueprint, chapter, unit and Lean fields. For every node the union
   of its proof-step `uses` is exactly `proof_deps`. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`, and its steps describe the actual Lean
   calls. Verdict: pass.

Changed only the two new geometry imports and this report. Closed no additional hole
and added no hole during second reading: the delivery remains one original hole closed,
two strictly smaller holes added, net minus one. The scratch axiom-check module was
removed before delivery. The original source document is unavailable locally as noted
above; the original module's complete proof docstring and DAG plan were available and
agree with the reduction.
