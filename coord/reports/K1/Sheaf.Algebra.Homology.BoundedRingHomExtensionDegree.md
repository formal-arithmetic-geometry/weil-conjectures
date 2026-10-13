## What changed

Replaced the sorry of CategoryTheory.boundedRingHom_extension_degree_isIso by a
finite-product proof. The proof establishes zero Hom factors outside the support,
uses an extended limiting fan, constructs mutually inverse lifts using the supplied
term comparisons, and proves equality with t from its normalization.

Added proof-only imports RingExtensionFiniteSupportProduct,
RingExtensionInternalHomExt, and Presheaf.InternalHomUnit. All original signatures,
visibility, and docstrings are unchanged. Updated the item's node to the actual route.
No other existing module was adapted.

## Proved and sorry left

Closed CategoryTheory.boundedRingHom_extension_degree_isIso, node
lem-pc-bounded-ring-hom-extension-degree, by reduction to one strictly simpler lemma.
This is a decomposition, not an unconditional proof: one old hole closed and one new
hole added, net zero holes. The remaining lemma concerns arbitrary finite-support
product fans, without Hom complexes, term comparisons, t, or its invertibility.

Proved CategoryTheory.ringExtension_internalHom_ext, node
lem-pc-ring-extension-internal-hom-ext, using tensor induction transported through
object identifications and the invertible bottom-topology sheafification unit.
Its private ringExtension_induction helper is also fully proved.

The only sorry in the delivery is CategoryTheory.ringExtension_finiteSupport_product,
node lem-pc-ring-extension-finite-support-product. It has a complete source-based
proof sketch, handles the empty interval, and assumes no flatness or normalization
of F.map. No sorry remains in the item's module or the extensionality module.

## No longer needed

No existing import removed: PerfectRHomBaseChangeMap is needed by the statement.
No original planned mathematical dependency is pruned. The direct dependency
lem-weil-pbc-tensor-finite-product is moved into the finite-support-product lemma's
proof dependencies, where it belongs; it remains needed. The source and target
shared product fans come from def-pur-hom-complex. No projectivity, finite-generation,
chain-map, quasi-isomorphism or derived comparison lemma is added to this proof.

## Where the brief, the DAG or earlier work was wrong

The planned finite-product theorem in Mathlib is an ordinary module theorem, not
an API for the module-sheaf product and sheafification transport. This remaining
transport is isolated in the new finite-support-product statement. The existing
statement deliberately fixes only F.obj, so no proof may assume its F.map is the
canonical tensor map. The new statement respects that distinction by asserting
existence of normalized product projections independent of F.map.

LeanSearch returned Internal Server Error and is recorded as unavailable.
LeanFinder, Loogle, and grep searches ran and are recorded in the new nodes.
A local Nonempty product-witness helper avoids repeatedly elaborating the long
existential signature of homComplex_exists. Edge cases checked mathematically:
a>b gives a product of zero objects, zero rings and zero source modules are covered
by tensor induction, Q may be unbounded, and no flatness is used.
The unit route is unchanged; this node is not a realized unit step.

## New nodes

lem-pc-ring-extension-finite-support-product: generic extension of a finite-support
limiting fan with its normalized pure-tensor projections. One named theorem, one
new module, and the only new sorry; this is the finite-product part of the original
plan, strictly independent of the Hom comparison's term maps and invertibility.

lem-pc-ring-extension-internal-hom-ext: proved extensionality for morphisms into
internal Hom out of an extended module, by pure tensors in both arguments. Its
module also contains a fully proved private induction helper. No change records
are required, since no existing public interface is changed.

## Second reading by K1

1. PASS: diffed every delivered module against the repository. Only the original
   module has a repository counterpart. Its existing public theorem signature and
   docstring are byte-for-byte identical; its public import and visibility stay
   unchanged. The additions are a private product-witness wrapper, proof-only
   imports, and the proof. No definitions or existing statements changed.
2. PASS: compiled all three files with lcompile.py in import order, without errors
   or warnings. Searched all delivered Lean files for forbidden declarations and
   sorry: the sole sorry is ringExtension_finiteSupport_product. Scratch copies
   with #print axioms verified both private helpers and ringExtension_internalHom_ext
   use only propext, Classical.choice and Quot.sound. The finite-support-product
   lemma and boundedRingHom_extension_degree_isIso additionally use sorryAx, as
   explicitly reported. No data definition or arbitrary witness construction was
   introduced; the product projections are uniquely determined by the normalized
   formula on generating pure tensors and are used only inside a theorem proof.
3. PASS: the remaining split is a true, strictly smaller finite-product transport
   lemma, with a source, complete natural-language proof, and matching node. It
   neither mentions Hom complexes nor assumes the term comparisons or concludes
   that t is invertible. Empty support (a>b), the zero ring, zero factors, unbounded
   Q, and non-flat scalar extension cause no exception: finite sums and products
   coincide for modules and tensor preserves finite sums. F.map is never assumed
   canonical. The proved extensionality lemma uses tensor induction twice and the
   actual singleton identity slice. Independent searches used LeanFinder on scalar
   extension and finite-support limits, Loogle on product preservation, grep on
   biproduct preservation, and rg on the sheaf change-of-rings APIs. Mathlib has
   finite-biproduct preservation and ordinary tensor-product distribution, but no
   exact normalized finite-support sheaf-fan statement. The leftover transport
   needs more than a short application of those APIs; no new hole was added during
   this reading.
4. PASS: read the proof from the original theorem downward. The zero-factor argument,
   two lifts, inverse identities, and comparison with t are substantive reductions.
   All imports are used: PerfectRHomBaseChangeMap by the signatures, each new helper
   by the proof, and InternalHomUnit by homObjMap_zero_left. No old mathematical
   dependency is eliminated: lem-weil-pbc-tensor-finite-product remains below the
   finite-support helper. The No longer needed section correctly records this
   movement rather than claiming pruning. The unit sk-thm-picard-duality has empty
   realized statement/step arrays; no realized unit route is bypassed.
5. PASS after metadata repair: checked the three nodes' proof steps, proof_deps
   unions, proof_origin, source, chapter/unit, created and blueprint fields against
   Lean. Each new declaration has its own module and node. Replaced both new nodes'
   whitespace-flattened lean.statement strings by the exact multiline Lean
   signatures, as the brief requires. No other node field or Lean proof was changed.

Second reading changed only the two new node signature records and this report.
The delivery remains a decomposition: one original hole closed, one lower hole
added, net zero; the additional internal-Hom extensionality theorem is fully proved.
