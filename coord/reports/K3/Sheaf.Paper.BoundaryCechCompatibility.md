## What changed

Closed `AlgebraicGeometry.Scheme.Modules.boundary_cech_compatibility` in
`Sheaf.Paper.BoundaryCechCompatibility`, without changing its signature or any definition.
The proof embeds the middle module B into an injective I, takes the cokernel of A → B → I,
and constructs the induced morphism of short exact sequences. It applies the existing
`boundary_cech_injective_middle` theorem, cancels the monomorphism B → I on sections to
recover the original differences, and transports the boundary through the sequence morphism.

Three proved private helpers establish naturality of the actual canonical derived-triangle
boundary: `singleTrianglePlus_comm₃`, `rightDerived_boundary_naturality`, and
`boundary_naturality`. They use Mathlib's `ShortExact.singleTriangle.map` and
`Functor.homologySequenceδ_naturality`, followed by the natural right-derived comparison
isomorphisms. There are no new public declarations. The original public imports remain;
`RingedSpaceDerivedDirectImage` and the Grothendieck enough-injectives import provide the
instance context needed to elaborate the existing comparison hypothesis.

Updated the existing node `lem-sc-boundary-cech-compatibility` in the sandbox: its proof,
proof dependencies and proof origin now describe this compiled argument. No new modules,
nodes, definition changes, statement changes, forced adaptations, or change records.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.boundary_cech_compatibility`
(node `lem-sc-boundary-cech-compatibility`). No `sorry` remains in the item's module;
0 holes added and 0 split off. All three private helpers are proved.

The proof uses the existing declaration
`AlgebraicGeometry.Scheme.Modules.boundary_cech_injective_middle`
(node `lem-sc-boundary-cech-injective-middle`), whose proof remains `sorry` in its own
unchanged module. This is the existing next proof obligation, not a new hole or a claim of
an axiom-free transitive closure. Enough injectives is supplied by the already proved
`AlgebraicGeometry.Scheme.Modules.enoughInjectives`. The injective object and embedding
are chosen only from that proved theorem, not from an unproved existence theorem.

## No longer needed

Removed these direct proof imports and their use in this proof:

- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`lem-weil-pbc-right-derived-universal-delta-functor`). The concrete boundary naturality
  is proved directly from the canonical derived triangle.
- `Sheaf.CategoryTheory.SiteCechComplex`
  (`def-weil-pbc-site-cech-complex`). The existing comparison and injective-middle
  interfaces already supply the Čech complex; no differential calculation is required here.
- `Sheaf.Paper.PQFCohomology` (`pqf-def-cohomology`). The statement uses the already
  defined module cohomology and boundary directly.

These are removals of direct proof edges, not a claim that all three modules leave the
entire targets' closure: other retained dependencies can still import them. No unit
statement or realized unit step is bypassed. The unit `sk-thm-curveestimate` realizes its
statement at `thm-sc-proper-cohomology` and has no realized steps containing these nodes.

## Where the brief, the DAG or earlier work was wrong

The old Step 1 invokes existence of a universal right-derived delta-functor as if it
identified its connecting maps with `moduleCohomologyBoundary`. Its Lean signature does
not provide that identification. The proof instead establishes naturality for precisely
the triangle-defined boundary in the existing statement, using the Mathlib leaf
`lem-weil-pbc-derived-cohomology-ladder`.

The old route extends A → I across A → B. Such an extension B → I need not be monic,
so its sectionwise equation alone cannot be cancelled to recover the original cocycle.
Embedding B itself into I makes that cancellation valid and avoids a separate cocycle
existence argument. This is a simplification below the unit level; the injective reduction
and the existing injective-middle comparison are retained. The original docstring records
the prior valid conceptual route; the updated DAG and the Lean proof record the implemented
route.

Edge cases introduce no new assumptions: empty covers are handled under the original
cover equation, and zero objects or split sequences still admit the same injective embedding
and cokernel construction. The sign and all original universes, binders, comparison data,
local lift hypotheses, and conclusions are unchanged.

## Second reading by K3

1. PASS — Compared the sole delivered module with the repository version using `diff`;
   independently extracted the complete existing theorem signature and checked byte-for-byte
   equality. No existing definition, declaration visibility, universe, binder, hypothesis,
   conclusion, or public import changed. The only node fields changed are `proof`,
   `proof_deps`, and `proof_origin`. There are no change records or forced adaptations.
2. PASS — Compiled the delivered file with the prescribed `lcompile.py`: exit code 0,
   no warnings (56.3 seconds). Compiled a scratch copy printing axioms of all four local
   theorems and `enoughInjectives`: exit code 0 (51.0 seconds). Each private helper and
   `enoughInjectives` uses only `propext`, `Classical.choice`, and `Quot.sound`;
   `boundary_cech_compatibility` additionally uses `sorryAx`, as permitted for its existing
   open dependencies. No forbidden declaration or option and no local `sorry` occurs.
   The chosen injective embedding comes from the axiom-checked, proved enough-injectives
   theorem; the cokernel and induced quotient map are actual library constructions.
3. PASS — No statement or hole was split off, so there are no new unresolved statements
   to validate or deduplicate. Checked the retained injective-middle theorem against the
   application: its additional injectivity assumption is discharged by `Injective.under`,
   and its first object is definitionally the original A. The reduction neither adds
   hypotheses nor changes the comparison or sign. Empty covers (under the existing cover
   equation), zero objects, split sequences, and repeated indices require no exceptional
   assumptions. Read the three private naturality proofs: the third triangle square comes
   from Mathlib's canonical `singleTriangle.map`; boundary naturality comes from the actual
   triangle defining `moduleCohomologyBoundary`, with the two comparison isomorphisms
   transported in the correct directions.
4. PASS — Independently searched the library and Mathlib for boundary naturality and
   maps of `singleTrianglePlus`, and queried Loogle through `msearch.py` for
   `homologySequenceδ_naturality`. The Mathlib match is precisely the lemma already used.
   Other boundary naturality declarations concern Ext or different boundary constructions
   and do not shorten this proof of the canonical derived-triangle equation. No alternate
   proved local-lift comparison was found. The two discarded old proof dependencies
   (universal delta-functor and site Čech complex) and the extra removed PQF import are all
   listed under `No longer needed`; enough injectives and injective-middle are retained.
   Public instance imports support elaboration of the existing comparison hypothesis.
   Checked `dag/units/sk-thm-curveestimate.json`: its realized statement is
   `thm-sc-proper-cohomology`, and it has no realized steps, so none is bypassed.
5. PASS — Read the original and updated node and checked all three new proof steps
   against the implementation. The dependency union is exactly enough injectives,
   derived cohomology ladder (a Mathlib leaf), and injective-middle. The recorded proof
   origin describes the injective-middle reduction and canonical triangle naturality.
   Existing statement and Lean records are unchanged; there are no new nodes requiring
   additional fields. Read the landed local-lifts sign change record: this delivery
   preserves the already recorded `t₁ - t₀` convention throughout.

Second reading changed only this report, adding the independent review and axiom evidence.
No Lean or DAG repair was needed. Closed 1 original hole, added 0 holes, split off 0;
this remains a proof relative to the existing injective-middle obligation, not a claim
that the entire import closure is axiom-free.
