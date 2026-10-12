## What changed

Replaced the sole proof hole of `MvPolynomial.exists_minimalPresentationTor_equiv` with a
complete Lean proof from a generic natural Tor boundary. The statement is unchanged.
Added a private, fully constructed residue equivalence using constant coefficient and
constant polynomials. Minimality directly makes the tensor of the kernel inclusion zero;
Mathlib projective Tor vanishing and exactness make the boundary bijective. The proof
constructs the inverse equivalences, transports naturality on quotient generators, and
transports subsingletonness. Updated the existing node's proof route.

Added `Sheaf.RingTheory.TorKernelBoundaryNaturality` for the missing first-variable
boundary naturality. This is one strict homological step, over arbitrary commutative
rings and surjections; it does not assert quotient/Tor equivalences or consequences of
minimality. All public imports of the existing module are unchanged. Its old direct
proof import is replaced by the new boundary module; TensorProduct.Quotient is added as
a proof-only Mathlib import. The new module retains the existing low-degree sequence as
a planned proof dependency.

## Proved and sorry left

Closed: `MvPolynomial.exists_minimalPresentationTor_equiv` (1 of 1 original holes).
No sorry remains in the item's module or its residue-equivalence helper.

Added: `CategoryTheory.exists_tor_kernel_boundary_natural`, the only new sorry,
node `lem-sc-p1-tor-kernel-boundary-natural`. This is a decomposition with one upper
hole closed and one generic lower hole added, not a claim of a sorry-free Tor theorem.
Both delivered modules compile locally in import order without warnings.

Edge cases checked for the new statement: the zero second module makes every tensor
and Tor term zero; an identity presentation has zero kernel and zero boundary; a
surjection onto zero has boundary with zero domain and an injective kernel inclusion,
so exactness is consistent. No projectivity is assumed in that intermediate result.
For the main theorem, free targets with identity presentations give zero kernel quotient,
and the residue-field presentation has kernel I and quotient I/I^2, as expected.

## No longer needed

Removed the direct proof import `Sheaf.Paper.TorLongExactFirstVariable` from the item.
It remains a planned proof dependency/import of the new boundary module, so this does
not prune that module from the target closure. No original dependency node is globally
pruned: free Tor vanishing and tensor-over-quotient are used directly, and the long exact
sequence is used in the boundary's proof plan. No unused new imports remain in the item.
The detour through proving F/IF -> N/IN is an isomorphism is unnecessary: minimality
already places ker(q) inside IF, which suffices to prove the inclusion tensor map zero.

## Where the brief, the DAG or earlier work was wrong

The existing `tor_long_exact_first_variable` quantifies naturality only in the second
module. The requested conclusion needs first-variable naturality across commuting
presentation squares, which its signature does not supply. The new boundary statement
isolates that missing strengthening without changing the existing theorem or any target.
The unit's route and statement are retained.

The local literature checkout lacks algebra.tex; the cited Stacks pages 00LY, 00M0 and
00LU were read online. The new proof origin is explicitly marked agent-expanded.
LeanSearch returned Internal Server Error; this is recorded as unavailable, with
LeanFinder, Loogle and a Mathlib source search completed instead.

## New nodes

`lem-sc-p1-tor-kernel-boundary-natural` in
`dag/nodes/sec-picard-framework/lem-sc-p1-tor-kernel-boundary-natural.json` records
`CategoryTheory.exists_tor_kernel_boundary_natural`, in the new module
`Sheaf.RingTheory.TorKernelBoundaryNaturality`. Its source is Stacks Algebra Section
00LY, particularly [00M0](https://stacks.math.columbia.edu/tag/00M0) and resolution-map
functoriality in [00LY](https://stacks.math.columbia.edu/tag/00LY). The node includes the
resolution construction, exactness transport, and cycle proof of naturality. Searches
of existing blueprint and Lean modules found only second-variable Tor naturality and
right-derived injective horseshoe results, not this statement. No change records are needed.

## Second reading by K1

1. **Unchanged public statements: PASS.** Read both delivered modules and compared the
   item with the repository using `diff -u`. The complete signature of
   `MvPolynomial.exists_minimalPresentationTor_equiv`, through `:= by`, is byte-for-byte
   unchanged (also checked programmatically). No existing definition or public import
   changed. The only new definition is the private residue equivalence, whose map is
   explicitly constant coefficient; no change record is required.
2. **Proof and axioms: PASS as a decomposition.** Compiled both modules locally in
   import order with lcompile.py: no errors or warnings. The only remaining `sorry`
   is `CategoryTheory.exists_tor_kernel_boundary_natural`, precisely the reported new
   theorem. No forbidden declarations, attributes, or hollow definitions occur.
   Scratch `#print axioms` checks give only propext, Classical.choice and Quot.sound
   for the private residue equivalence, and those plus sorryAx for the existing theorem
   and the new boundary theorem. The boundary witness is eliminated inside a theorem;
   it is not used to define an arbitrary public data object. Boundary bijectivity,
   inverse transport and subsingleton transport are proved in the item itself.
3. **Split statement: PASS.** Independently checked both exact pairs and the direction
   of the naturality equality. For M=0 all terms vanish. For q=id the kernel is zero,
   and exactness at Tor holds because Tor(id) is the identity. For N=0 the boundary
   domain is zero and the kernel inclusion is an isomorphism. More generally, for
   a split projection K direct-sum N -> N, Tor(q) is surjective and the tensor kernel
   inclusion is split injective, so the zero boundary satisfies both pairs. The
   commuting-square condition forces c to be the induced kernel map. Compatible
   horseshoe lifts, the cycle formula, and resolution comparison give simultaneous
   first-variable naturality. This is a genuine homological subproblem: it contains
   neither minimality nor a quotient equivalence nor the zero-module consequence.
   It has a complete docstring proof and a matching node. Repeated searches with
   different wording via LeanFinder (`left derived tensor functor connecting morphism
   natural short exact sequence`), Loogle (`CategoryTheory.Functor.leftDerived`), and
   rg over Mathlib and both project roots found comparison and homology components,
   but no ready-made Tor boundary family. Read the existing Tor exact-sequence and
   dimension-shift statements: their naturality concerns the second argument and
   does not provide the missing square. Verified the cited
   [Stacks 00LY](https://stacks.math.columbia.edu/tag/00LY) resolution functoriality
   and [00M0](https://stacks.math.columbia.edu/tag/00M0) exact sequence; the first-variable
   boundary proof is the recorded expansion via free resolutions, rather than a
   claim that 00M0 literally states the delivered family. Closing this remaining
   homological theorem requires substantial resolution infrastructure, not a short
   local proof.
4. **Route and pruning: PASS.** The proof uses Mathlib projective Tor vanishing and
   tensorQuotEquivQuotSMul directly. Minimality puts the kernel in I F and kills its
   inclusion after tensoring; no graded Nakayama lemma is unnecessarily imported.
   The original proof dependencies were the Tor long exact sequence, free Tor
   vanishing, and tensor-over-quotient. The first is replaced as a direct dependency
   by the natural boundary node, and retained below it as a planned dependency;
   the other two are used through their Mathlib matches. Thus no old dependency is
   omitted from the report and no module is globally pruned. The new public Mathlib
   imports supply the ModuleCat/Tor structures and instances needed by its statement;
   the two new imports into the item are proof-only. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists are
   empty and unchanged. The existing graded-resolution route is retained.
5. **DAG agreement: PASS.** The existing node's three proof steps describe the actual
   boundary application, bijectivity argument, and quotient/naturality transport;
   proof_deps is their union. The new node states the exact Lean theorem, has the
   required source, statement dependencies, proof plan, dependency union, origin,
   searches, creation, blueprint, chapter/unit and Lean fields. Its proof dependencies
   are explicitly a plan for the remaining hole, rather than claims of a completed
   Lean proof. Existing node changes are restricted to proof, proof_deps and
   proof_origin; the unit record is unchanged.

Second reading changed only this report: added the independent checks and explicit
axiom results. No Lean repair was necessary. Holes closed: one; holes added: one;
net zero. This delivery is a decomposition, with no globally pruned modules.
