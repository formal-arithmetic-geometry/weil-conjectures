## What changed

Replaced the sorry in AlgebraicGeometry.RingedSpace.coherent_extension_relations by
an actual proof of the relation-kernel argument. A private lemma in an arbitrary
abelian category constructs the induced map from kernel (g ≫ quotient) into the
first term, and constructs inverse kernel lifts identifying its kernel with
kernel g. A second private lemma transports finite local generators along an
isomorphism. Both private lemmas are fully proved.

Added the proof-only import Sheaf.AlgebraicGeometry.CoherentFiniteTypeKernelOver.
The public imports, existing signature, definitions and visibility are unchanged.
The new module states only the open-slice version of the finite type source to
coherent target kernel lemma, with a complete source proof. It is a strictly
separate part of the argument: no short exact sequence, middle term, or finite
free map into a middle term occurs in its signature.

Read Stacks 01BY and 01BV at https://stacks.math.columbia.edu/tag/01BY and
https://stacks.math.columbia.edu/tag/01BV. The local literature checkout has only
its citation lists, so these pages supplied the source text.

## Proved and sorry left

Closed the hole AlgebraicGeometry.RingedSpace.coherent_extension_relations
(lem-weil-pbc-coherent-extension-relations), by reduction to the named new lemma.
No sorry remains in the item's module.

Added one hole: AlgebraicGeometry.RingedSpace.coherent_finiteType_kernel_over
(lem-weil-pbc-coherent-finite-type-kernel-over), in its own new module. This is a
one-hole decomposition, with net zero holes closed, not a sorry-free proof of the
mathematical assertion. The remaining work is the open-slice interface for
01BY (2); the categorical extension argument is completely proved.

## No longer needed

No original direct import was removed: Coherent supplies the signature and
ShortComplex.ShortExact supplies the short exact sequence and its kernel property.
The original DAG's snake lemma route is unused:
lem-weil-pbc-snake-lemma-abelian (Mathlib.Algebra.Homology.ShortComplex.SnakeLemma)
and lem-weil-pbc-abelian-exact-iff-epi-kernel-lift
(Mathlib.Algebra.Homology.ShortComplex.Exact). Neither is imported for this proof.
The latter module remains transitively available through ShortExact, so this is
an argument dependency removal, not a claim of pruning its entire import closure.

The original direct proof dependency
lem-weil-pbc-ringed-space-module-exactness-local-lifting
(Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting) is not used by the
item: existing, proved restriction instances and ShortExact.map_of_exact suffice.
It remains a transitive dependency of the existing finite type kernel theory.
The existing finite type kernel lemma
lem-weil-pbc-coherent-finite-type-sub-kernel
(Sheaf.AlgebraicGeometry.CoherentFiniteTypeSubKernel) is used by the new node's
proof plan, not directly by the item. No global unreachability is asserted.

## Where the brief, the DAG or earlier work was wrong

The planned finite type kernel declaration accepts only modules over moduleRings X.
Here its finite type source is a module over (moduleRings X).over U. The existing
coherence-local-on-cover theorem is for schemes, while this item concerns any
ringed space. Thus it cannot supply this open-slice interface unchanged.
The new lemma isolates exactly this issue. There is no mathematical dispute.

The unit sk-thm-p1 realized statements and steps are unchanged. This node is below
them; only the categorical implementation of its relation diagram changed.
Initial concrete sheaf elaboration timed out. Supplying the category explicitly
and making generator transport a generic helper removed the expensive inference;
no compilation limit, public definition, or statement was changed.

## New nodes

lem-weil-pbc-coherent-finite-type-kernel-over states Stacks 01BY (2) on an open
slice, with the target restricted from a coherent ambient module. Small cases:
U empty gives the zero sheaf; U = X is 01BY (2); zero source has zero kernel; zero
map has kernel the finite type source. No surjectivity of phi is assumed. The
proof is exactly the local free presentation argument of 01BY (2).

Existing-node searches: rg over all DAG nodes for finite type kernels on opens,
all IsCoherent declarations in Sheaf/WeilConjectures, and blueprint_refs search
"finite type kernel" (zero matches), followed by "coherent". The general kernel
node exists but has no slice signature; the scheme restriction node excludes
ringed spaces. The Mathlib searches recorded in the new node were run via
msearch.py with this item's name. LeanSearch returned Internal Server Error and
is recorded as unavailable, not as a negative match. The nearest-ancestor script returned None due
to earlier created.item records naming modules; the explicit existing parent
blueprint reference was followed instead, retaining its ancestor and adding this
item to the via path. No change record is necessary: no existing interface changed.

## Second reading by P1

1. PASS: compared both delivered modules with the repository. The sole existing
   declaration's full signature is byte for byte unchanged, as is its public
   visibility. The only new declarations are two proved private helpers and the
   named public open-slice kernel theorem. No definitions or target statements
   changed; no change record or forced adaptation is needed.
2. PASS as a decomposition: compiled both files with lcompile.py in import order,
   without errors or warnings. The sole delivered sorry is the whole proof of
   coherent_finiteType_kernel_over. A scratch copy with explicit print-axioms
   commands shows only propext, Classical.choice and Quot.sound for both private
   helpers; the item and the split theorem additionally use sorryAx, as reported.
   No forbidden declarations, hollow definitions, or arbitrary witness data occur.
   Read both inverse kernel lifts and their cancellation proofs, and the finite
   generator transport: these prove exactly the required kernel identification
   and finite type transport.
3. PASS: independently read Stacks 01BY (2), (4) and Definition 01BV. The new lemma
   isolates the finite type source-to-coherent target kernel argument; it does not
   restate the extension problem. Its docstring gives the local finite free
   presentation, finite type relation kernel and locally surjective image proof.
   Checked empty U, maximal U, zero source, zero map, and a one-point ringed space:
   they give respectively the zero category, the ambient finite type kernel
   theorem, zero kernel, the given finite type source, and the usual module lemma.
   No epi hypothesis on the map is needed. Repeated msearch LeanFinder with
   "finitely generated kernel ... localized site", Loogle with
   "SheafOfModules, CategoryTheory.Limits.kernel", and grep with kernel/iso
   variants. Read Mathlib Generators/Quasicoherent candidates and searched both
   Sheaf and upstream modules. No existing theorem has this arbitrary-ringed-space
   open-slice signature. The existing ambient kernel theorem is still sorry;
   proving its slice interface needs substantive local-generator/site transport,
   so it cannot be closed in a few-minute repair.
4. PASS: the categorical helper replaces the unnecessary snake-lemma route with
   explicit kernel universal properties. The item imports only its signature
   modules publicly and the split theorem privately. The split theorem imports
   the existing ambient kernel module privately for its recorded proof plan.
   All four old proof dependencies omitted by the new argument are listed in
   No longer needed (snake lemma, exact-iff-epi-kernel-lift, local lifting and the
   ambient finite type kernel node); none is claimed globally unreachable.
   Read dag/units/sk-thm-p1.json realized: this item realizes no unit statement or
   step, and the prescribed unit route is unchanged.
5. PASS: checked the existing node diff changes only proof, proof_deps and
   proof_origin. Each node's proof_deps is exactly the union of its step uses;
   each dependency exists. The Lean declarations and recorded signatures agree,
   and the new node has its source, searches, creation, blueprint ancestry,
   chapter, unit and Lean record. The proof records follow the actual restriction,
   kernel lifts and open-slice kernel application.

Second reading changed only this report by adding the independent review and
verification evidence. The proofs, new statement, imports and nodes were correct
and were left unchanged. One upper hole is closed and one lower hole is added:
a decomposition with net zero holes closed, not a complete axiom-free proof.
