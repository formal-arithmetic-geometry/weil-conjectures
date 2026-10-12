## What changed

Reduced `AlgebraicGeometry.schemeMayerVietorisComplex_shortExact` to degreewise
short exactness, using Mathlib's
`HomologicalComplex.shortExact_of_degreewise_shortExact` and a proof-only import
of `Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise`. The theorem's
signature is unchanged. Restored the original public Mathlib injectivity import
so that the delivery preserves the public interface. The second reader narrowed
the new lemma to injectivity of I.X n and restored its proof-only lifting import.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeMayerVietorisComplex_shortExact` by a complete Lean
assembly proof. Added one hole:
`AlgebraicGeometry.schemeMayerVietorisComplex_degreewise_shortExact`, node
`lem-pc-kinjective-mayer-vietoris-degreewise`, in its own new module.
This is a decomposition: one hole closed, one added, net zero. The degreewise
sheaf exactness argument remains to be proved; the original module has no holes.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective` and
`Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` from the exactness module.
Their sectionwise arguments belong to the degreewise component. The data module
still imports the restriction-map machinery. No claim is made that either module
leaves the targets' entire import closure. All three old proof_deps leave the upper node's direct proof:
def-pc-kinjective-mayer-vietoris-data,
def-pc-derived-open-restriction-maps, and
lem-sc-ringed-space-injective-restriction-surjective.
They remain below the degreewise node; none is globally pruned.
The new module imports InjectiveRestrictionSurjective for the stated lifting
step; DerivedOpenRestrictionMaps is already publicly imported by the data module.

## Where the brief, the DAG or earlier work was wrong

The previous attempt removed the public import
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`, triggering an interface
change without a change record. It is now restored. The previous delivery-tool
ImportError no longer occurs. The original proof's degreewise step is now a
separate named item, with the generic complex assembly carried out in Lean.
The unit's realized routes are unchanged.

## New nodes

`lem-pc-kinjective-mayer-vietoris-degreewise` states the degreewise component
needed by Mathlib's assembly theorem. Its module is
`lean/Sheaf/AlgebraicGeometry/KInjectiveMayerVietorisDegreewise.lean`.
The theorem keeps the cover and assumes injectivity only of the evaluated term I.X n. Its proof in
words treats empty and repeated opens by the same sheaf gluing and lifting
argument. The existing exactness node now records only the assembly step.

## Second reading by N1

1. Interface: compared the delivered exactness module with the repository using
diff. Its sole existing theorem signature, universe, namespace, visibility,
public imports, and definitions are unchanged byte for byte. Only private
proof imports and the proof body changed. No existing statement or definition
change needs a change record. The added degreewise module has no repository
version. No other module is adapted.

2. Proof: compiled both modules together in import order using lcompile.py.
The assembly applies Mathlib's
HomologicalComplex.shortExact_of_degreewise_shortExact, whose source proves
monicity, epicity, and exactness from evaluation at every degree. The only
remaining syntactic hole is the named degreewise theorem. No axioms, unsafe,
opaque, implemented_by, extern, or data definitions are added. Scratch
#print axioms checks for both theorems are recorded below. The original hole
is closed conditionally on this split-off hole: this is decomposition, not a
net proof or an axiom-free completion.

3. New statement: read the data module's actual biproduct maps and adjunction
mates, DerivedOpenRestrictionMaps, and the now-proved
injective_restriction_surjective. Read Stacks
[08BV](https://stacks.math.columbia.edu/tag/08BV),
[01EB](https://stacks.math.columbia.edu/tag/01EB), and
[01EA](https://stacks.math.columbia.edu/tag/01EA).
The degreewise statement is true: evaluating gives the pair of restrictions
and their difference, the cover supplies unique gluing for the kernel, and
injectivity lifts an intersection section on the U side, with zero on V.
This needs injectivity only in degree n, so I narrowed the new lemma's
hypothesis accordingly. Other terms and differentials need no injectivity.
For U empty and V top, the sequence is M to 0 plus M to 0; for U=V=top it is
the diagonal M to M plus M followed by difference to M. For the empty scheme
all section modules are zero. No nonempty or distinct-open hypothesis is
needed. The docstring describes the section identifications and the kernel
universal property, not just surjectivity. Fixed-degree sheaf exactness is a
strict part of the argument; the upper proof supplies the distinct passage
from degreewise statements to complex exactness.

Independent searches via msearch leanfinder (flasque open-cover module
sequence), loogle (HomologicalComplex.eval, ShortComplex; remote identifier
unavailable), and rg on the library and Mathlib found no complete existing
specialization. MayerVietorisSquare.shortComplex_shortExact constructs a
sequence of free additive sheaves; MayerVietorisFreeComplex is its free
abelian specialization. Neither identifies the transported O-module maps
here. EtaleMayerVietorisExact is a cohomology statement on a different site.
I found no split-off theorem that closes by a short existing application.

4. Pruning and route: the upper proof uses exactly the new degreewise
module beyond its public data/injectivity imports. The removed two direct
private imports and all three old direct proof_deps are listed above.
No module is claimed globally pruned. The new module imports the injective
restriction theorem for its proof plan; the data module already imports the
nested restriction machinery. Read dag/units/sk-thm-picard-duality.json:
its realized statement and sole step are empty arrays and unchanged.
No unit or chapter route is bypassed; the original sectionwise argument
is retained below the new node.

5. DAG: the existing node records the one generic assembly step and only
the new degreewise node in proof_deps. The new node has its own module,
verbatim Lean signature, source, complete proof steps, union of proof_deps,
creation record, blueprint parent, matching chapter/unit, and independent
searches. I restored the omitted derived-open-restriction dependency for
the mate identification, removed a proof lemma from stmt_deps, and cited
the scheme and sheaf category definitions used by its statement.

Changes by this reader: narrowed the new theorem to injectivity at its chosen
degree and passed hI n in the existing proof; restored its private lifting
dependency import; repaired new-node statement/dependency/search metadata;
completed the list of removed direct dependencies and this reading.

Axiom verification: scratch copies with #print axioms for
AlgebraicGeometry.schemeMayerVietorisComplex_shortExact and
AlgebraicGeometry.schemeMayerVietorisComplex_degreewise_shortExact both compiled
and printed exactly propext, Classical.choice, Quot.sound, and sorryAx.
The scratch copies were removed. The final two modules compiled cleanly
together (5.6 s and 6.6 s).
