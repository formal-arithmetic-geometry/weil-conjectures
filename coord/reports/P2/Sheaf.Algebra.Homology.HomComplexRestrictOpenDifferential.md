## What changed

Completed `CategoryTheory.homComplex_restrict_open_differential` in
`Sheaf.Algebra.Homology.HomComplexRestrictOpenDifferential`, with its signature unchanged.
The proof uses joint monicity of the chosen product projections, the global and localized
differential formulas, and a proved private categorical calculation distributing subtraction
and the integer sign. The sign is converted from an integer unit to its integer value
before the categorical calculation, avoiding redundant scalar-action reductions.
Explicit site parameters avoid expensive typeclass diamonds when
specializing naturality. All seven let bindings are introduced without unfolding their data.

Added and proved the public theorem `CategoryTheory.overHomObjIso_naturality` in
`Sheaf.Algebra.Homology.InternalHomOverNaturality`. It identifies the underlying presheaf comparison,
removes the final equality transport by proof irrelevance, and verifies naturality on every
section and every component of the section morphism. The new statement has its own module, imported only for the differential proof.
No existing definition, public import, or theorem signature changes.

## Proved and sorry left

Closed the item's sole hole, `CategoryTheory.homComplex_restrict_open_differential`
(node `lem-sc-hom-complex-restrict-open-differential`).
The added `CategoryTheory.overHomObjIso_naturality`
(node `lem-sc-internal-hom-over-naturality`) is fully proved.
Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
The private precomposition, postcomposition, and signed factor-calculation helpers are proved.

## No longer needed

The new `Sheaf.Algebra.Homology.InternalHomOverNaturality` module contains the proved
naturality statement and is imported only for the proof. The existing three public imports
supply the statement's Hom-complex projections,
ringed-space module-ring notation and additive restriction instance, and internal Hom comparison.
The only new import is the proof-only naturality module. No node or module from the existing route is bypassed or pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt did not compile: unfolding all theorem let bindings and inferring
site parameters during naturality specialization caused deterministic elaboration timeouts.
Introducing the bindings explicitly, specifying the site parameters, and using the categorical
factor calculation resolves this without changing an interface. Its proposed naturality hole
is unnecessary: the sectionwise proof now compiles. The unit's realized lists are empty and
its fixed route is unchanged.

The cited Stacks source files are absent from this read-only checkout. The corresponding
public Stacks pages 0A8X, 08DL, 04TT, and 04IX were read online to check the signed differential,
restriction construction, internal Hom, and ringed-site localization. The naturality claim
is the direct sectionwise consequence of these constructions, rather than a quoted theorem.
Zero maps, identity maps, empty opens, and unbounded complexes need no extra hypotheses.

## New nodes

`lem-sc-internal-hom-over-naturality` records naturality in both arguments of the existing
canonical internal Hom restriction isomorphism, on an arbitrary ringed site. Its Lean theorem
is proved in its own new module, not left as a new hole. The three search kinds in the node and
the sandbox search
log found no exact existing theorem. The parent node's third step now names this proved lemma;
the projection and additive-restriction steps are retained. No change record is needed.

## Second reading by P2

1. Compared every delivered Lean module with the repository. The only existing declaration
   changed is `CategoryTheory.homComplex_restrict_open_differential`: its signature is
   byte-for-byte identical, checked by extracting the text before `:= by`. No definition
   or existing public import changes. The new module has no repository predecessor.
2. Both final modules compile through lcompile.py in import order without errors or warnings
   (11.6 s and 53.5 s). Neither contains sorry, axiom, unsafe, opaque, implemented_by,
   extern, or a kernel-check bypass. There is no new data construction or witness choice.
   The chosen projections were already in the unchanged signature, and their specifications
   are used explicitly in the proof. A scratch copy prints the axioms of the main theorem,
   the naturality theorem, and all three private helpers; results are recorded below.
3. No statement is split off with sorry. The new, proved naturality theorem is strictly
   a component of the argument: it concerns two sheaf morphisms on a site, with no complexes,
   differential, products, or degreewise comparison isomorphisms. Its sectionwise proof and
   source are in its docstring, and its node matches the Lean signature verbatim. Checked
   zero and identity morphisms, arbitrary site objects (including empty opens), and the
   direction of contravariance in the first argument. Repeated LeanFinder, Loogle and grep
   searches with different wording; no existing theorem replaces the comparison naturality.
4. Read from the differential theorem down through projection joint monicity, both signed
   projection formulas, and naturality. The integer sign is unchanged by Units.smul_def;
   p + 1 is the correct precomposition index since m = n + 1. The private categorical
   calculation is a direct additive-functor calculation, with no further hypotheses on the
   complexes. All existing imports supply signature data; the new import is proof-only.
   Every old proof dependency remains used, so nothing is pruned. The unit
   sk-thm-picard-duality has empty realized lists; no unit statement or step was changed.
5. Compared both node files with their Lean proofs and the repository node. The existing
   node changes only proof, proof_deps and proof_origin. Their dependency union agrees
   with the three written steps. The new node has source, full proof, search records,
   creation provenance, blueprint ancestry, chapter, unit and the exact Lean record.

Changed the packaging of the proved public naturality theorem: moved it to the new module
`Sheaf.Algebra.Homology.InternalHomOverNaturality`, added a plain proof-only import to the
item, and updated its node and the report. This enforces the brief's requirement that a new
statement has its own module. Also restored the original spacing before the main theorem's
proof, so the existing signature text is exactly identical. No mathematical proof was rewritten.

Axiom verdict: the scratch #print axioms checks compiled in 42.1 s and showed only
`propext`, `Classical.choice`, and `Quot.sound` for all five declarations, including
the main theorem; no `sorryAx` occurs. The scratch copy was removed before delivery.
