## What changed

Proved AlgebraicGeometry.Scheme.picard_directImage_fibre_betti with its original
signature, definitions, public imports and docstring unchanged. It uses two new,
proved structural cohomology lemmas, each in its own module. The final numerical
argument converts the negative zero object to a subsingleton vector space, hence
finrank zero, and transports degree-zero finrank through an isomorphism with the
residue field, whose dimension is one.

Both structural lemmas construct the canonical derived module base-change map and
apply perfect_derivedDirectImage_baseChange. Their local flatness proof uses
projectivity of finite locally free affine sections and transitivity of flatness.
The negative lemma uses the proved nonnegativity corollary of unbounded/bounded-below
right-derived compatibility. The degree-zero lemma uses the existing descended-fibre
generator theorem, trivializes its globally generated module, and transports this
trivialization through fibre-product associativity and tensor-pullback composition.
Degree-zero right-derived pushforward is ordinary pushforward. The tensor structure
comparison and hO make its global-sections ring map an isomorphism; restriction of
scalars along this map and GammaSpecIso gives the residue-field module.

The DAG records these actual proofs and the final dimension calculation. There are
no circular dependencies and no interface changes to existing declarations.

## Proved and sorry left

Closed one original hole:
AlgebraicGeometry.Scheme.picard_directImage_fibre_betti.

Also proved the two new declarations:
- AlgebraicGeometry.Scheme.picard_directImage_fibre_cohomology_negative
  (lem-sc-picard-direct-image-fibre-cohomology-negative).
- AlgebraicGeometry.Scheme.picard_directImage_fibre_cohomology_zero
  (lem-sc-picard-direct-image-fibre-cohomology-zero).

There are no sorries in any delivered module and no holes added. These proofs use
existing library declarations, whose own unresolved dependencies remain their
existing items. This is not a claim that the entire target import closure is
sorry-free. Every private helper is proved. No data is defined from an arbitrary
existence witness: the adjunction comparisons are determined by uniqueness of
left adjoints, and the open-site derived localizations use the standard construction.

## No longer needed

Removed the item's direct imports of
Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial and
Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange, replacing them with the two
structural cohomology modules. These original modules are still used indirectly,
through the fibre generator theorem and the structural proofs, respectively.
No existing module or node is globally pruned.

The original parent proof_deps no longer used directly are:
- def-pc-derived-direct-image
- def-pc-module-pullback
- def-sc-invertible-module
- def-weil-residue-field
- lem-pc-invertible-sheaf-instance
- lem-pc-module-pullback-adjunction
- lem-pc-rf-perfect-base-change
- lem-sc-field-pullback-rank-one-trivial

These remain statement dependencies or occur in the structural lemmas' transitive
proof dependencies (the rank-one lemma through the existing generator theorem).
Their removal from the parent's direct proof_deps does not globally prune them.

The negative statement does not require hO, fibre descent, an immersion, or the
field rank-one lemma. Its statement imports TensorPullback rather than
TensorPullbackAdjunction and omits the locally-free and immersion statement imports;
TensorPullbackAdjunction is imported privately for its proof. The degree-zero proof
uses the existing generator theorem, so it needs no new explicit nonemptiness or
residue-field transport obligation.

Removed the prior attempt's unsubmitted numerical component placeholders and nodes
lem-sc-picard-direct-image-fibre-betti-negative and
lem-sc-picard-direct-image-fibre-betti-zero. They are superseded by the proved
structural lemmas, not counted as holes closed against the repository baseline.

## Where the brief, the DAG or earlier work was wrong

The saved attempt had six long-line compiler warnings, which deliver3.py rejects.
Its component nodes depended circularly on their parent, were not in separate
modules, had non-verbatim Lean records, and did not update the parent proof plan.
Those problems are repaired. The new nodes are self-contained and have no edge to
the parent; their Lean records contain their actual signatures.

A shorter route was found for fibre triviality: the already-proved
picard_h1_base_descent_fibre_generator supplies a global free generator. This avoids
repeating its residue-field and rank-one argument. No unit statement or proof step
is bypassed; this node is not listed in the unit's realized statement/step arrays.

Edge cases: the identity morphism gives the expected field module in degree zero;
empty fibres are allowed by the negative lemma; in the degree-zero lemma hO
excludes them because the residue field has nonzero global sections. Positive
cohomology may be nonzero and no proof asserts its vanishing. The negative proof
uses zero objects, rather than merely zero finrank, so infinite-dimensional issues
cannot make the argument vacuous.

Mathlib's abstract nonnegative-cohomology results do not identify the geometric
fibre; the actual proof constructs that base-change comparison. The library's
private fibre_homology_iso in PicardFiberDirectImageRankConstructible guided this
construction but is not imported or invoked as an inaccessible private theorem.

## New nodes

lem-sc-picard-direct-image-fibre-cohomology-negative records the proved geometric
negative-cohomology vanishing before taking dimensions, for arbitrary base changes
and without descent. Its module is
Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyNegative.

lem-sc-picard-direct-image-fibre-cohomology-zero records the proved isomorphism
between H0 of the derived residue and the residue field, using the existing fibre
generator theorem and the universal structure unit. Its module is
Sheaf.AlgebraicGeometry.PicardDirectImageFibreCohomologyZero.

No change record: all existing statements, definitions and visibility are unchanged;
new dependencies of the item are ordinary proof imports. No forced adaptations.

## Second reading by K2

1. PASS: Diffed the existing module against the repository. Its sole existing
   theorem signature is byte-for-byte unchanged, as are its public imports and
   definitions. Only its proof and private proof imports change. Both additional
   modules are new; there are no forced adaptations or interface changes. The
   existing node changes only proof, proof_deps and proof_origin.
2. PASS: Compiled all three delivered modules in dependency order through
   lcompile.py, without errors or warnings. Source scans found no sorry, axiom,
   unsafe, opaque, implemented_by, extern or kernel-check bypass. Scratch copies
   with #print axioms for all three public theorems report exactly propext,
   Classical.choice, Quot.sound and sorryAx. The last is inherited from existing
   dependencies; there are no new holes. The delivery tool also probes every
   declaration, including the proved private helpers. All constructed maps come
   from the chosen derived functor's universal comparison or adjunctions; no new
   definition selects arbitrary data from unproved mere existence.
3. PASS: No statement is left split off with sorry. Read both new proved
   structural statements and their word proofs: negative vanishing needs neither
   descent nor hO, while degree zero follows from fibre triviality and hO.
   Checked identity morphisms, negative degrees, possibly empty fibres, and the
   lack of any positive-degree vanishing claim. hO excludes an empty fibre in
   degree zero. Repeated Lean Finder searches using different phrases for each
   statement, Loogle for rightDerivedZeroIsoSelf, and local searches for fibre
   homology comparisons. No directly applicable public geometric comparison was
   found; the abstract Mathlib lemmas already used do not replace base change.
4. PASS: The parent proof takes dimensions only after proving structural
   cohomology results. Checked the canonical comparison against the existing
   private fibre_homology_iso and the PlusCompatibility corollaries. The
   previously proved fibre-generator theorem avoids repeating rank-one descent.
   Proof-only imports are private. The pruning section now lists every old direct
   proof dependency removed; none is globally pruned. The unit sk-prop-av-cube
   has no realized statement or step naming this node, and its record and route
   are unchanged.
5. PASS: Parsed all three nodes, checked each lean.statement against the actual
   declaration signature, resolved every statement/proof dependency, and checked
   proof_deps against the union of proof-step uses. The structural nodes have
   source, word proofs, search records, provenance and Lean records, and no
   dependency back to the parent. The DAG follows the actual Lean argument.

Changes by this reading: corrected the degree-zero theorem's explanatory
empty-fibre wording and the report's corresponding edge-case wording; completed
the No longer needed section with all eight removed direct parent proof dependencies;
added independent second-reader searches to the two new nodes. No proof,
statement, definition or import was changed by this reading.
