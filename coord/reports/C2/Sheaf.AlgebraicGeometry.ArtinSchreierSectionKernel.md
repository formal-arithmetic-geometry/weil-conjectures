## What changed
Proved `AlgebraicGeometry.Scheme.artinSchreier_section_data_isKernel` with its unchanged signature. For a nonempty scheme, construct its structure morphism to Spec of the universe-lifted prime field and apply the existing proved `AlgebraicGeometry.artinSchreier_kernel_sections`. Assemble sectionwise unique preimages into an additive natural transformation and use the kernel universal property. For an empty scheme use `Etale.isZero_sheaf_of_isEmpty`. Added proof imports `Sheaf.AlgebraicGeometry.ArtinSchreierKernelSections` and `Mathlib.Algebra.Field.ULift`. Updated the node's proof route and docstring.

## Proved and sorry left
Closed the sole hole, `AlgebraicGeometry.Scheme.artinSchreier_section_data_isKernel` (lem-sc-artin-schreier-section-kernel). No holes added; no sorry remains in the delivery. Compilation is clean. A scratch-copy `#print axioms` check reports `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for the delivered declaration and for the imported `AlgebraicGeometry.artinSchreier_kernel_sections`. Thus the own hole is closed, but the cached upstream proof closure remains open; this is not a claim that the theorem is axiom-complete. The dry-run probe also checks the delivered declaration.

## No longer needed
Removed direct imports `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`, `Sheaf.RingTheory.LocalRing.ArtinSchreierKernel`, and `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`. The target proof no longer needs geometric-stalk identification, pointed etale neighborhoods, constant-sheaf geometric-stalk comparison, stalk exactness, or geometric-stalk conservativity: def-weil-pbc-geometric-stalks, def-weil-pbc-pointed-etale-neighbourhoods, lem-weil-pbc-constant-sheaf-geometric-stalk, prop-weil-pbc-geometric-stalks-exact, lemma-weil-pbc-geometric-stalk-conservative. The old direct dependency `lem-sc-local-ring-artin-schreier-kernel` is replaced by `lem-sc-as-kernel-sections`, but remains needed transitively by ArtinSchreierKernelSections, so it is not globally pruned. The old direct dependency `def-weil-pbc-exact-sequence` is no longer used in this kernel-only assembly. These are direct import/dependency removals; globally unreachable modules are determined by the maintainer's ledger, not asserted here. No unit realization is bypassed: sk-prop-cd has empty realized statement and step lists.

## Where the brief, the DAG or earlier work was wrong
No false statement found. The stalk plan was unnecessary: the existing sectionwise theorem applies after constructing the canonical prime-field structure morphism. Empty schemes require a separate branch because global sections are the trivial ring and cannot carry CharP p for prime p. The new argument explicitly includes this case. The section choices are determined uniquely by injectivity; no arbitrary data is obtained from an unproved existence theorem. Two exploratory stalk modules were discarded and are not delivered.


## Second reading by C2
1. Interface preservation: compared the sole delivered Lean module with the repository
   using `diff`, and compared the complete declaration signature as bytes. It is
   identical. No declaration or definition was added, removed, or changed; the two
   public imports are unchanged. Verdict: pass; no change record is required.
2. Proof and trust: read both branches and the sectionwise dependency. Launcher
   compilation succeeds without errors or warnings. No `sorry`, forbidden declaration,
   or hollow definition occurs in the delivered module. A scratch-copy `#print axioms`
   gives only the three standard axioms plus imported `sorryAx`, also present in
   `artinSchreier_kernel_sections`. The nonempty branch constructs its prime-field
   structure map explicitly; all section choices are uniquely determined by injectivity.
   The empty branch uses the zero-sheaf theorem. Verdict: pass with the recorded
   upstream open proof closure.
3. Split statements: none were introduced; no holes were added. Checked that the
   existing sectionwise theorem permits locally varying constants on disconnected
   objects and includes empty etale objects. The argument does not assume a single
   constant represents every root. Primality excludes p = 0 and p = 1, and the empty
   base is handled before constructing CharP on its trivial global-section ring.
   Verdict: pass; no new nodes or restatement of the target.
4. Route and pruning: searched Lean sources with kernel/injectivity terminology and
   Loogle for `KernelFork.IsLimit`. The proof already uses the appropriate Mathlib
   constructors `ofι'` and `ofMonoOfIsZero` and the existing sectionwise theorem;
   no missed direct replacement was found. The two added imports are proof-only,
   and retained public imports occur in the signature. Checked all seven old
   proof dependencies against the report, including the transitive local-ring node
   and the removed abstract exact-sequence node. Read `dag/units/sk-prop-cd.json`:
   its realized statement and step lists are empty, and this kernel assembly does
   not bypass any recorded realization. Verdict: pass.
5. DAG agreement: only `proof`, `proof_deps`, and `proof_origin` differ in the node.
   Its unchanged Lean statement matches the byte-identical signature. Its three
   proof steps describe the prime-field reduction, natural additive lift, and empty
   case exactly; the union of their uses is `lem-sc-as-kernel-sections`.
   Verdict: pass; no new-node requirements apply.

Second-reading changes: no Lean or node edits. Completed the explicit old-dependency
pruning list, distinguished direct pruning from ledger-measured global pruning,
and documented the observed imported `sorryAx` instead of implying axiom-completeness.
