## What changed

Replaced the first worker's redundant tail-isomorphism auxiliary theorem with a
real reduction to the existing, completely proved integer finite-column theorem
`HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns`.

The item now transposes the bicomplex, extends both indices by zero, proves its
outer support bounds 0 and N, transports the given column quasi-isomorphisms
through extension, and applies the integer comparison theorem. Mathlib's
extension reflection and signed total symmetry transport the conclusion back.
The natural-number total symmetry has a private construction, used as a local
instance inside the proof, and the extension helpers are private,
constructed explicitly, and completely proved. No definition chooses data from
an unproved existence statement.

Added the proof-only import `Sheaf.Algebra.Homology.FirstQuadrantTotalExtension`.
Its one named open theorem, `HomologicalComplex₂.totalMap_extend_nat_arrow_iso`,
is the independent natural isomorphism commuting extension and totalization;
it has no finite-row bounds or columnwise quasi-isomorphism hypothesis. Added
proof-only imports of BicomplexColumns and Mathlib TotalComplexSymmetry.
Restored the original DoubleComplexTotal proof import, whose proved
`hasTotal_of_firstQuadrant` is actually used. All original public imports remain.

## Proved and sorry left

Closed the original local hole in
`HomologicalComplex₂.quasiIso_totalMap_of_columns_of_finite_rows`
(node `lem-sc-finite-row-total-column-comparison`) by the reduction above.

Added one hole in
`HomologicalComplex₂.totalMap_extend_nat_arrow_iso`
(node `lem-sc-total-extension-nat-arrow-iso`, module
`Sheaf.Algebra.Homology.FirstQuadrantTotalExtension`). This is the only `sorry`
in the delivered modules. Its docstring gives the construction in all degrees,
inverse equations, sign check, and naturality square.

This delivery is a decomposition: one old local hole closed and one genuinely
smaller transport hole added; net zero. The original theorem still has `sorryAx`
through that transport theorem and is not counted as an axiom-free proof.
The previous sandbox-only auxiliary hole was discarded, not counted as a closure.
The integer comparison and `hasTotal_of_firstQuadrant` use only `propext`,
`Classical.choice`, and `Quot.sound`, as checked with `#print axioms`.

## No longer needed

Removed the unlanded sandbox declaration
`HomologicalComplex₂.quasiIso_totalMap_of_columns_of_finite_rows_aux`
and its unlanded node `lem-sc-finite-row-total-column-comparison-aux`.
The earlier `...-le` helper was also absent from the repository baseline and is
not delivered. Neither removal counts as pruning a baseline module or node.

No repository import or old proof dependency is pruned. The original sole
`proof_deps` entry, `def-sp-double-complex-total`, remains genuinely needed for
`hasTotal_of_firstQuadrant`. A trial explicit ExtendHomology import was removed
because it is already available through the retained imports. The original
public imports and proof import of DoubleComplexTotal are retained.

## Where the brief, the DAG or earlier work was wrong

The first worker's auxiliary theorem assumed the original hypotheses plus that
maps between zero tail objects are isomorphisms. The added condition follows
immediately from those original hypotheses; consequently its open theorem
merely restated the item. Supplying that condition did not implement the finite
filtration argument. The auxiliary docstring also used the obsolete `...-le`
blueprint identifier and exceeded the line-length limit.

The repository plan itself explicitly suggested integer extension and the
existing finite-column theorem. The second reading implements that route rather
than adding a second comparison theorem. The existing node's proof metadata is
updated to match the actual extension, comparison, and symmetry proof.

## New nodes

`lem-sc-total-extension-nat-arrow-iso` records the new transport theorem in
`FirstQuadrantTotalExtension.lean`. It is a strict part of the argument:
reindexing two ways of forming the same diagonal coproduct, independent of any
quasi-isomorphism or finite-row hypothesis. Source: Stacks Definition 12.18.3
(Tag 012Z), with the reindexing proof written by J2. Searches with LeanFinder,
Loogle, direct ripgrep in both library roots and Mathlib, and DAG search found
extension-homology and total-symmetry tools but no existing declaration of this
natural arrow isomorphism. LeanSearch was attempted and returned an unavailable
service error, recorded without a mathematical verdict.

`lem-sc-integer-finite-column-total-comparison` records the existing complete
upstream theorem `total.quasiIso_map_of_finitely_many_columns`, with
`lean.existing: true`; no module or hole is added for it. The other bounded-above
comparison node records a different theorem requiring upper bounds on both
indices, unavailable here. The finite-column theorem's complete induction proof
was read, including the empty interval, the single-column shift, degreewise
splittings, and the five-lemma step. Mathlib searches returned generic
quasi-isomorphism results; direct source search found the exact declaration.

No statement or definition change record is required: all existing signatures,
definitions, and public imports are unchanged.

## Second reading by J2

1. Compared both delivered modules against the repository. The new transport
   module has no repository counterpart. For the existing module, a byte-for-byte
   comparison of the entire original theorem signature through `:= by` passes:
   category, universes, abelian hypothesis, double-complex shapes, f, N, hK, hL,
   hf, and total-map conclusion are unchanged. Its original docstring is restored.
   All added imports in that module are proof-only; no public definition or
   existing declaration is changed. Verdict: pass after removing the redundant
   unlanded auxiliary theorem.

2. Both final modules compile cleanly through `lcompile.py --all` (approximately
   1.4 and 2.2 seconds per file). A scratch copy with explicit `#print axioms`
   checks the item, transport theorem, integer comparison, and first-quadrant
   total existence. The item and transport have only the three standard axioms
   and the permitted `sorryAx`; the two reused proofs have only standard axioms.
   The delivered source has exactly one named theorem with `:= by sorry`, no
   forbidden declaration or attribute, and no `sorry` in a definition. The
   transport isomorphism is eliminated only inside a proposition proof, never
   used to define library data. Verdict: valid partial proof, not a completed
   axiom-free comparison theorem.

3. Tested the new transport statement by its diagonal construction: for the zero
   bicomplex all terms are zero; for a single object in (a,b) both constructions
   place it in integer total degree a+b; in degree 0 the sole surviving summand
   is (0,0); in negative degree every integer summand is zero, including the
   boundary differential -1→0. On a nonzero vertical differential the integer
   and natural total signs both equal (-1)^a. The summand maps are natural, so
   the statement covers arbitrary f and imposes no hidden finite-row assumption.
   These are mathematical edge-case checks, not claimed formal proofs of the
   remaining hole. Read Stacks 012X/0133 for the comparison route and 012Z's total
   construction; the transport docstring supplies the full reindexing argument.
   Checked the recorded searches with different extension/reindexing queries.
   The original auxiliary failed the strict-part requirement and was removed;
   the new hole concerns only extension/totalization compatibility. Verdict: pass.

4. The existing finite-column theorem supplies the finite-filtration induction,
   so no new open filtration comparison is introduced. Bounds and extension
   quasi-isomorphisms are proved, and the signed total-flip naturality is checked
   on every coprojection. Import minimization was tested by compilation: the
   explicit ExtendHomology import is redundant, while TotalComplexSymmetry is
   necessary. Every old proof dependency is accounted for above.
   `dag/units/sk-thm-picard-duality.json` has empty realized statement and step
   arrays; no realized unit node or chapter route is bypassed or edited.
   Verdict: the plan's explicit integer-extension alternative is kept.

5. Opened the item and new node records alongside the final Lean. The item's
   three proof steps now follow extension/support, the existing comparison,
   and transport/symmetry. Its `proof_deps` is precisely the union of those
   steps' node references. Both new nodes carry source, complete proof steps,
   actual search outcomes, creation/blueprint/chapter/unit fields, and verbatim
   Lean signatures. The transport node names its own new module; the finite
   comparison node reuses the existing upstream declaration. No unrelated
   existing-node fields are changed. Verdict: pass.

Changes made by this reader: removed the equivalent tail-isomorphism auxiliary
and its stale node; restored the original signature and docstring; implemented
integer extension/support and column quasi-isomorphism transport; reused the
proved finite-column comparison; supplied and proved the local natural total symmetry
and its naturality; isolated only the totalization/extension arrow isomorphism
as an open theorem with a full proof docstring and node; corrected all metadata,
imports, and the report's decomposition accounting.

The first dry run flagged the added global `open ComplexShape` command as an
interface change. Removed that command, qualified its names explicitly, and
replaced the private instance registration by a private construction installed
only inside the comparison proof. No interface change or change record is needed.
