## What changed

Repair of return X-9c722 (head 9c7227545): expanded the factorization node's
third proof step to describe Core's private helper argument and cite its actual
mathematical dependencies. Removed the unused Core existential theorem from
proof_deps and corrected the report's dependency claims. The Lean import all
and helper application are unchanged.

Repair of return X-54ab0 (head 54ab01c55): removed the duplicated private
isIso_unit_constantSheaf_of_generic_residueFieldIso declaration from
NormalizedGenericDataWithFactorization. Reuse the existing proved helper with
`import all Sheaf.AlgebraicGeometry.NormalizedGenericDataCore`. This is a
proof-only import: Core is untouched and no existing signature or visibility
changes. Removed the now-unused Coherence and FinitePushforward proof imports.
Updated the factorization node's proof and proof_deps to record the reuse.
The delivery tool rebases the repaired sources on current origin/sheaf-dag.

Corrected AlgebraicGeometry.Etale.normalized_generic_data_lifts to retain the finite
kappa(x)-algebra structure on K and the normalization square. Proved it with
Scheme.SpecToEquivOfField, IsAlgClosed.lift, Spec.map_comp_assoc and AlgHom.commutes.
The original statement was false, so this is an explicit interface repair, not a
proof of that false signature.

Added Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization, whose fully
proved construction reuses the existing core construction but retains its hAlg,
hfin and hcomp witnesses. The old Core module and its signatures are untouched.
Adapted only the necessary proof lines of
Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData; its statement
and visibility are exactly unchanged. Its proof retains the full source route.

Change record: coord/changes/normalized-generic-data-residue-field-square.md.

## Proved and sorry left

Original hole: AlgebraicGeometry.Etale.normalized_generic_data_lifts
(new-normalized-generic-data-lifts). Its corrected source-faithful statement is
now proved without a local sorry. The old false statement is not claimed proved.
This is a statement repair followed by a proof, not a decomposition or a claim
that adding hypotheses alone proves the original statement.

Also proved the new
AlgebraicGeometry.Etale.exists_constructible_module_normalized_generic_data_with_factorization
(new-normalized-generic-data-with-factorization). The unit-transport helper is
reused from Core; this delivery neither declares nor reproves it.
The adapted exists_constructible_module_normalized_generic_data remains fully
proved with its exact existing signature.

Holes added: zero. Split off: zero. Sorries left in delivered modules: none.
Existing imported theorem dependencies may still rest on sorry; none were added
or changed by this delivery. The lifting proof itself uses only Mathlib.

## No longer needed

Removed the public import Sheaf.AlgebraicGeometry.NormalizedGenericDataCore from
the item, replacing it with the four imports its statement uses. Removed the
Core proof import from ConstructibleModuleNormalizedGenericData, replacing it
with NormalizedGenericDataWithFactorization.

Core remains imported for its private helper; its existential theorem new-normalized-generic-data-core is not used: the factorization
constructor now imports Core to reuse its private unit-transport theorem.
The earlier pruning claim for Core was wrong and is withdrawn. Removed the
duplicate helper and its standalone proof work, and the constructor's direct
Coherence and FinitePushforward proof imports. Their mathematical dependencies
remain reachable through Core; no whole module is claimed pruned from the target
closure. No blueprint unit statement or realized step is bypassed.

The old lifting node's circular proof dependency on its own caller,
lem-weil-pbc-constructible-module-normalized-generic-data, is no longer needed.
Its proof now uses the existing Mathlib algebraic-extension embedding node and
the geometric-point definition. No new pointwise or equivalent split-off hole
is introduced. The previous NormalizedGenericDataLiftSingle proposal stays removed.

The second reader also removed the redundant public import
Mathlib.AlgebraicGeometry.Sites.EtalePoint from the new WithFactorization module;
its statement and proof compile without it. The caller's former direct proof
 dependencies prop-constructible-pullback,
lem-weil-pbc-finite-locally-constant-module-values,
lem-weil-pbc-constructible-field-finite-separable-constant,
def-weil-pbc-etale-constructible-sheaf,
lem-weil-pbc-normalization-in-residue-field-extension,
lem-weil-pbc-inverse-image-composition, lemma-constructible-pullback-constant,
lem-weil-pbc-normal-constant-generic, def-weil-geometric-point,
def-weil-pbc-inverse-image, and
lem-weil-pbc-algebraic-extension-embeds-algebraically-closed are now reached
through the constructor or lifting step, rather than direct proof dependencies;
this is not a claim that these nodes are pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied a private helper already stated and proved in Core.
The landing checker correctly rejected that duplicate. `import all` makes the
existing private theorem available for proof use without changing its visibility.
The previous claim that Core left the import closure was consequently incorrect.

STATEMENT-DISPUTED (old signature): the sheaf hypotheses do not force g followed
by nu to lie over x. The two-component zero-sheaf counterexample in the earlier
report applies. The core proof already produced the necessary finite residue-field
algebra and factorization, but omitted them from its existential statement.
The old node's proof plan cited its caller, an import cycle, and supplied no way
to extract the missing geometric data from the actual hypotheses.

This repair follows Stacks Tag 09Z6 (lemma-constructible-maps-into-constant), proof
of (1), the finite K/kappa(x) extension and normalization paragraphs, transferred
to (3). Source read at https://stacks.math.columbia.edu/tag/09Z6 because the local
literature tex is absent. The top-level existential result keeps every original
hypothesis and conclusion. The corrected local statement now exposes exactly
the geometric information used by that proof.

Edge cases checked: X empty has no x; zero F and M impose no geometric restriction
and hence cannot replace the added square; identity residue-field extensions lift;
finite inseparable extensions also admit the required embedding into Omega by
IsAlgClosed.lift. No separability or normality hypothesis is needed by the lifting
step itself. The fully proved constructor supplies the stronger finite separable
data already used by the original proof.

LeanSearch was unavailable (Internal Server Error); Loogle and LeanFinder found
IsAlgClosed.lift, and grep found the residue-field point equivalence. All new-node
search records describe searches actually run in this session.

## New nodes

new-normalized-generic-data-with-factorization: fully proved construction of the
existing normalized generic data retaining its finite kappa(x)-algebra and square.
It is not a renamed lifting theorem and contains no sorry. Its proof is the
existing core argument with three witnesses preserved in the existential.
The constructor reuses Core's existing private unit-transport theorem through
import all; its node expands the helper's argument and cites the normal constant generic theorem, inverse-image composition and residue-field definition.

The corrected lifting node carries statement_change and lists every base citer.
The caller node records the two actual constructor/lifting steps of its Lean proof.
Change record: coord/changes/normalized-generic-data-residue-field-square.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData: the old final
application supplies M where the corrected theorem expects the residue-field
algebra a, causing an application type mismatch. Its old core existential lacks
a, ha and hcomp. Replacing the proof constructor import and invocation and
extending the existential pattern are necessary to obtain these witnesses; the
final application passes them. No statement, binder, universe or visibility
changes in this adapted module. deliver3.py checks the original against the
compiled baseline and changed dependencies and appends the exact compiler error.

## Earlier second reading (a previous round; superseded)

1. Compared each delivered Lean module with the repository version. Existing declarations in the adapted caller retain their signatures and visibility; the lifting theorem's intentional statement change is documented in the change record. Verdict: pass.

2. Compiled all three delivered modules with lcompile.py. There are no `sorry`s, axioms, unsafe declarations, or hollow definitions in the delivered Lean files. The lifting proof uses the supplied algebra and square, `IsAlgClosed.lift`, and `Spec.map` functoriality. Verdict: pass.

3. Checked the corrected lifting statement on empty schemes, zero sheaves, identity residue-field extensions, and finite inseparable extensions. The added residue-field algebra and commuting square are necessary; the factorization argument is valid without separability. The constructor statement is strictly stronger data than the old core existential and is fully proved. Verdict: pass.

4. Checked the proof route against the DAG and imports. The unit route through finite field trivialization, normalization, generic constant unit, and geometric lifting is retained. The old core import is replaced by the factorization constructor; the lifting module exposes only imports needed by its statement and proof. Verdict: pass.

5. Checked the DAG nodes and change record against the Lean declarations, including the statement change, proof dependencies, proof origin, and forced caller adaptation. The factorization node is a genuine construction retaining witnesses, not a renamed lifting theorem. Verdict: pass.

Changed: added this second-reading record only; no Lean proof or statement was altered during review.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData
Original against changed dependencies failed:
```
/tmp/forced-adaptation-k4ectrom/lean/Sheaf/AlgebraicGeometry/ConstructibleModuleNormalizedGenericData.lean:76:61: error: Application type mismatch: The argument
  M
has type
  ModuleCat Λ
of sort `Type (u + 2)` but is expected to have type
  Algebra (↑(X.residueField x)) K
of sort `Type u` in the application
  normalized_generic_data_lifts Λ F hF x Y ν hν K hK g M

(with the modules compiled into /tmp/forced-adaptation-k4ectrom/.lbuild) [7.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier independent reading (superseded by repair X-54ab0)

1. Compared all delivered modules with the repository. The only existing signature
change is the explicitly recorded repair of normalized_generic_data_lifts; the
caller signature, visibility and docstring are byte-for-byte unchanged. The new
constructor retains the core argument's algebra, finiteness and square witnesses.
The disjoint-two-components, zero-sheaf example refutes the old lifting statement.
Verdict: pass as an interface repair, not a proof of the former false statement.

2. Compiled all three modules through lcompile.py without errors or warnings.
Scanned the delivered sources for sorry, axioms, unsafe, opaque, extern and
implemented_by: none. Scratch #print axioms checks cover the lifting theorem,
new constructor, private unit-transport helper and adapted caller. The lifting
uses only propext, Classical.choice and Quot.sound; the others additionally use
sorryAx from existing upstream theorem dependencies. No definition or arbitrary
existential-witness-based data definition is introduced. Verdict: pass.

3. No statements with sorry were split off. Checked the fully proved constructor
against the original core proof, including the private helper, and the lifting
against the finite algebra and commuting square. Empty X admits no x; zero
coefficients do not determine a geometric square; identity and inseparable finite
extensions still lift into an algebraically closed field. Fresh grep, Loogle and
LeanFinder searches with residue-field and field-embedding queries confirm the
Mathlib tools used and find no replacement for the combined sheaf construction.
Verdict: pass; zero holes added.

4. Read Stacks Tag 09Z6 at https://stacks.math.columbia.edu/tag/09Z6 and checked
its finite residue-field extension and normalization argument. The source route
through field trivialization, normalization, normal generic constant unit and
lifting is retained. Read sk-thm-p1.json: none of its realized steps is bypassed.
Confirmed the old Core module's only importers are the two adapted files and
listed the displaced direct proof dependencies above. Removed the redundant
EtalePoint public import from the new constructor and checked it compiles.
Verdict: pass.

5. Checked all three node records: statements match the corrected lifting,
stronger constructor and unchanged caller; proof_deps is the union of step uses;
proof_origin records the actual agent proof and source. New-node source, searches,
created, blueprint, unit and Lean fields are present. The statement change and
forced caller adaptation are documented; no base DAG node cites the old lifting
node. Made the lifting and constructor lean.statement fields and the change
record's old/new signatures verbatim multiline source text. Verdict: pass.

Changed in this second reading: removed one redundant constructor import;
normalized recorded signatures to verbatim source; expanded pruning accounting;
added this independent review. No Lean proof or theorem signature was changed.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData
Original against changed dependencies failed:
```
/var/tmp/forced-adaptation-o38605tk/lean/Sheaf/AlgebraicGeometry/ConstructibleModuleNormalizedGenericData.lean:76:61: error: Application type mismatch: The argument
  M
has type
  ModuleCat Λ
of sort `Type (u + 2)` but is expected to have type
  Algebra (↑(X.residueField x)) K
of sort `Type u` in the application
  normalized_generic_data_lifts Λ F hF x Y ν hν K hK g M

(with the modules compiled into /var/tmp/forced-adaptation-o38605tk/.lbuild) [6.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Earlier second reading (a previous round; superseded)

1. Compared all delivered sources with the repository. The caller signature,
visibility and docstring are byte-for-byte unchanged; its four changed proof lines
and constructor import are forced by the lifting repair. The only existing
signature change is the explicitly documented finite residue-field algebra and
normalization square in normalized_generic_data_lifts (including unused binder
renamings recorded verbatim). The old signature is false on two disjoint field
spectra with zero coefficients and a point on the other component. No target or
existing definition changes. Verdict: pass as a documented intermediate statement
repair; the former false theorem is not proved.

2. Compiled all three delivered modules through lcompile.py: no errors or warnings.
Scanned their sources: no sorry, axiom, unsafe, opaque, extern or implemented_by,
and no new definitions. Scratch #print axioms confirms the lifting theorem uses
only propext, Classical.choice and Quot.sound. The constructor and unchanged
caller additionally depend on sorryAx from existing imported results; this delivery
adds no holes. The repaired constructor reuses Core's existing private helper
through a proof-only import all, without redeclaring it. Verdict: pass.

3. No sorry statements are split off. Compared the new fully proved constructor
line-by-line with Core: it preserves hAlg, hfin and hcomp, and otherwise follows
the existing construction. The lifting uses the actual supplied algebra, Module.Finite
instance and commuting square, rather than any sheaf hypothesis. Empty X has no
point x; zero coefficients cannot imply the missing square; identity extensions
and finite inseparable extensions admit the same lift. Fresh Loogle search
`IsAlgClosed, AlgHom` finds IsAlgClosed.lift and extension-of-embedding tools;
LeanFinder's residue-field factorization query supplies no combined construction.
Repository and Mathlib rg confirm the existing normalization, residue-field point
equivalence and field-trivialization inputs. No shorter existing theorem supplies
the stronger combined constructor. Verdict: pass; zero new holes.

4. Checked the finite extension and normalization argument against
[Stacks Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6), and read the Core
unit-transport proof and sk-thm-p1 realized fields. The field trivialization,
normalization, generic constant unit and geometric lift route is retained;
no unit statement or realized step is bypassed. Public imports supply statement
symbols; added proof dependencies are plain imports. The report accounts for every
old proof dependency displaced from a direct dependency. Core remains imported
for its private helper; no whole module is pruned from the target closure.
Verdict: pass.

5. Checked all three node records. lean.statement matches source signatures
verbatim, and each proof_deps is exactly the union of its proof-step uses.
The proofs and proof_origin describe the actual lift, retained witnesses and
Core helper reuse. The new node contains source, search, created, blueprint,
chapter, unit and Lean fields. The lifting statement_change records the old
statement and dependencies; the base DAG has no node citing that lifting node.
The change record names the sole Lean caller and explains its forced adaptation.
Verdict: pass.

Changed during this second reading: appended this current review and created a
scratch axiom-check module. No delivered Lean proof, statement, import or node
needed further modification after repair X-54ab0. The lifting hole is replaced by
a proof of its corrected source-faithful statement; the original false statement
is not counted as proved. No holes are added and no modules are claimed pruned.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData
Original against changed dependencies failed:
```
/tmp/forced-adaptation-e3d_ot36/lean/Sheaf/AlgebraicGeometry/ConstructibleModuleNormalizedGenericData.lean:76:61: error: Application type mismatch: The argument
  M
has type
  ModuleCat Λ
of sort `Type (u + 2)` but is expected to have type
  Algebra (↑(X.residueField x)) K
of sort `Type u` in the application
  normalized_generic_data_lifts Λ F hF x Y ν hν K hK g M

(with the modules compiled into /tmp/forced-adaptation-e3d_ot36/.lbuild) [2.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by P2

1. Compared all three delivered modules with the repository and read the change
record. The caller's signature, visibility and docstring are unchanged byte for
byte. The lifting signature's added algebra, finiteness and commuting square,
including renamed unused binders, are explicitly recorded. The former statement
is false for disjoint field spectra with zero coefficients; this is an interface
repair, not a proof of that false statement. No target or definition changes.
Verdict: pass.

2. Compiled all three modules using lcompile.py --all without errors or warnings.
Compiled the scratch ReviewAxioms module: the lifting theorem uses only propext,
Classical.choice and Quot.sound; the constructor and caller additionally use
sorryAx from existing imported results. No delivered source contains sorry,
axiom, unsafe, opaque, extern or implemented_by. There are no new definitions
choosing arbitrary data from unproved existence. The constructor reuses the
existing private Core helper via proof-only import all. Verdict: pass.

3. No statements are split off with sorry. Read the new constructor against Core:
its construction and transport proof are unchanged except that hAlg, hfin and
hcomp are retained. The lift genuinely extends the residue-field embedding using
IsAlgClosed.lift and proves the square by AlgHom.commutes. Checked empty X,
zero coefficients, identity extensions and inseparable finite extensions.
Fresh repository searches find the separate inputs and Core, without a shorter
combined construction. A fresh Loogle field-embedding search was also run.
Verdict: pass; zero holes added.

4. Read Stacks Tag 09Z6, especially its finite separable residue-field extension,
normalization and generic constant sheaf paragraphs. Read sk-thm-p1's realized
steps: this repair bypasses none. The imports distinguish public signature needs
from proof dependencies. The report accounts for old displaced dependencies;
Core remains reachable for its helper and no whole module is claimed pruned.
The forced adaptation test run by deliver3.py confirms the original caller fails
against the repaired lifting signature, whereas the adapted caller compiles.
Its import, constructor call, existential pattern and final application are
precisely the necessary changed lines. Verdict: pass.

5. Read all three delivered nodes, their proof steps and proof_origin, and the
change record. The lifting node records the embedding and point equivalence;
the constructor records the comparison, field trivialization, normalization,
Core helper's normal-unit and composition argument, and constant pullback;
the caller records the constructor and lift. Each proof_deps is the union of
step uses. Statements agree with Lean and the new node has the required source,
searches, creation, blueprint and Lean records. Verdict: pass.

Changed in this second reading: appended this current review only. No further
Lean, import, signature or node repairs were necessary after return X-9c722.
The corrected lifting hole is closed; the former false signature is not counted
as proved. No new holes, no split-off statements, and no whole modules pruned.

## Forced adaptations

### Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData
Original against changed dependencies failed:
```
/tmp/forced-adaptation-m722dfb7/lean/Sheaf/AlgebraicGeometry/ConstructibleModuleNormalizedGenericData.lean:76:61: error: Application type mismatch: The argument
  M
has type
  ModuleCat Λ
of sort `Type (u + 2)` but is expected to have type
  Algebra (↑(X.residueField x)) K
of sort `Type u` in the application
  normalized_generic_data_lifts Λ F hF x Y ν hν K hK g M

(with the modules compiled into /tmp/forced-adaptation-m722dfb7/.lbuild) [3.6 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
