## What changed

Proved `TopCat.Sheaf.constantSubsheaf_quotient_gluing` with its original
signature, visibility and docstring unchanged. Glue the family which is
`π(s i)` on top-labelled opens and zero on lower-labelled opens. The mono
into the constant integer sheaf gives top-top compatibility; zero stalks
and section extensionality give compatibility on all other overlaps.
The one remaining proved private helper,
`TopCat.Sheaf.integerExtension_of_section`, constructs the integer extension
map and computes its value on every contained open.

Repair of the return at head 989c5ce08: removed both duplicate helpers
`TopCat.Sheaf.extensionSection_naturality` and
`TopCat.Sheaf.extensionSection_counit`. Added the proof-only
`import all Sheaf.Topology.AbelianSheafLocalIntegerGenerator` and use its
existing private `TopCat.extensionSection_naturality` and
`TopCat.extensionSection_counit` directly. Lean's `import all` makes these
private lemmas available without changing their module or visibility.
The surviving helper needs section values on every subopen, which the
public local-integer-generator theorem's germ conclusion does not supply.

Updated the existing node's proof, proof dependencies and proof origin to
record this reuse. No other module, definition or existing signature changes;
no new nodes, holed statements or change records are introduced.
The original public imports remain. The proof-only zero-group import supplies
`AddCommGrpCat.isZero_iff_subsingleton`.

## Proved and sorry left

Closed 1 original hole: `TopCat.Sheaf.constantSubsheaf_quotient_gluing`
(node `lem-sc-constant-subsheaf-quotient-gluing`). No `sorry` remains in the
item and no hole is added elsewhere. The remaining private helper
`TopCat.Sheaf.integerExtension_of_section` is proved. This is a complete
proof, with no split-off statements. The imported section identities and
their module are already proved.

## No longer needed

Removed original proof import `Sheaf.Topology.PresheafModuleStalkFunctor`
and proof-dependency edge `def-weil-pbc-module-stalk`. Mathlib's abelian-group
stalks and section extensionality suffice. The node remains in statement
dependencies, which this delivery does not change. This is local pruning,
not a claim that every target stops using the module.

Removed both duplicate extension-section helper declarations and their
local proofs; use the existing ones instead. No other original imports,
nodes or modules are pruned. The constant-sheaf and extension-by-zero
nodes remain needed, and the local-integer-generator module is now explicitly
needed for its two identities. Separate top-union gluing and a restricted
zero-object argument are unnecessary; one compatible cover suffices.
The unit record has no realized proof steps requiring the two-stage route.

## Where the brief, the DAG or earlier work was wrong

The returned delivery and its earlier second reading incorrectly treated
private library helpers as unavailable and copied their proofs. The repair
uses Lean's supported `import all` to access both lemmas directly, resolving
both duplicate-statement findings without adapting another module.

No mathematical statement error was found. The DAG's two-stage gluing route
is longer than necessary; the single-cover proof preserves the unit route.
The existing node now records the actual dependency on the reused identities.
The superseded second reading has been removed for a fresh independent reader.

## Second reading by V3

1. Compared the delivered module with the repository using `diff -u`, and
   compared the existing theorem signature byte for byte: identical. The
   original public imports, visibility, docstring and all definitions are
   unchanged. The only additional declaration is a proved private helper.
   No change record or forced adaptation is needed. Verdict: pass.

2. Compiled the delivered module with `lcompile.py`: exit 0, no warnings
   (4.1 seconds). Refreshed scratchpad/AxiomCheck.lean from the actual
   delivery, removing the obsolete duplicate helper proofs from that scratch
   file, and compiled it separately. `#print axioms` for
   `TopCat.Sheaf.constantSubsheaf_quotient_gluing`,
   `TopCat.Sheaf.integerExtension_of_section`, and the imported private
   `TopCat.extensionSection_naturality` and `TopCat.extensionSection_counit`
   reports only `propext`, `Classical.choice`, `Quot.sound`. There is no
   `sorry`, forbidden declaration, or data definition in the delivered code.
   The extension morphism is explicitly constructed by sheafification and
   the counit; the glued section comes from proved unique gluing.
   Verdict: pass.

3. No statements are split off and no holes are added. Read the new private
   helper: it computes the image of integer one on every contained subopen,
   whereas the existing public local-generator theorem only supplies some
   preimage in each stalk. Thus it is not a duplicate of that theorem.
   Searched with fresh Lean Finder, Loogle and grep queries, and read the
   local-generator module, extension-by-zero definitions, and relevant
   Mathlib declarations. No existing theorem with the helper's section-value
   conclusion was found. The two existing section identities are reused by
   `import all`, with no copies. Checked empty U and V, the zero section,
   an empty indexing family, b=0, and absent top labels: the construction
   and compatibility proof include these cases. Verdict: pass.

4. Read the proof from the target down. It uses Mathlib section extensionality
   and unique gluing directly, then the proved section-value helper; no
   unproved library statements are needed. On top-top intersections the
   constant values agree and the component mono cancels; every other
   intersection lies in the lower union and has equal sections by equal
   germs. The direct cover argument avoids the unnecessary intermediate
   top-union gluing. All added imports are proof-only. The original proof
   dependency `def-weil-pbc-module-stalk` and its module are the only original
   dependency removed, and both are listed under No longer needed; the other
   two original proof dependencies remain. Read the unit record
   `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, and its steps are empty, so this local change
   bypasses no required unit step. The referenced blueprint markdown is not
   present locally; the unit's recorded statement and steps were available.
   Verdict: pass.

5. Compared the node JSON files: only `proof`, `proof_deps` and `proof_origin`
   differ. Read all three new proof steps against the Lean proof, including
   the dependency on the imported local-generator identities; their uses
   have exactly the recorded union of proof dependencies. No new node is
   needed for an unfinished theorem, since none is introduced. The existing
   statement, statement dependencies and Lean declaration record are
   unchanged. Verdict: pass.

Second reading changed the report and refreshed the scratch axiom check.
No delivered Lean or DAG repair was necessary. Closed one original hole,
added zero holes; this is a proof, not a decomposition.
