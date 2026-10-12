## What changed

Proved `AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image` in
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage`, preserving its exact signature
and visibility. Added only proof imports:
`Sheaf.AlgebraicGeometry.FieldEquivariantGermsOnePoint`. The second reader removed
the redundant proof import `Mathlib.Algebra.Category.Grp.FilteredColimits`: the
required filtered-colimit instance is already available through the other imports.

For the converse, the canonical filtered-colimit comparison identifies the underlying
set stalk of an abelian sheaf with its abelian stalk, preserving germs. Transport the
supplied representation action through this comparison and the supplied isomorphism.
An invariant vector gives a constant covariant family on the lifts to T. The existing
`AlgebraicGeometry.Scheme.onePoint_selected_lift_section` supplies a section with this
prescribed germ. Terminality proves that T has a single underlying point; the supplied
lift proves nonemptiness. The reverse implication directly extends a Galois automorphism
to Omega, proves that it leaves the terminal lift unchanged, and applies hi.

The parent node's proof and proof_deps now describe this actual proof. The theorem-local
unused-variable linter option preserves the original names `hτ` and `hx` inside the
supplied compatibility condition; those nondependent binders would otherwise warn once
the enclosing proof is filled. All public imports remain as before.

Validation: the item compiles without errors or warnings through lcompile.py. The retained added proof import
is used; compilation also succeeds without the redundant filtered-colimit import. The final delivery dry run checks the axiom probe, signatures, node
record and import cycle. No data definition was added or changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image`
(node `aux-etale-global-sections-image`). No sorry remains in the item module.
Added 0 holes and split off 0 statements.

This proof uses existing named library results; it does not claim that their transitive
proof dependencies have all been completed. In particular, the selected-lift theorem
has a proved body but depends on existing geometric-point comparison and invariant-section
results. No additional unproved theorem is introduced by this delivery.

## No longer needed

Removed the worker-added redundant proof import
`Mathlib.Algebra.Category.Grp.FilteredColimits`. No original imports or
proof-dependency nodes were removed. The original
`lem-exc-galois-automorphism-extension` remains used. No new modules or new nodes are
included in the delivery. The existing selected-lift reconstruction retains the finite
separable/Galois descent route of Tag 04JM internally, so no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step node named only automorphism extension, leaving its converse's
finite Galois reconstruction implicit. Existing
`lem-exc-field-equivariant-germs-one-point-selected-lift` supplies that reconstruction
for arbitrary algebraically closed Omega, including transcendental extensions. Although
`exists_fieldSection_of_invariant_germ` and `fieldSections_stalkInvariants` themselves
assume algebraicity, the selected-lift theorem already constructs the relative algebraic
closure and transports the germ formulas. It therefore fits this item after the proved
forgetful-stalk comparison, without a new geometric reconstruction statement.

No existing statement, definition, target, public import, or unit realization changed.
The assigned unit record has no realized statement/step nodes bypassed by this proof.

## Second reading by F1

1. **Interface unchanged — pass.** Diffed the sole delivered module against the
   repository version and compared the complete theorem signature byte for byte;
   it is identical, including `hτ`, `hx`, all universes, field instances, arbitrary
   algebraically closed Ω, terminality, the equivalence, and the stalk/action
   compatibility. The node's `lean.statement` equals that exact signature.
   No definitions, visibility, public imports, target statements, or change records
   were added or altered. Only this module and its existing node are delivered;
   the earlier decomposition files are confined to scratchpad and are excluded.
2. **Proof and axioms — pass.** Compiled the delivered file with `lcompile.py`
   without errors or warnings. A scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image`
   reports precisely `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter is from existing open dependencies, not a hole in this module.
   There are no `sorry`, axioms, unsafe declarations, opaque declarations, external
   implementations, or data definitions in the delivered module. The local `e`
   uses a proved bijectivity result for the actual canonical comparison `c`;
   the obtained section is used only to prove an existential proposition.
3. **Split statements — pass, none.** No new statement, module, node, or hole is
   added. Read `onePoint_selected_lift_section` and its node: its hypotheses allow
   arbitrary algebraically closed Ω and its conclusion is the prescribed germ at
   the selected lift of a nonempty one-point etale scheme. Here `hj` makes `T.left`
   a subsingleton and the supplied lift gives nonemptiness. The comparison `he`
   proves that action transport preserves every germ; `hi` gives `hρ`, and
   invariance of `v` gives covariance of the constant family. Thus the cited result
   supplies exactly the required section. Empty `T` is excluded by the given lift;
   zero sheaves, trivial Galois groups, imperfect fields, and transcendental Ω
   require no extra hypothesis. No arbitrary witness is turned into public data.
4. **Shortest route and pruning — pass after repair.** Read Stacks
   [Tag 04JM](https://stacks.math.columbia.edu/tag/04JM),
   `lemma-global-sections-point`, including its direct finite Galois descent proof,
   and [Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ),
   `lemma-equivalence-abelian-sheaves-point`. Searched Mathlib, upstream
   WeilConjectures, and `lean/Sheaf` for fixed-fiber/global-section comparisons,
   and independently queried LeanFinder with alternate wording. The nearby
   `nonempty_iso_etaleFieldSections_invariants` requires algebraicity of Ω and
   cannot prove this statement as given; the parent global-sections comparison
   imports this item and cannot be used without a cycle. The selected-lift theorem
   retains the source's descent route and handles the missing generality. Removed
   the redundant `Mathlib.Algebra.Category.Grp.FilteredColimits` import after a
   scratch compilation without it succeeded. All original public imports serve
   the signature, and the original automorphism-extension dependency remains
   used, so no original dependency node is pruned. Read
   `dag/units/sk-thm-br.json`: its realized statement and step lists are empty,
   and none is bypassed. The selected-lift node belongs to `sk-prop-h2` and is
   used as a tool for invariant-germ reconstruction; the assigned unit provides
   no competing realization for that step. No `tool_uses` field was edited.
5. **DAG agreement — pass.** Compared the old and delivered node. Only `proof`,
   `proof_deps`, and `proof_origin` change. Read each new proof step against the
   Lean: terminality supplies `hj` and the one-point instances; Mathlib's canonical
   filtered-colimit comparison supplies `e` and `he`; selected-lift reconstruction
   supplies the invariant section; automorphism extension plus the base-map
   identity and terminality supplies unchanged-lift invariance. The two cited
   node declarations are used, and their union is exactly `proof_deps`.

Second-reading changes: removed one redundant proof import and corrected the
report's import claims. The theorem proof, signature, and DAG proof route were
otherwise retained.
