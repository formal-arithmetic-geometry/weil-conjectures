## What changed

Proved `AlgebraicGeometry.formalCompletion_map_surjective_of_proper` in
`Sheaf.AlgebraicGeometry.FormalCompletionMapSurjectiveProper`, preserving its signature.
The proof follows Stacks Tag 0883: internal Hom is coherent; the existing completion/internal-Hom
comparison supplies compatible quotient sections; degree-zero formal functions algebraizes them;
its specified projection equalities and the Hom comparison factorization identify the resulting
completion with the original morphism. The last identification is a componentwise Lean proof,
cancelling the cokernel projection and using `cokernel.π_desc`.

Three private, fully proved helpers construct a section family by restriction from the top open,
show evaluation at the top determines the family, and express naturality of the internal-Hom
sections equivalence. No data are chosen by a new definition from an unproved existence theorem.
The theorem-local transparency option avoids expensive unfolding during definitional equality;
the proof compiles within the default heartbeat limit. No public import or interface changed.

Updated the item's DAG proof with these steps and its actual coherence dependency.
The declared source file is absent from this machine, so its short proof was read at the primary
Stacks page https://stacks.math.columbia.edu/tag/0883 instead.

## Proved and sorry left

Closed the sole local hole:
`AlgebraicGeometry.formalCompletion_map_surjective_of_proper`
(node `lem-weil-pbc-formal-completion-map-surjective-proper`).
One original hole closed; zero new holes. No `sorry` remains in the delivered module.

This is a completed proof from existing named dependencies, not a new decomposition.
It still depends on existing unproved theorems:
`AlgebraicGeometry.Scheme.Modules.isCoherent_homObj`
(`lem-weil-pbc-coherent-sheaf-hom-coherent`),
`AlgebraicGeometry.completion_internal_hom_bijective`
(`lem-weil-pbc-completion-internal-hom`), and
`AlgebraicGeometry.globalSections_formalFunctions_complete_base`
(`lem-weil-pbc-formal-functions-complete-base`). None was edited or newly holed.

Validation: the single-file local compile passed without warnings in about seven seconds after
import pruning; the final dry run runs the delivery axiom probe and preflight as well.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.Coherent`: its definitions are already publicly available through
  `CoherentFormalModule`; node `pqf-def-coherent` is still used transitively.
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`: this proof uses categorical
  epimorphy of a cokernel projection, not surjectivity on affine sections;
  node `lem-weil-pbc-quasi-coherent-module-cokernel-image` is not a direct dependency here.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: the used internal-Hom API
  is publicly imported by `CompletionInternalHom` and `CoherentSheafHom`;
  node `def-pur-sheaf-hom` remains needed.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: no affine tilde equivalence,
  pullback, or basic-open localization is used in this proof. Its nodes
  `lem-weil-pbc-module-pullback-quasi-coherent` and
  `lem-weil-pbc-affine-module-basic-open-localization` are not direct dependencies here.

No original DAG proof dependency was discarded. Removed imports may remain in the transitive
closures of the retained modules; this report does not claim those modules are globally unreachable.
The unit statement and all realized unit steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous item's one-step proof listed the internal-Hom definition but omitted the theorem that
internal Hom is coherent, although formal functions requires a coherent object. Added
`lem-weil-pbc-coherent-sheaf-hom-coherent` to the proof dependencies and spelled out its use.
No false statement, signature change, forced adaptation, or tool workaround was needed.

## Second reading by H3

1. **Visible changes.** I diffed the delivered module against the repository version. The
   existing theorem signature is byte-for-byte unchanged; only its proof, private helpers, and
   proof-only imports changed. The DAG node keeps the same statement and records the added
   coherence dependency used by the proof.

2. **Proof and axioms.** The module compiles with `lcompile.py` without warnings. It contains no
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or kernel-skip construct.
   The proof uses only existing named results and categorical extensionality; no definition takes
   data from an unproved existence statement. The delivery axiom probe is included in preflight.

3. **Statements and dependencies.** No new public statement was introduced. The three private
   helpers are proved by restriction compatibility, section extensionality, and definitional
   naturality respectively. The theorem remains exactly the stated surjectivity result, and the
   node's `proof`, `proof_deps`, and `proof_origin` match the implemented route.

4. **Pruning and route.** I checked the removed imports against the proof: none is referenced
   directly, while all retained dependencies are used. The unit statement and every realized unit
   step remain represented in the node; the shorter componentwise cokernel-epimorphism argument
   stays below the unit level.

5. **Source and prior work.** The proof follows Stacks Lemma 0883 together with the existing
   completion/internal-Hom and formal-functions declarations. The earlier DAG omission of the
   internal-Hom coherence theorem is corrected in the node. No statement dispute or forced
   adaptation was found.

I changed only the report to add this second-reading record; the Lean proof and DAG changes were
   already reviewed above. The dry run is required to pass before delivery.
