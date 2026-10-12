## What changed
Replaced the sorry proof of `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreData`
with a two-step reduction: obtain strictly henselian affine presentations and residue
factorizations, derive compatibility of the geometric points from `hι`, and obtain the
local ring map by strict henselization functoriality. Added proof-only imports of
`CompatibleStrictHenselizationCoreExistence` and `CompatibleStrictHenselizationCoreCompletion`.
The original declaration signature, docstring and public imports are unchanged.

## Proved and sorry left
Closed one upper hole: `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreData`.
Added two lower holes, both public named theorems with full natural-language proofs:
- `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreExistence`, node
  `compatible-strict-henselization-core-existence`;
- `AlgebraicGeometry.Etale.exists_compatibleStrictHenselizationCoreCompletion`, node
  `compatible-strict-henselization-core-completion`.
This is a decomposition, not a net proof gain: one hole closed, two added (net -1).
No sorry remains in the item's module, and no definitions or arbitrary data chosen from
unproved existence assertions were added. The residue factorization theorem and the
functorial map theorem each express strictly separate parts of the original construction.

## No longer needed
No original imports removed; each is needed by the unchanged statement. The original
node had empty `proof_deps`, so there are no old dependency nodes to prune. Pruned modules:
none. Removed the first worker's completion-module imports of core existence and universal
homeomorphisms: its corrected statement only needs the structural map and henselian API.
These original proposed imports were replaced with direct public imports of those APIs.

## Where the brief, the DAG or earlier work was wrong
The first worker's completion statement was false: it asserted residue factorizations
for arbitrary residue maps without any compatibility hypothesis. On the spectrum of an
algebraically closed field, choose a nontrivial field automorphism for ρA and the identity
for σ; the asserted factorization is false. It also had independent geometric points s
and t with no equation relating them. On a scheme with two disjoint closed components,
choose s and t on different components and g the identity; no structural square exists.
The corrected existence theorem supplies the residue factorizations itself, and completion
requires `s = t ≫ g` and only concludes the functorial local map and its structural square.
The first worker's node records lacked mathematical statements, verbatim Lean signatures,
search records and a parent proof-route update; these have been supplied.

## New nodes
`compatible-strict-henselization-core-existence`: coordinate-ring colimits yield the two
strictly henselian ring presentations. Their residues are separable closures inside Ω;
the integral geometric residue extensions give purely inseparable extensions and hence
universal-homeomorphism residue maps with the required factorizations. Sources:
[04HX](https://stacks.math.columbia.edu/tag/04HX),
[03PS](https://stacks.math.columbia.edu/tag/03PS),
[04DY](https://stacks.math.columbia.edu/tag/04DY).

`compatible-strict-henselization-core-completion`: compatible Ω-geometric points give the
functorial local ring map on arbitrary affine presentations of the strict henselizations,
with structural compatibility. Source: [04GU](https://stacks.math.columbia.edu/tag/04GU).
No change records are needed: only new interfaces were corrected, and no existing interface
or definition changes.

## Second reading by G3
1. Compared every delivered module with the repository version. The only existing module
   has its theorem signature byte for byte unchanged. Its docstring and public imports
   are unchanged; only its proof and two private proof imports differ. New modules have
   no repository counterpart. No target or existing definition changes. Verdict: pass.
2. Compiled all three modules in import order through lcompile.py, without warnings.
   Scratch `#print axioms` copies show exactly propext, Classical.choice, Quot.sound and
   sorryAx for all three declarations. The last is expected from the two named lower
   holes. No axiom, unsafe, opaque, implemented_by, extern or holed definition occurs.
   Verdict: pass as a decomposition, not an axiom-free completed theorem.
3. Tested the proposed completion on nontrivial field automorphisms and incompatible
   components; rejected it as false and repaired it as described above. The repaired
   existence and functoriality claims match the cited Stacks constructions. For identity
   g and compatible points, the induced ring map is the presentation isomorphism; on
   field spectra the ring construction gives the separable closure and the residue
   extension is purely inseparable. With empty base there is no geometric point, so
   the hypotheses have no instances. Neither new theorem repeats the whole item.
   Read the upstream and project strict-henselization APIs and searched with leanfinder,
   loogle and rg using different terminology. Leansearch returned a service error, recorded
   as unavailable without a verdict. No available API closes either construction in a
   few minutes. Verdict: repaired and pass.
4. Read the original proof plan and all structural-map/coordinate-ring declarations.
   No shorter existing construction or localness theorem was found. Kept all original
   public imports needed for the signature; removed unrelated proposed imports from
   completion. `sk-thm-p1` realized statement/steps are unchanged: this is below that
   unit's route, and the surrounding strict-local-model reduction is retained.
   Old proof_deps were empty; no old node is omitted from the pruning report. Verdict: pass.
5. Added the parent node update with both actual proof dependencies. Completed each new
   node's statement, verbatim Lean declaration, source, proof steps, proof_deps, origin,
   search records and creation record. Their definition dependencies are recorded and
   the parent proof assembles precisely their conclusions. Verdict: repaired and pass.

Second reading changed: repaired both split interfaces and the assembly proof; removed
redundant overlapping instances and proof-only public imports from completion; expanded
both docstring proofs; completed the DAG and report records. All existing signatures stay
unchanged. No split-off hole was closed.
