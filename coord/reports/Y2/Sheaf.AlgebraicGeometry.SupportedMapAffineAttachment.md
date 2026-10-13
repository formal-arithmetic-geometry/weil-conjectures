## What changed

Replaced the earlier rejected restatement with a reduction through a perfect supported
source on the open subscheme Y = W ⊔ V. The new module
`Sheaf.AlgebraicGeometry.SupportedMapAffineUnionGluing` stops before ambient extension.
The original theorem chooses derived localizations on Y using the existing
`open_derived_localization_adjunction`, constructs the iterated restriction comparison
explicitly, applies the new union construction, then applies the existing
`exists_supported_map_initial_ambient_lift`. It composes the resulting isomorphisms and
proves the final map equation by naturality in the fully proved private helper
`restrict_map_comparison`. No existing signature or public import changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_supported_map_affine_attachment`.
There is no sorry in the item's module. Added one hole:
`AlgebraicGeometry.Scheme.exists_supported_map_affine_union_gluing`, node
`lem-sc-supported-map-affine-union-gluing`, in its own new module. This is a decomposition:
one hole closed and one added, with zero net holes removed. The ambient extension,
restriction comparison, and combining map equation are complete Lean proofs from the
named intermediate and existing statements. The existing ambient-lift theorem still
has its own previously recorded sorry, which this delivery does not modify.

## No longer needed

Removed the item's direct proof imports of `AffinePerfectMapLift`,
`AffinePerfectSupportExtension`, `DerivedOpenGluing`, `DerivedOpenLocalization`, and
`DerivedOpenRestrictionQCoh`. The affine and gluing dependencies belong to the new
union-construction node and remain imported by its module; the localization theory
remains reachable through `OpenDerivedLocalizationAdjunction`. The old direct proof dependencies no longer used by the attachment proof are
`def-pc-perfect-complex`, `lem-pc-derived-open-restriction-qcoh-iff`,
`lem-pc-derived-open-localization-universe`, `lem-sc-affine-perfect-support-extension`,
`lem-sc-affine-perfect-map-lift`, and `lem-sc-derived-open-gluing`.
PerfectComplex stays a public statement import. The affine, gluing and quasi-coherence
nodes remain dependencies of the new union node, and localization-universe remains
reachable through the localization adjunction. Thus no existing node or module is
globally pruned. The rejected sandbox-only
`supported_map_affine_attachment_core` and its candidate local existence theorem were
removed; neither is part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier core theorem repeated the requested statement and was correctly rejected.
The weaker local-existence candidate lost the comparison data and could not support
assembly of the conclusion; it was discarded. The replacement is an actual step of
Tag 09IM's proof: it constructs F and alpha on Y, with global perfectness and support
there, and supplies no source on X. The existing ambient-lift theorem supplies that
missing step in the item's proof. The source's two-open route and the unit remain intact.
Empty U, empty W or V, V contained in W, empty support, and a zero source all retain
valid restriction and gluing constructions. No compactness of X or global perfectness
of the input R was added. An arbitrary supplied natural comparison c is allowed:
naturality transports the stabilization identification and its map equation together.

## New nodes

`lem-sc-supported-map-affine-union-gluing` isolates the source and compatible map on
W ⊔ V, excluding extension to X. Its theorem has a complete proof in words and a
verbatim Lean statement in the node. Searches found no Mathlib statement of this
construction; LeanSearch was unavailable, and LeanFinder, Loogle and grep found only
generic fraction and restriction infrastructure. The blueprint search for supported
perfect statements found no matching imported blueprint node. No change record or
forced adaptation is needed.


## Second reading by Y2

1. **Interfaces: pass.** Read the full diff of SupportedMapAffineAttachment against
   the repository. Its sole existing theorem's raw signature is byte for byte
   identical, including the independent derived-category instances and every
   local-model, stalk, stabilization and map clause. The only additions are a
   private proved categorical helper and proof imports. Both public imports remain
   identical. No definitions, other modules, target statements or change records
   were altered. The new union theorem has its own module.

2. **Lean and axioms: pass with the reported open dependencies.** Both delivered
   modules compiled through lcompile.py in import order (18.8 and 32.8 seconds).
   The attachment has no sorry; the union module has exactly its named public
   theorem's `by sorry`. No forbidden declaration or hollow definition occurs.
   A scratch copy printing axioms gives only propext, Classical.choice and
   Quot.sound for restrict_map_comparison; the attachment and union additionally
   use sorryAx from the recorded open statements. The final map calculation uses
   naturality in the correct direction and the ambient lift's exact map equation.
   Localization choices come from the already proved localization theorem; the
   proof introduces no definition choosing an arbitrary existential witness.

3. **Split statement: pass after clarifying its comparison argument.** Read Stacks
   Tags 09IM, 08EK, 08EH and 08DG and the complete interfaces of
   exists_perfect_supported_extension, exists_perfect_map_lift_of_isAffine,
   derived_open_gluing, schemeDerivedQCoh_openRestriction_iff and the ambient lift.
   On the affine V, W intersect V is compact by quasi-separatedness and compactness
   of W and V; V minus T is compact by the same fact applied to the compact open
   complement Tᶜ. These supply precisely the affine lemmas' hypotheses. The map
   lift explicitly preserves the closed support, and gluing includes the compatible
   morphism, rather than just an object. Local finite-free retract models and stalks
   restrict and transport through the open equivalences. Empty U, W, V and T, zero
   R, and V contained in W give zero or redundant restrictions, with no excluded
   case. The new hole supplies F and alpha only on Y; ambient extension and the
   final comparison remain separate completed Lean steps, so this is a strictly
   smaller construction rather than the rejected ambient restatement.
   Independent LeanFinder searches for gluing derived objects and maps found only
   ordinary scheme/sheaf gluing. Loogle found Functor.mapBiprod and its projection
   infrastructure, not the supported construction. Mathlib grep for perfect gluing
   and supported complexes found only cochain-support infrastructure. Searches in
   both library roots and the upstream WeilConjectures tree found no replacement
   for the union theorem. Its hole is substantial and cannot be closed in a few
   minutes from these categorical comparisons alone.

4. **Route and pruning: pass.** The proof first uses the proved localization
   adjunction, explicitly builds the iterated restriction comparison, then uses
   the union statement and existing ambient lift. The private helper completes
   their composition. The two-open affine extension / map lift / gluing route of
   09IM is retained. All six old direct dependencies removed from proof_deps are
   now explicitly listed under No longer needed; none is globally pruned. The
   unit sk-thm-picard-duality.json is unchanged (its existing realized statement
   and step arrays are empty); this delivery neither replaces a unit step nor
   claims to repair that pre-existing realization record. Public imports serve
   the signatures; added and retained proof-dependency imports are plain imports.

5. **Nodes: pass.** The existing node changes only proof, proof_deps and
   proof_origin. Its four steps correspond respectively to localizations and
   explicit comparison, union construction, ambient lift, and categorical
   naturality. The new node has source, creation, blueprint ancestry, searches,
   matching chapter/unit and a verbatim Lean signature. Its proof_deps are the
   union of the cited step dependencies. Its local construction uses exactly the
   support extension, support-preserving map lift and compatible-map gluing
   interfaces read above. No additional node duplicates an existing statement.

Changes made by the second reader: expanded the new theorem's docstring and its
node's last proof step to handle arbitrary c explicitly. For the canonical
comparison k and its identification e0, form t = k.symm followed by c, a natural
automorphism of direct restriction J. Postcompose e0 by the biproduct of t_R and
its shift; its first projection acquires t_R, and naturality at beta gives the
map identity with c. This requires no shift compatibility for c. Also completed
the explicit removed-node list in No longer needed. No Lean proof or signature
needed repair, and no additional hole was closed or introduced.
