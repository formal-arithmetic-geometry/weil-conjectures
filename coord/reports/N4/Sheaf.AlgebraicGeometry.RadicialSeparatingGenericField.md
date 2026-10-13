## What changed

The original module's sole hole, `AlgebraicGeometry.exists_radicial_separating_generic_field`, now has a complete compiling Lean reduction. It obtains the finitely generated generic field and its dominant map, applies the existing `FieldExtension.exists_finitePurelyInseparable_separablyGenerated`, spreads the finite base extension, and applies the reduced generic-fibre embedding theorem. Quasi-compactness follows from affine source and target by instance synthesis. The existing declaration's signature and visibility are unchanged.

Three new modules isolate precisely the scheme steps absent from the stated field dependency: `Sheaf.AlgebraicGeometry.GenericFibreDominantField`, `Sheaf.AlgebraicGeometry.PurelyInseparableGenericBaseSpread`, and `Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbedding`. Each contains one public named theorem with a source and full proof in words; each becomes an independent item. The sandbox copy of `lem-sbc-radicial-separating-generic-field` updates its proof, proof dependencies and proof origin to match the Lean proof. No definitions or existing interfaces were changed, and no other group's modules were adapted.

All four files compile together without warnings using `lcompile.py --all`. The delivery dry run and declaration axiom probes pass except for the second reading, which the designated second reader writes. Nothing is pushed.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_radicial_separating_generic_field` (node `lem-sbc-radicial-separating-generic-field`). No `sorry` remains in the item module.

Added holes:

- `AlgebraicGeometry.exists_generic_fibre_dominant_field`, node `lem-sbc-generic-fibre-dominant-field`, in `GenericFibreDominantField.lean`.
- `AlgebraicGeometry.exists_purely_inseparable_generic_base_spread`, node `lem-sbc-purely-inseparable-generic-base-spread`, in `PurelyInseparableGenericBaseSpread.lean`.
- `AlgebraicGeometry.exists_reduced_generic_fibre_field_embedding`, node `lem-sbc-reduced-generic-fibre-field-embedding`, in `ReducedGenericFibreFieldEmbedding.lean`.

This is a decomposition: one original hole closed and three smaller holes added, a local net of minus two. The field-square theorem is an existing dependency, not a new hole of this delivery. No `sorry` occurs in a definition, private declaration, or partial proof.

## No longer needed

No original imports, dependency nodes, or modules were removed: `Sheaf.FieldTheory.MakeSeparablyGenerated` remains used directly. The old prose plan's replacement of the upper field by a compositum, and the associated separably-generated subextension argument, are unnecessary here: the existing upper field E is already separably generated over the new base field and the reduced tensor injects into E. There are no separate modules or node IDs for these discarded steps in the item's original dependency list. The new modules import only the APIs their signatures need.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left an `aesop` placeholder and abandoned without implementing the affine plan. The plan admits a strict decomposition: the first lemma constructs only the original generic function field, the second concerns only the base and a supplied field extension, and the third assumes all those objects and performs only the reduction/embedding and scalar transport. None repeats the original existential theorem under another name.

The reduced-fibre embedding needs a generic lifted point in an integral new base. These hypotheses are explicit: the spreading lemma supplies genericity, and the combination passes it to the embedding lemma. Passage to the residue field is then localization, so reduction commutes with the generic pullback. The original theorem itself need not assert genericity of its witness.

Edge cases checked mathematically against the statements: geometric irreducibility excludes the empty/zero generic fibre; identity field extensions and characteristic zero work in the spreading step; the embedding lemma allows nonreduced total pullbacks and arbitrary original source fibres admitting the supplied dominant field map. Finite purely inseparability makes the tensor of the two fields Artinian with one prime; its reduction injects into E by the compatible field maps. No arbitrary witness is used to define data. Stacks Tags 0559 (second proof), 030R and 04KM were read. LeanSearch requests were unavailable and recorded as such; LeanFinder and grep searches are recorded in the node metadata and sandbox search log.

## New nodes

`lem-sbc-generic-fibre-dominant-field`: the localization of a reduced affine source at the generic base point is a nonzero domain; its actual fraction field is finitely generated, with a compatible dominant spectrum map. Module `Sheaf.AlgebraicGeometry.GenericFibreDominantField`.

`lem-sbc-purely-inseparable-generic-base-spread`: clears denominators of finitely many purely inseparable field generators, constructs their integral affine subalgebra, and identifies the residue field of its generic point with the specified field extension. Module `Sheaf.AlgebraicGeometry.PurelyInseparableGenericBaseSpread`.

`lem-sbc-reduced-generic-fibre-field-embedding`: given the original dominant field map, a finite purely inseparable base extension, a compatible residue field equivalence and an upper field square, uses injectivity after tensoring and reduction to give the required dominant map; transports separable generation along the field equivalence. Module `Sheaf.AlgebraicGeometry.ReducedGenericFibreFieldEmbedding`.

Each node preserves chapter `sec-smooth-base-change`, unit `sk-prop-normal-form`, and blueprint ancestor `sbc-lem-slicing`. The unit's `realized` route is untouched. There are no change records or forced adaptations.

## Second reading by N4

1. Compared the delivered item against the repository with `diff -u`, and read all
   four delivered modules. The only changes to the existing module are three plain
   proof imports and its proof body. Restored the original single space before `:=`
   so its existing signature is byte-for-byte unchanged. Its original docstring,
   public visibility, hypotheses and every existential/conjunct remain unchanged.
   There are no definitions, interface changes, change records or forced adaptations.
   Verdict: pass.

2. Compiled all four modules locally in import order with `lcompile.py --all`:
   no errors or warnings. The only three `sorry` tokens are the complete proofs of
   the three named new public theorems listed above. No axiom, unsafe, opaque,
   implemented_by, extern, hollow definition or arbitrary data definition occurs.
   The explicit declaration axiom probe and delivery probe check the allowed
   standard axioms plus `sorryAx` from still-open dependencies. The item is a
   reduction resting on open helpers, not an axiom-free completed target.
   Verdict: pass as a decomposition, one hole closed and three added.

3. Matched each new theorem to its node and complete docstring proof. Checked
   the actual second proof of [Stacks Tag 0559](https://stacks.math.columbia.edu/tag/0559),
   [Tag 030R](https://stacks.math.columbia.edu/tag/030R) and
   [Tag 04KM](https://stacks.math.columbia.edu/tag/04KM).
   For the first helper, a reduced generic localization is a domain because
   geometric irreducibility supplies both irreducibility and nonemptiness;
   finite presentation supplies finite field generation. For the second, scaled
   purely inseparable generators are integral over the original coordinate ring,
   with the specified fraction field and compatible residue embedding. For the
   third, the finite purely inseparable tensor is local Artinian; its map into E
   kills exactly its unique prime. Injection on reductions followed by spectrum
   gives scheme-theoretic dominance. Genericity and integrality of S-prime make
   the passage to its residue field a localization, so reduction commutes here.
   Checked identity extensions, characteristic zero, a zero-dimensional original
   fibre, and a nonreduced tensor such as k(u) tensor_k k(u) with u^p in k.
   Empty original fibres cannot satisfy the first helper's hypothesis.
   Each helper addresses only one stage: original function field, base spreading,
   or embedding of supplied data; none restates the item. Independent searches
   used LeanFinder for dominant function-field maps, Loogle for
   `IsPurelyInseparable, TensorProduct`, and grep for function-field dominance,
   purely inseparable spectrum maps, and residue fraction rings, plus `rg` in
   both Lean roots. Results include `Scheme.PartialMap.fromFunctionField`,
   `functionField_isFractionRing_of_isAffineOpen`, and
   `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`: useful component
   APIs, not duplicate statements or a direct shorter solution. No helper can
   be closed in a few minutes solely by applying these APIs. Verdict: pass.

4. Read the existing field-square theorem and checked its witness order against
   the reduction. It supplies E separably generated over k-prime, so the direct
   injection into E avoids the old compositum/separable-subextension detour.
   The proof uses each of its four dependency nodes; the sole original dependency,
   `lem-weil-pbc-make-separably-generated`, remains directly used. Thus the
   no-longer-needed list has no omitted old node. All newly added proof imports
   are plain imports. The helpers' public imports support their signatures.
   Read `dag/units/sk-prop-normal-form.json`: its `realized` route is untouched,
   and this change concerns only affine steps below that route. Verdict: pass.

5. Compared the original and delivered item JSON: only `proof`, `proof_deps`
   and `proof_origin` change. Their four steps match the four actual applications
   and witness assembly. Checked the three new nodes' required fields, verbatim
   Lean signatures, source, mathematical statements, proof text, empty union of
   named proof dependencies, searches, creation data, chapter, unit and blueprint
   ancestry. Each node matches its respective Lean statement. Verdict: pass.

Second reading changed only the item's signature whitespace back to the exact
original formatting, clarified in the new embedding helper's docstring why its
explicit generic-point hypothesis permits localization, and added this review.
No statement, proof route, hole count or import changed.
