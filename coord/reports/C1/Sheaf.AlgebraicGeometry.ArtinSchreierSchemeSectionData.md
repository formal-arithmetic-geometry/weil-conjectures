## What changed

Proved `AlgebraicGeometry.Scheme.exists_artinSchreier_section_data` without changing
its signature. Reused `AlgebraicGeometry.artinSchreier_construction` for arbitrary
schemes and transported its section identifications through the supplied isomorphism.
Two proved private helpers keep the transport and algebraic construction abstract in
the sheaf, avoiding expensive repeated unfolding of tensor-section definitions.
Constructed the Frobenius-minus-identity map, the constant map through sheafification,
all section formulas, and their zero composite. Added the proof-only import
`Sheaf.AlgebraicGeometry.ArtinSchreierDataConstruction` and updated the DAG route.

## Proved and sorry left

Proved the one original sorry: `AlgebraicGeometry.Scheme.exists_artinSchreier_section_data`.
Also proved private helpers `transport_section_identifications` and
`construct_section_maps`. No sorry remains in the delivery and none was split off.
The imported `AlgebraicGeometry.artinSchreier_construction` is still an open existing
statement, node `lem-sc-as-sequence-construction-helper`; it supplies only the
section-identification part, not the Artin–Schreier maps.
Local compilation succeeds. Characteristic-p additivity treats trivial section rings
separately; the prime-field ring map uses divisibility by ringChar and therefore also
works on the empty scheme. No affineness, curve, or ground-field assumption is added.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.EtaleTensorSections` and
`Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`. Their nodes
`lem-sc-etale-qcoherent-presheaf-functorial` and
`lem-weil-pbc-module-pullback-structure-sheaf` are not direct proof dependencies here;
they remain needed through the reused construction helper, so neither is globally
pruned. The old direct proof dependency `def-sc-etale-qcoherent-module` is also
removed from `proof_deps`; it remains a statement dependency, its public import
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf` remains necessary, and the
construction helper also depends on it. No whole module or node is asserted to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The DAG's single construction step can reuse the existing arbitrary-scheme
`artinSchreier_construction`; no duplicate section-identification statement is needed.
The already proved curve formulas provide the algebraic and sheafification route,
but their curve/field hypotheses prevent directly applying their theorem. This
proof instead pulls characteristic p directly from the given global-section hypothesis.
No statement correction or new node was needed; the unit route is preserved.

## Second reading by C1

1. Compared the sole delivered module and existing node with the repository using
   `diff`. The existing public theorem signature is byte for byte identical;
   no definition or public import changed, and no change record is needed.
   The only additions are two proved private helpers and a proof-only import.
   Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py` (5.7 seconds,
   no warnings). Scanned for sorry and prohibited declarations/attributes: none.
   A scratch copy with `#print axioms` for all three declarations compiles:
   both private helpers use only propext, Classical.choice, Quot.sound; the
   public theorem additionally uses sorryAx from the existing, reported
   `AlgebraicGeometry.artinSchreier_construction`. The inverse-isomorphism
   transport, characteristic-p additivity, naturality, sheafification lift,
   displayed formulas, and zero-composite argument were read individually.
   Verdict: pass as a reduction to that existing open construction theorem,
   not an axiom-free completion of its dependency closure.
3. No statement or sorry is split off, and no new node is added. Both private
   statements are fully proved and strictly cover transport or map construction.
   Checked trivial section rings (in particular the empty scheme), p = 2,
   and arbitrary nonaffine schemes: the subsingleton branch and ringChar
   divisibility avoid an illicit nontriviality hypothesis. No curve, field,
   or affineness assumption is introduced. Verdict: pass.
4. Searched the library independently for section identifications, section data,
   Frobenius subtraction, and constant-presheaf/sheafification constructions,
   including an msearch grep with a different query. Read the existing
   ArtinSchreierDataConstruction and ArtinSchreierDataFormulas modules: the
   first is the needed general-scheme section-identification lemma; the second
   requires an algebraically closed field and a curve, so cannot directly
   replace the map construction here. The two public imports are needed by
   the signature; the added import is proof-only. Checked every old proof
   dependency against the new list and corrected the report omission below.
   The unchanged unit sk-prop-cd has empty realized entries; no prescribed
   realized node or unit step is bypassed. Verdict: pass.
5. Read the node's three proof steps, proof_deps, proof_origin, and lean record.
   They match inverse-isomorphism transport from the construction helper,
   characteristic-p algebra, and the constant-sheaf/sheafification argument.
   The proof-dependency list is exactly the union of the recorded step uses;
   only permitted existing-node fields differ. Verdict: pass.

Second reading changed only this report: completed `## No longer needed` with
`def-sc-etale-qcoherent-module` and added the independent review and axiom results.
No Lean or DAG repair was necessary. Holes closed: the one original
`AlgebraicGeometry.Scheme.exists_artinSchreier_section_data`; holes added: none.
No whole module is globally pruned.
