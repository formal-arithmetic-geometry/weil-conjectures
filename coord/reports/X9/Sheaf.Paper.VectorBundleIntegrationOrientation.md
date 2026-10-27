## What changed

Replaced the hole in `WeilConjectures.PurityFiniteSetting.vectorBundleIntegration_orientation_inv`
by the affine-frame descent argument, keeping its statement unchanged. The proof constructs the
shifted finite Tate sheaf normal form, transfers concentration to the target using the supplied
orientation, chooses actual finite affine bundle frames, evaluates the given normalization in
those frames, cancels the invertible locality comparisons, and proves global equality using
injectivity of cohomology on the concentrated Hom set and joint faithfulness of sheaf pullback.
A proof-only `import all Sheaf.Paper.DiagonalOrdinaryOrientationRigidity` reuses its already
proved private concentration and equality-test helpers. No helper is duplicated or changed,
and no arbitrary-derived restriction faithfulness is asserted.

Added the proof import `Sheaf.Paper.VectorIntegrationOrdinaryFrameCounit`. Its theorem isolates
the remaining calculation on one affine linear frame: the actual ordinary integration adjunct
has the ordered affine-counit formula with the specified source-etale locality. It has no
orientation input and no global equality/descent conclusion. The main module supplies all
chart geometry and combines this local equation with the given normalization in real Lean.
All other added imports are private proof imports; the existing public import is unchanged.
The parent DAG proof and proof dependencies now follow this argument.

The statement of the new frame lemma was checked at rank zero and on an empty frame: the
ordered adjunction is the identity in rank zero, and arrows on the empty site are unique.
The proof uses the actual positive diagonal exponent, so arbitrary finite coefficient
extensions remain in scope. No definition, existing theorem signature, or consumer changed. Local irreducibility
attributes prevent large functor implementations from unfolding during proof elaboration;
they do not change shared attributes or importer behavior.

Validation: `lcompile.py --all` compiled both modules, at 39.5 seconds for the new frame
statement and 53.1 seconds for the item, both below the 60-second limit. The only warnings
were for temporary profiling options, which are removed from the delivered source. The
finite frame index is lifted to the scheme universe before applying the equality helper.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.PurityFiniteSetting.vectorBundleIntegration_orientation_inv`
(node `lem-pur-vector-bundle-integration-orientation`). Its assembly proof is complete.

Added one hole, the whole proof of
`WeilConjectures.PurityFiniteSetting.vectorIntegration_ordinary_frame_counit`
(node `lem-pur-vector-integration-ordinary-frame-counit`), in the new module
`Sheaf.Paper.VectorIntegrationOrdinaryFrameCounit`.

Thus this delivery is a decomposition: one upper hole closed, one strictly local hole added,
net zero holes. There are zero holes in the item module and one in the delivered files.
No claim is made that the integration frame calculation itself has been proved.

## No longer needed

No original Lean import was removed: the item originally imported only its statement data.
The following planned direct dependencies are removed from the parent's proof route:

- `lem-pur-affine-ordered-integration-transposes` /
  `Sheaf.Paper.AffineOrderedIntegrationTransposes`: its ordered pro-etale purity recursion is
  unnecessary for an equality stated entirely in the ordinary-etale category.
- `lem-pur-vector-integration-chart-comparison` /
  `Sheaf.Paper.VectorIntegrationChartComparison`: its comparison-image equation, in the
  older coefficient coordinates, is replaced by the ordinary frame-counit equation.
- `lem-pur-degree-zero-derived-map-gluing` /
  `Sheaf.Paper.DegreeZeroDerivedMapGluing`: the full existence/unique-gluing assertion is
  unnecessary. A private proved equality test uses only cohomology injectivity and the
  already proved jointly-surjective sheaf conservativity theorem.

The affine-space top-trace dependency is needed by the new local lemma, rather than directly
by the assembly proof. Finite Tate line flatness and Tate products are needed transitively
through the reused rigidity helpers; finite affine frames remain a direct dependency.
Their supporting facts are reused through the existing rigidity module rather than
through duplicate local proofs. These are route changes only; no module is withdrawn, and no assertion is
made that other consumers of the listed modules disappear from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The planned integration chart comparison is not immediately an ordinary-etale locality
formula: its declared result is after site comparison, uses a different displayed coefficient
presentation, and has exceptional base-change coordinates on the frame base. The item needs
an ordinary formula using source-etale locality and the affine tower over the ambient base.
The new node states precisely this local comparison, with its source proof and all maps
specified. The original statement and the unit's vector-bundle route are preserved.

No statement was disputed. No source-library declaration or public import changed.

## New nodes

`lem-pur-vector-integration-ordinary-frame-counit` is the one-frame ordinary integration
calculation from the second paragraph of `thm-amb-vector-bundle-purity.proof.md` and
orientation-charts Step 4. It is realized by
`WeilConjectures.PurityFiniteSetting.vectorIntegration_ordinary_frame_counit`
in `Sheaf.Paper.VectorIntegrationOrdinaryFrameCounit`. Its proof plan first evaluates the
actual trace normalization, then transposes and pastes exceptional mates, and finally uses
affine trace base change and Tate pullback coherence. It contains none of the global descent
argument now proved in the item. No change record is required: there is no existing interface
change and no adapted consumer.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
