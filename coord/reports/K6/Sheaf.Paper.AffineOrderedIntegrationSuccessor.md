## What changed

Replaced the proof hole of
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.integrationTranspose_successor`
with a proof by the injectivity of the existing restricted exceptional Hom bijection.
The statement and the definitions it uses are unchanged. The proof first establishes
that inverse-transposing each positive-stage integrationTranspose is the specified
sourceComparison followed by augmentation. At a positive successor it applies
AffineLineEvaluation.composite_transpose to the previous-stage integration transpose,
identifies the exact inverse exceptional compositor using its HEq specification,
and uses the coefficient evaluation contraction. Dimension zero is handled separately
using the literal identity transpose and identityCompositeMap; equality transport of
counits is proved directly by substitution.

Added two smaller statement modules: AffineOrderedEvaluationContraction isolates
the compact-support coefficient calculation, including its first-coordinate unit
case, and AffineLineStandingTranspose isolates the normalization of the single-line
comparison after changing compactification. Both retain their actual maps, source
representatives, and comparison isomorphisms. The main proof imports these privately;
its original public import is preserved. All helper theorems remaining in the item are private
and proved. The proved inverse-transpose and first-line counit calculations are in
new modules AffineOrderedTransposeCounit and AffineOrderedFirstLineCounit. The item node now records this proof route. No existing module besides
the assigned item was changed.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.integrationTranspose_successor`
(node lem-pur-affine-ordered-integration-successor). Its combining proof has no sorry.

Added two holes, each the entire proof of a public named theorem:

- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.orderedEvaluation_contraction`,
  node lem-pur-affine-ordered-evaluation-contraction, in
  Sheaf.Paper.AffineOrderedEvaluationContraction.
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.lineComparison_counit`,
  node lem-pur-affine-line-standing-transpose, in Sheaf.Paper.AffineLineStandingTranspose.

This is a decomposition of one hole into two, not a proof free of new assumptions.
The contraction statement is about compact-support evaluations and contains no
exceptional inverse image or integration transpose. The line statement concerns
one affine-line projection and has no ordered successor or dimension parameter.
Also proved, with no new holes:

- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.integrationTranspose_counit`
  (lem-pur-affine-ordered-transpose-counit).
- `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.lineComposite_counit`
  (lem-pur-affine-ordered-first-line-counit).

The existing composite_transpose theorem is used as stated, including its currently
postponed proof; it is not recreated.

## No longer needed

No public import was removed and no existing module is withdrawn. No complete module
is claimed pruned. The old direct proof dependency
lem-pur-integration-transpose-composition (Sheaf.Paper.IntegrationTransposeComposition)
is not needed: the existing restricted-domain composite_transpose is a closer fit
than its unrestricted ordinary-adjunction interface. The other old geometric
calculation dependencies remain needed by the new coefficient contraction node or
by the existing construction data; their absence from the main proof's direct
imports is not claimed as removal from the target closure.

## Where the brief, the DAG or earlier work was wrong

The old node gave the coefficient contraction and the passage to the specified
standing-site line transpose as one prose step. Their concrete, independently
constructed maps were not related by a directly applicable declaration. The new
nodes state these two identities explicitly, while the actual adjunction-pasting
part is already the existing AffineLineEvaluation.composite_transpose. Its ordinary
antecedent and the retained positive-stage antecedent in exceptionalLine agree in
the recorded comparison coordinates. The zero stage must use its actual identity
normalization, rather than inserting the positive-stage exceptional functor there.
In particular, the standing counit uses rightDerivedLowerShriekComparisonIso,
whereas the chart evaluation uses fixedCompactSupportComparisonIso and its origin
comparison. The new line statement requires their compatibility at the retained
source, not merely existence of a site-comparison isomorphism. This normalization
is an explicit remaining proof obligation and is not claimed to follow by rfl.

The rework row records a previous dependency quarantine. The assigned source is
present, and its theorem, Lean attachment, and construction dependencies are
preserved; no quarantine archive is deleted or treated as unused mathematics.
No source-library declaration or target signature is changed.

## New nodes

lem-pur-affine-ordered-evaluation-contraction records the pre-transpose coefficient
calculation (ordered counit expansion, tensor action and projection composition,
and site transport), with the first-coordinate identity case included. Its module
is lean/Sheaf/Paper/AffineOrderedEvaluationContraction.lean. The zero coefficient ring,
the empty base and dimension zero were checked in the written argument: all displayed
maps retain their unit constraints and equality transports, with no nonvanishing
assumption or cancellation of a trace.

lem-pur-affine-line-standing-transpose records the inverse transpose of the single
standing line comparison. Its module is lean/Sheaf/Paper/AffineLineStandingTranspose.lean.
The proof in words follows the specified Hom chain and the ordinary right-adjoint
uniqueness map. It does not assume that the line comparison is invertible. Its empty
and zero-coefficient cases use the same Hom-chain cancellation.

lem-pur-affine-ordered-transpose-counit is the fully proved inverse-Hom calculation
for integrationTranspose, in lean/Sheaf/Paper/AffineOrderedTransposeCounit.lean.
It uses the unique-HEq specification and the actual restricted Hom bijection.

lem-pur-affine-ordered-first-line-counit is the fully proved equality-transport
calculation for the first coordinate, in
lean/Sheaf/Paper/AffineOrderedFirstLineCounit.lean. Its private transport lemma is
proved by substituting equal morphisms.

No change record is necessary: all existing signatures, public imports, definitions,
instances and attributes are unchanged. The added reducibility attributes are local
to the proof modules. They expose only cached category, coordinate and support
wrappers during tactic matching. The large exceptional Hom equivalence and its
counit stay abstract, with the existing inverse-Hom formula used explicitly. The
zero and positive cases are separate proved private lemmas so that elaboration
uses the ordinary per-declaration heartbeat limit without increasing it.

Timing: after exposing only the local coordinate/support wrappers and replacing
large rewrites by abstract functoriality lemmas, every theorem checked under the
ordinary heartbeat limit. The combined file nevertheless took 70 seconds, including
15.4 seconds of olean serialization. The two self-contained proved counit lemmas
were moved to their own modules; shared definitions were not changed. Profiling
options were removed. The final delivery checks compile the resulting files alone.

Validation: lcompile.py --all accepted all five modules after the refactor, with
no errors and no per-file timing rejection. The compiler's proof-valued-instance
style suggestions were applied before delivery. All five Lean signatures agree
with their DAG attachments, and the assigned public theorem signature is unchanged.
The only two sorry bodies are the two lower evaluation statements listed above.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
