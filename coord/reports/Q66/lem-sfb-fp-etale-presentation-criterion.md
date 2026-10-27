## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFpEtalePresentationCriterion` states the
presentation equivalence in `AlgebraicGeometry.AlgebraicSpace.fp_iff_etale_scheme_presentation`
and the final affine-choice clause in
`AlgebraicGeometry.AlgebraicSpace.exists_affine_fp_etale_presentation`.
Both proofs are exactly `by sorry`; no definition or proof is added.

Hypotheses and clauses, in order:

- The ambient scheme is `{S : Scheme.{u}}`, with the explicit universe `u`.
  `T : Over S` retains its actual scheme and structure morphism; `[IsAffine T.left]`
  is exactly the affine-base hypothesis. `Y : AlgebraicSpace S` is the recorded
  fppf-sheaf algebraic space, and `f : Y.obj.obj ⟶ yoneda.obj T` is its map to T.
  The arbitrary ambient S imposes no finiteness or separation restriction. Taking
  S to be T covers an algebraic space presented directly over the affine base too.
- Condition (1) is the conjunction `MapIsQuasiCompact f`,
  `MapIsQuasiCompact (pullback.diagonal f)`, and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation) Y T f`. These are affine-test
  quasi-compactness, quasi-compactness of the actual relative diagonal, and local
  finite presentation on every representable étale scheme chart of Y.
- `↔` states both directions. The right side quantifies `W : Over S` and the actual
  map `q : yoneda.obj W ⟶ Y.obj.obj`. `IsEtale q` includes representability on
  every scheme test; `IsSurjective q` is representable surjectivity on those tests.
  Thus representability is retained without a redundant separate assumption.
- W's map to T is canonically `yoneda.preimage (q ≫ f)`. The conjunction
  `LocallyOfFinitePresentation ...left ∧ QuasiCompact ...left ∧ QuasiSeparated ...left`
  is scheme finite presentation, including all three required conditions.
- `R : Over S`, `p₁ p₂ : R ⟶ W`, and
  `IsPullback (yoneda.map p₁) (yoneda.map p₂) q q` specify exactly the scheme
  W ×_Y W and both projections. This is the universal-property encoding of the
  relation scheme, not an unrelated scheme or a chosen abstract map. Its map to T
  is the induced `p₁.left ≫ (yoneda.preimage (q ≫ f)).left`; the square gives equality
  with the map via p₂. The final three conjuncts assert its scheme finite presentation.
- The second theorem repeats precisely condition (1) as `hf` and asserts the same
  presentation, now with `IsAffine W.left`. It states the affine choice when (1)
  holds, without requiring every atlas in the first theorem to be affine.

Dependency declarations inspected and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsRepresentable`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`. The definition's
  `IsEtale` tests all pullback schemes and therefore includes representability.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, its affine-local signature.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `IsPullback` gives the equivalent square encoding.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact` and
  `MapToSchemeIsLocally`, with their full definitions and docstrings read.
  The already-landed owning node `def-sfb-proper-curve-moduli` is added to stmt_deps
  as authorized for landed notions. No duplicate definition or new node is needed.
- The scheme-conventions and size-convention nodes are conventions, with no object
  to import: the scheme conjunction is written explicitly and universe u is explicit.
- Proof-only project imports: `SpaceLocalPropertiesChartTest` and
  `AlgebraicSpaceAffineEtaleCover`; both are in the recorded proof dependencies.
  Their signatures and docstrings were read. Other proof-only project dependencies
  currently have no Lean record, mathlib match, or closed upstream audit; they are
  listed in the docstring proof but cannot yet supply imports. Mathlib proof inputs
  concerning qcqs permanence and composition are available through the imported
  scheme finite-presentation and quasi-separated modules. No import cycle is added.

Sources checked: local `spaces-limits.tex` Tag 07SK, first paragraph;
`spaces-properties.tex` Tags 03H6 and 07S4; `spaces-morphisms.tex` Tags 06G5,
073B(1)-(3) and 0410(6)-(8). The newest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md` was read for the inherited context.
The original node statement needs no correction.

Edge cases: empty Y permits the empty scheme atlas, which is affine; no Nonempty
assumption is present. Empty T and empty W are permitted. No Noetherian, separated,
reduced or nonzero-base-ring hypothesis is introduced. Non-quasi-separated atlases
are excluded only by the required finite-presentation conjuncts. In particular the
relation projection is not declared quasi-compact just because it is étale; the
proof uses the finite presentation of R over affine T and qcqs scheme permanence.
The universe is the big scheme site's u throughout; test schemes and presheaf values
use the same u, with no independent smaller universe.

Searches actually run using `msearch.py Q66 lem-sfb-fp-etale-presentation-criterion`:

- leanfinder: "Finite presentation of algebraic spaces detected by etale presentation
  atlas and relation finite presentation"; 8 hits, all ring or scheme results,
  including `Algebra.Etale.finitePresentation` and `LocallyOfFinitePresentation`;
  none states this algebraic-space criterion.
- loogle: `"AlgebraicSpace", "FinitePresentation"`; 0 hits.
- grep: `AlgebraicSpace|algebraic space`; 0 Mathlib hits.
- leansearch: "An algebraic space is finitely presented over an affine scheme if and
  only if it has an etale scheme presentation with finitely presented atlas and relation";
  8 hits, ring algebra presentation and scheme finite-presentation results only.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, presentation/finite
  presentation names, and the two proposed declaration names found no existing
  theorem. Searches of the space modules found the shared `MapIsQuasiCompact`,
  `MapToSchemeIsLocally`, and general chart-local property APIs, which are reused.

Validation: scompile.py compiled the delivered file in sandbox and library modes,
with no errors or warnings. Every variable and universe is explicitly bound;
`set_option autoImplicit false` is also present. The required deliver2.py --no-push dry run passed preflight and compilation
(OK, provisional commit 1beb8e26349); the final delivery uses the same checked sources.
No STATEMENT-DISPUTED or node fault remains.

## Second reading by Q66

Author's separate rereading, not a claim of independent review (the dispatcher brief
reserves independent review for the maintainer and prohibits starting other agents).
Reopened the original node and the completed Lean file. Matched the affine T binder,
the arbitrary algebraic space Y and map f, all three finite-presentation conditions
on f, the two directions of the equivalence, the representable surjective étale map q,
all three scheme finite-presentation conditions for W and R, and the affine-choice
clause in the second theorem. Checked that the square is the actual W ×_Y W square,
with q on both bottom/right edges, and that the R → T map is its first projection
followed by W → T. The unused second route is forced equal by that square. Checked
that the first theorem allows non-affine W and the second adds affineness only in
the asserted choice. No clause mismatch or added mathematical hypothesis was found.
No change was needed after this rereading; independent review remains the maintainer's.
