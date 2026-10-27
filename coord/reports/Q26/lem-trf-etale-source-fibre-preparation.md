## Worker report

Item: lem-trf-etale-source-fibre-preparation. Group Q26, stage 2, 2026-10-23.
The module lean/Sheaf/AlgebraicGeometry/EtaleSourceFibrePreparation.lean states the
accepted node in three named theorems, each with sorry and a source/proof docstring.
No definition, auxiliary axiom, new node, dependency replacement or statement
correction is needed. No mathematical assertion is proved.

The inherited BLOCKED ending concerned Q151's stage-1 split, not a Lean statement.
The current node has no lean or reviewed_lean record; coord/queue.tsv lists stage 2.
The maintenance handoff in coord/brief-stage2.md §0 explicitly authorizes stating
this reviewed split in stage 2. I preserved every original node field, adding lean only.
The required CompactObject example is now withdrawn; its node points to the
upstream module. I used the required current module/public-import/expose header.

Hypothesis and clause correspondence:

- Schemes and the morphism f:X→S: `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The arbitrary family indexed by a set: `{I : Type v}`, `U : I → Scheme.{u}`,
  `h : ∀ i : I, U i ⟶ X`. The independent index universe is unrestricted.
- Every source map étale: `[∀ i : I, Etale (h i)]`. Images cover X:
  `hjoint : ∀ x : X, ∃ (i : I) (y : U i), h i y = x`.
- The flatness equivalence is the first conjunct of etale_source_fibre_preparation:
  `Flat f ↔ ∀ i : I, Flat (h i ≫ f)`.
- The local-finite-presentation equivalence is its second conjunct:
  `LocallyOfFinitePresentation f ↔ ∀ i : I, LocallyOfFinitePresentation (h i ≫ f)`.
  These two clauses have no finite-presentation or flatness hypothesis on f.
- The remaining assertions assume either equivalent presentation condition. The
  third conjunct uses `LocallyOfFinitePresentation f → ...`; the second conjunct
  supplies exactly the same assertion starting from presentations of all composites.
- Every algebraically closed field and geometric point are quantified by
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ S)`.
  All schemes and coefficient rings are in the same arbitrary universe u, the
  standard Mathlib convention for schemes and their spectra. No characteristic,
  nonempty index set, finite extension or fixed closure is imposed.
- C and D_i are literally `pullback f g` and `pullback (h i ≫ f) g`.
  For each i the theorem asserts a unique isomorphism to
  `pullback (h i) (pullback.fst f g)`, with its projections to U_i and Spec Ω
  equal to the two original projections. Thus these are canonical isomorphisms,
  characterized as in the node, rather than an arbitrary Nonempty isomorphism.
- The actual canonical comparison is `(pullbackRightPullbackFstIso f g (h i)).inv`.
  Its composite with the second projection to C is precisely e_i. The theorem
  asserts `Etale` of these composites and explicitly states their joint
  surjectivity on points. Compatibility with the C projection follows from the
  projection characterization and pullback uniqueness, without any choice of a map.
- The remaining fibre conjuncts give `LocallyOfFiniteType (pullback.snd f g)` and
  `IsLocallyNoetherian (pullback f g)`, and the identical two predicates for every D_i.
- Every finite-presentation affine chart is covered by
  geometric_fibre_finite_presentation_affine_chart. The rings R,A have CommRing
  structures and Algebra R A, Algebra R Ω. The open embeddings a:Spec A→X and
  b:Spec R→S are the affine charts; `Algebra.FinitePresentation R A` is exactly
  the finite-presentation chart condition. The equations ha and hg specify the
  restriction of f and the factorization of g through b, respectively.
- That theorem identifies the pullback of each such chart,
  `pullback (a ≫ f) g`, with `Spec (.of (Ω ⊗[R] A))`. Its two displayed equations
  specify the projections using includeRight and algebraMap, so the tensor formula
  respects the chart and Ω-structure. It also asserts
  `Algebra.FinitePresentation Ω (Ω ⊗[R] A)`.
- geometric_fibre_finite_presentation_affine_charts_cover quantifies every point
  x of C and supplies R,A, their algebra structures, open embeddings a,b, the
  finite presentation and factorization equations, and a point y of the chart's
  pullback mapping to x under the canonical comparison and second projection.
  This is exactly coverage by the specified charts; base change of an open
  immersion is open by Mathlib's imported instance. Apply these last two theorems
  with `X := U i` and `f := h i ≫ f` for the stated identical claims for every U_i
  and D_i. Their finite-presentation hypotheses come from the main equivalence.
- No quasi-compactness, separation or Noetherian assumptions on X,S,U_i occur.
  There are no Nonempty or finite-index hypotheses and no nonzero chart hypothesis.

Recorded dependency declarations used (the source docstrings and signatures were read):

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme,
  Scheme.Hom, and the category morphism notation.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  AlgebraicGeometry.Etale; its affine-local class and the recorded equivalence
  identify exactly the node's flat/lfp/unramified condition.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  AlgebraicGeometry.Flat, with Flat.iff_flat_stalkMap giving the stalk interpretation.
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  AlgebraicGeometry.LocallyOfFinitePresentation and its finitePresentation_appLE field.
- def-weil-field: Mathlib.Algebra.Field.Defs, Field.
- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, IsAlgClosed
  (exposed by the recorded AlgebraicClosure module). The node asks for an
  algebraically closed field here, not an algebraic extension of a chosen field.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Spec
  and Spec.map, with CommRingCat.of / CommRingCat.ofHom.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  CategoryTheory.Limits.pullback, pullback.fst and pullback.snd. The existing
  pullbackRightPullbackFstIso in Shapes.Pullback.Pasting supplies the canonical
  comparison; no private copy of a fibre or base-change construction was made.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType. The node asserts locally finite type only.
- pqf-def-locnoeth: Mathlib.AlgebraicGeometry.Noetherian,
  AlgebraicGeometry.IsLocallyNoetherian.
- def-weil-pbc-finitely-presented-algebra: Mathlib.RingTheory.FinitePresentation,
  Algebra.FinitePresentation. Tensor product and canonical inclusions are Mathlib's
  Algebra.TensorProduct API; pullbackSpecIso was read to check factor ordering.

The two landed non-Mathlib proof dependencies are imported privately:
Sheaf.RingTheory.FlatnessFaithfullyFlatExtension,
Module.Flat.iff_flat_tensorProduct_of_faithfullyFlat_extension; and
Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource,
AlgebraicGeometry.locallyOfFinitePresentation_iff_of_fppf_source_family. The remaining
proof ingredients are Mathlib declarations, including faithful flatness for flat
local homomorphisms, base-change of étale coverings, pullbackSpecIso, finite-presentation
base change, affine opens, and LocallyOfFiniteType.isLocallyNoetherian. Their modules
are imported directly or exposed by the public statement imports. The docstrings
reproduce the six accepted proof steps and identify the relevant DAG inputs.

Edge cases checked mathematically: I empty forces X empty by hjoint, making the
reverse flat/lfp conditions vacuous; empty individual U_i are allowed. Empty fibres
have no points in either joint-surjectivity or chart-coverage clauses. A zero chart
ring A is permitted, and Ω⊗_R A is zero, so its spectrum is the empty chart. No
Nontrivial A was introduced. A chart outside the chosen fibre gives the same empty
spectrum. The identity cover, redundant infinite covers, and non-quasi-compact
sources have the same formulas. The Ω projection uses algebraMap Ω, while the A
projection uses includeRight: the tensor factors are Ω first, A second as required.

Searches for reuse (2026-10-23):

- msearch.py leanfinder: “Flatness and local finite presentation descend through an
  etale source covering and geometric fibres have finitely presented tensor product
  affine charts”. Eight hits included LocallyOfFinitePresentation, Etale, and
  UniversallyOpen.of_flat; none states the assembled result or its chart clauses.
- msearch.py loogle: `AlgebraicGeometry.LocallyOfFinitePresentation,
  AlgebraicGeometry.Flat`. Twelve hits; target descent, flat/open facts and ringed
  functors, with no exact source-family theorem with the requested fibre preparation.
- msearch.py grep: `etale.*source|[Ff]ibre.*[Cc]hart|[Ff]iber.*[Cc]hart` in
  AlgebraicGeometry: zero hits.
- msearch.py leansearch: “Etale source covers descend flatness and local finite
  presentation and geometric fibres have finite presentation affine charts”. Eight
  hits for individual notions and locality APIs, no exact theorem.
- rg in lean/WeilConjectures and lean/Sheaf for source/fibre preparation and affine
  fibre chart combinations: unrelated individual fibre results, no equivalent
  declaration. rg for the blueprint id in WeilConjectures: no hit. Name search for
  all three delivered names in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no hit. Pullback API search found the canonical
  pullbackRightPullbackFstIso, which is reused rather than redefined.

Sources read locally: curves.tex lemma-nodal-family-etale-local-source (0C5D),
descent.tex lemma-flat-fpqc-local-source (036K) and
lemma-locally-finite-presentation-fppf-local-source (036N), algebra.tex
lemma-base-change-finiteness (05G5), and morphisms.tex lemma-finite-type-noetherian
(01T6). The latest blueprint's locality proof uses contracting correspondences;
this node is the retained generic scheme-theoretic tool identified in its accepted
split, and this delivery changes no blueprint route or target.

Validation: scompile.py compiled both the sandbox module and its actual library
module cleanly (1.7 seconds each), with no errors or non-sorry warnings. The first
probe exposed a type/coercion ambiguity in point binders for generic pullbacks;
explicit `(pullback ... : Scheme.{u})` annotations fixed it without changing the
mathematical statement. No local or global build was run. No node faults or
STATEMENT-DISPUTED concerns were found.

## Second reading by Q26

No second reading by a worker: the current brief requires direct worker delivery
and the maintainer's independent review is the only independent review. No other
agent was started. I re-read all three signatures against the node's hypotheses
and clauses as recorded above; all chart and fibre clauses are present.
