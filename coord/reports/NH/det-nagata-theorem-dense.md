## Worker report

This delivery records an existing statement, without adding a Lean module:
`AlgebraicGeometry.exists_isDense_compactification` in
`WeilConjectures.Compactification.Dense`, together with
`AlgebraicGeometry.Compactification.quasiCompact_openImmersion` in
`WeilConjectures.Compactification.Defs` (publicly imported by `Dense`).
Both full signatures and docstrings were read. The published source obtained with
`scompile.py --source WeilConjectures.Compactification.Dense` agrees with the local source.
The old attachment named these results but lacked the complete stage-2 binding; this
completes only the item's `lean` record. Every other node field is preserved, including
its inherited status `imported`.

Source: current blueprint `main-20261015`, chapter `sec-nagata-compactification`,
unit `sk-thm-nagata-compactification`, file `det-nagata-theorem-dense.md`.
The source statement was opened and agrees with the node. No statement correction,
new node, dependency repair, or disputed mathematical statement is needed.

Hypothesis and conclusion correspondence:

- Schemes `X` and `S`: the existing theorem's `{X Y : Scheme.{u}}`, with `Y` standing
  for `S`, and its explicit argument `(f : X ⟶ Y)`. The universe `u` is arbitrary.
- Quasi-compact base: `[CompactSpace Y]`.
- Quasi-separated base: `[QuasiSeparatedSpace Y]`.
- Separated morphism: `[IsSeparated f]`.
- Finite-type morphism: `[LocallyOfFiniteType f] [QuasiCompact f]`. Mathlib's
  `Morphisms.FiniteType` module explicitly defines finite type as these two properties;
  this is the same hypothesis, without a finite-presentation or Noetherian assumption.
- Existence of the compactification: `∃ c : Compactification f, c.IsDense`.
  The structure `Compactification f` supplies `c.Z`, `c.i : X ⟶ c.Z`,
  `c.g : c.Z ⟶ Y`, and `c.comm : f = c.i ≫ c.g`.
- The open-immersion clause is `c.isOpenImmersion : IsOpenImmersion c.i`.
- The properness clause is `c.isProper : IsProper c.g`.
- Quasi-compactness of the open immersion follows for every such witness from
  `c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)`.
  Its full signature is `(c : Compactification f) (hf : QuasiCompact f) : QuasiCompact c.i`.
  Thus omitting this redundant conjunct from the existing existential does not weaken
  the node: the additional property follows for the same witness, with no extra hypothesis.
- Scheme-theoretic density: `c.IsDense` is defined as
  `IsSchemeTheoreticallyDominant c.i`, exactly the predicate recorded by the sole
  statement dependency `def-nagata-dense-compactification`. The dependency's current
  `blueprint_update` describes vanishing of the largest quasi-coherent kernel ideal;
  Mathlib's class has the field `ker_eq_bot : c.i.ker = ⊥`.
- Injectivity of `𝒪_{c.Z} → c.i_* 𝒪_X`: once the preceding quasi-compactness is supplied,
  `AlgebraicGeometry.Scheme.Hom.app_injective c.i U` states
  `Function.Injective (c.i.app U)` for every open `U : c.Z.Opens`.
  These are exactly the components of the displayed structure-sheaf map.
  Conversely injectivity makes the kernel ideal zero, so there is no stronger density
  condition hidden in this formulation. Quasi-compactness is essential to using the
  largest quasi-coherent kernel ideal here and has been explicitly accounted for.

Dependency declarations read and used:

- `def-nagata-dense-compactification` records
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant` in
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
  Its class definition and module documentation were read, as was the same module's
  `AlgebraicGeometry.Scheme.Hom.app_injective` with its `[QuasiCompact f]` hypothesis.
- `AlgebraicGeometry.Compactification` and its fields, and
  `AlgebraicGeometry.Compactification.quasiCompact_openImmersion`, were read in
  `WeilConjectures.Compactification.Defs`.
- `AlgebraicGeometry.Compactification.IsDense` was read in
  `WeilConjectures.Compactification.Dense`; it uses the recorded dependency predicate
  directly, without a duplicate notion.

The existing theorem's proof is already present upstream: it uses Nagata's
compactification and its dense refinement. This delivery writes no proof and no
postponed theorem. Existing declarations require no new proof-import module.

Edge cases checked: no nonempty assumption on `X` or `S`; the empty source can be
compactified by the empty scheme, and a morphism to the empty base forces empty source.
For proper `f`, the identity open immersion gives a dense compactification. No reduced,
integral, Noetherian, affine, characteristic, or finite-presentation assumption appears.
Nonreduced schemes are included: density uses the scheme-theoretic kernel, not just
topological density. The explicit quasi-compactness result covers every existential
witness, even though the upstream compactification structure allows non-quasi-compact
open immersions for general morphisms.

Searches made before choosing the existing declaration:

- `msearch.py leanfinder`, query: "A separated finite type morphism of schemes over a
  quasi compact quasi separated base admits a scheme theoretically dense compactification
  with quasi compact open immersion". Eight hits on quasi-compactness, normalization,
  and properness; no dense compactification existence theorem in Mathlib.
- `msearch.py loogle`, query:
  `AlgebraicGeometry.Compactification, AlgebraicGeometry.IsSchemeTheoreticallyDominant`.
  Zero hits; unknown identifier `AlgebraicGeometry.Compactification` (upstream-only).
- `msearch.py leansearch`, query: "A separated finite type morphism to a quasi compact
  quasi separated scheme has a dense compactification". Eight hits on separatedness,
  quasi-separatedness and properness; no matching Mathlib existence theorem.
- `msearch.py grep`, query:
  `exists.*[Cc]ompactification|[Dd]ense.*[Cc]ompactification|[Cc]ompactification.*[Dd]ense`,
  restricted to `AlgebraicGeometry`: zero hits.
- `rg` in upstream `WeilConjectures/` for
  `exists_isDense_compactification|denseCompactification|IsDenseCompactification|det-nagata-theorem-dense`:
  found `Compactification/Dense.lean` and its finite-presentation variant and curve use.
  Read `Dense.lean` and `Defs.lean` in full through the relevant declarations.
- The prescribed `grep -rn "det-nagata-theorem-dense"` in upstream `WeilConjectures/`
  found no exact node-id tag. The name search nevertheless found the exact theorem.
- `rg` in `lean/Sheaf/` for the same pattern found only
  `Compactification/DenseRefinementMorphisms.lean`; inspection shows a theorem about
  morphisms between compactifications, not this existence theorem.
- `rg` in `dag/lean_names_upstream.json` for `nagata|compactification` confirms the
  upstream compactification family is indexed; the item's old attachment already
  names the two declarations now bound with a complete record.

Validation: the scratch-only `ExistingChecks.lean` imports the existing module,
checks the existence theorem, quasi-compactness theorem, density definitions and
sectionwise injectivity theorem, and prints the axioms of all three relevant theorems.
It is compiled only through `scompile.py`; it is not a delivered module.
The scratch check compiled cleanly in both wrapper checks (sandbox and library),
with no warnings. The existence theorem, quasi-compactness theorem and injectivity
lemma each report exactly `[propext, Classical.choice, Quot.sound]` as axioms.

## Second reading by NH

I reread the item node, its blueprint source, the upstream declarations, and the
Stacks source before checking the existing attachment. The Stacks compactification
section (`literature/stacks-project/flat.tex`, section `section-compactify`) defines
compactification by a quasi-compact open immersion into a scheme proper over the
quasi-compact, quasi-separated base; Theorem `theorem-nagata` at lines 9949--9958
gives existence for a separated finite-type morphism. The scheme-theoretic-density
meaning and its injective structure-sheaf characterization are in
`literature/stacks-project/morphisms.tex`, definitions and Lemma
`lemma-characterize-scheme-theoretically-dense`. The blueprint node's three proof
steps (Nagata compactification, quasi-compactness of the open, then dense
refinement) agree with these source places.

Object, hypothesis, and conclusion checklist:

1. The base scheme (S) is the existing theorem's `Y : Scheme.{u}`. Its
   `[CompactSpace Y]` and `[QuasiSeparatedSpace Y]` instances are exactly
   quasi-compactness and quasi-separatedness; no Noetherian, affine, reduced,
   integral, field, characteristic, or universe restriction is added.
2. The morphism (f : X \to S) is the explicit `(f : X ⟶ Y)` with arbitrary
   `X Y : Scheme.{u}`. `[IsSeparated f]` renders separatedness. The source's
   finite-type assumption is exactly `[LocallyOfFiniteType f] [QuasiCompact f]`;
   Mathlib's finite-type convention is locally finite type plus quasi-compact.
3. The compactification (X \xrightarrow{j} \overline X \xrightarrow{p} S)
   is the witness `c : Compactification f`. Its fields `c.Z`, `c.i`, `c.g`, and
   `c.comm : f = c.i ≫ c.g` render the intermediate scheme, the two maps, and the
   required factorization. The structure fields `c.isOpenImmersion` and
   `c.isProper` render the open-immersion and properness clauses.
4. The node's quasi-compactness clause for (j) follows for the same witness from
   `c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)`. This is an
   equality-preserving consequence of the exact existential theorem, not an added
   hypothesis or a weaker witness.
5. The node's density dependency is rendered by `c.IsDense`, which unfolds to
   `IsSchemeTheoreticallyDominant c.i`, exactly the recorded
   `def-nagata-dense-compactification` notion. With the preceding quasi-compactness,
   `AlgebraicGeometry.Scheme.Hom.app_injective c.i U` gives injectivity of every
   section map, hence of the displayed structure-sheaf map
   \(\mathcal O_{\overline X}\to j_*\mathcal O_X\), as required by the node.
   The existing theorem's existential therefore entails every displayed clause in
   the node with the same witness.

The dependency declaration was checked directly: `AlgebraicGeometry.IsScheme-
TheoreticallyDominant` is the Mathlib class recorded for
`def-nagata-dense-compactification`; no private duplicate is introduced. The
compactification structure and `Compactification.quasiCompact_openImmersion` were
read in `WeilConjectures.Compactification.Defs`, and `Compactification.IsDense` in
`WeilConjectures.Compactification.Dense`. Their universes, maps, and typeclass
hypotheses match the node. The imported `Dense` module publicly exposes `Defs`.

Edge cases checked: empty (X) and empty (S) remain allowed (a map to an empty
base forces an empty source); the identity compactification covers proper (f);
zero or nonreduced schemes are admitted; no nonempty-index, positive-integer,
characteristic, or finiteness-of-the-base assumption is present; and the single
scheme universe `u` is arbitrary. The quasi-compactness consequence applies to
every witness, including witnesses whose open immersion was not definitionally
declared quasi-compact.

Independent searches and duplicate checks were repeated with different wording:

- `msearch.py` LeanFinder query “Nagata separated finite type qcqs base dense
  compactification” returned only generic quasi-compactness, normalization, and
  properness declarations; no matching existence theorem.
- `msearch.py` Loogle query
  `AlgebraicGeometry.Compactification, AlgebraicGeometry.IsSchemeTheoreticallyDominant`
  returned no result (the compactification declaration is upstream-only).
- `msearch.py` LeanSearch query “separated finite type morphism dense compactification”
  returned generic separatedness/properness results and no duplicate.
- Grep of Mathlib for `exists.*compactification|dense.*compactification` returned
  no existence theorem; `rg` over upstream `WeilConjectures/`, project `lean/Sheaf/`,
  and `dag/lean_names_upstream.json` found only the recorded
  `Compactification.Dense` family and unrelated refinement files. The exact
  declaration names were opened in the pinned upstream source.

Mismatches found: none. The worker's existing attachment was complete; I made no
Lean or node change and added only this independent reading. The existing theorem,
quasi-compactness consequence, density predicate, and sectionwise injectivity lemma
are sorry-free and use only `[propext, Classical.choice, Quot.sound]`. No new node,
dependency module, statement correction, or citer audit is needed.
