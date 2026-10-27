## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGenericRankLocus` states
`AlgebraicGeometry.Scheme.Modules.exists_smooth_generic_rank_locus`, with one
`sorry` and no definitions. The source is Stacks More on Flatness, Tag 05UC,
`lemma-free-at-generic-points-representable`, together with
`situation-free-at-generic-points` and `equation-free-at-generic-points` in
`literature/stacks-project/flat.tex`. I read the source situation, lemma and
proof, and the current blueprint's CTF-stability proof. The node is exactly
the affine, finitely presented case; no statement correction is needed.

Hypotheses and clauses, in order:

- Schemes S and X: `{X S : Scheme.{u}}`. Affineness of each is
  `[IsAffine X] [IsAffine S]`; no Noetherian assumption is introduced.
- The specified morphism is `(g : X ⟶ S)` and smoothness is `[Smooth g]`.
- Geometrically irreducible nonempty fibres are `[GeometricallyIrreducible g]`.
  Mathlib uses `IrreducibleSpace`, which includes nonemptiness, and supplies
  this instance on every `g.fiber s`. Thus a separate nonemptiness hypothesis
  would be redundant. The source's unique generic point exists by sobriety
  and irreducibility; the predicate quantifies over every generic point, so
  it does not introduce a chosen generic point or an extra assumption.
- The module is `(E : X.Modules)`, with `[E.IsQuasicoherent]` and
  `[E.IsFinitePresentation]`, using the recorded sheaf-module definitions.
- Every nonnegative integer rank, including zero, is `(r : ℕ)`.
- The representing scheme and its map are `∃ (Sᵣ : Scheme.{u}) (i : Sᵣ ⟶ S)`.
- A locally closed immersion is `IsImmersion i`. The Mathlib module's
  `isImmersion_iff_exists` identifies this with a closed immersion followed
  by an open immersion, exactly as the node specifies.
- Finite presentation is written out as `LocallyOfFinitePresentation i ∧
  QuasiCompact i ∧ QuasiSeparated i`, including all three clauses of the node.
- All test schemes over S are `∀ (T : Scheme.{u}) (h : T ⟶ S)`, with no
  affineness, reducedness or finite-type condition on T.
- X_T is the canonical `Limits.pullback g h`, and the tensor-pulled module is
  `(tensorPullback (pullback.fst g h)).obj E`. This is the dependency's actual
  tensor construction, rather than Mathlib's differently implemented module
  pullback. Its structure map to T is `pullback.snd g h`.
- For each `t : T`, a fibre point has type `(pullback.snd g h).fiber t`.
  `IsGenericPoint ξ Set.univ` means its closure is the entire fibre.
- The open neighbourhood is `W : (Limits.pullback g h).Opens` and contains
  the image `(pullback.snd g h).fiberι t ξ`. It is an open in the ambient
  X_T; freeness merely on the fibre would give a different statement.
- Freeness is `Nonempty (E_T.over W ≅ SheafOfModules.free
  (ULift.{u} (Fin r)))`. The free sheaf is the coproduct of r copies of the
  restricted ring sheaf; ULift only places this finite index in the sheaf's
  existing coefficient universe. The restriction is the established
  `SheafOfModules.over` construction, as in the recorded presentation node.
- Singleton-or-empty values and representability are stated by the iff
  between the preceding predicate and `∃! k : T ⟶ Sᵣ, k ≫ i = h`.
  Thus Hom over S has exactly one element precisely when H_r(T) does,
  and is empty otherwise. Precomposition of the unique factorization gives
  the restriction maps and naturality. No extra arbitrary functor or action
  is supplied. This is the full functor-of-points universal property.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, and `Spec.map`; `IsAffine` is the existing affine
  scheme predicate. No alternative spectrum or category of schemes occurs.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`, importing
  `Geometrically.Irreducible`: `GeometricallyIrreducible` and its
  `IrreducibleSpace (g.fiber s)` instance. The recorded dependency exposes
  these declarations, not only the stronger geometric-integrality class.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded public
  `SheafOfModules.IsQuasicoherent` interface, using the individual
  quasi-coherence clause rather than imposing coherence or a kernel condition.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and
  `.Quasicoherent`: `SheafOfModules.IsFinitePresentation`; the recorded
  docstring describes finite local cokernel presentations.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, publicly importing
  `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`. I read both the real
  tensor construction and the dependency's section-normalized adjunction.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, defined by closure of a singleton.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `.Immersion`:
  `IsClosedImmersion`, `IsImmersion` and its factorization characterization.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; `.QuasiCompact`: `QuasiCompact`;
  `.QuasiSeparated`: `QuasiSeparated` (quasi-compact diagonal).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: `SheafOfModules.free`,
  the existing coproduct construction, used for the finite rank clause.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `.fiberι`.

The non-public imports include the recorded proof-dependency modules and
Mathlib matches, including proper/base-change permanence, smooth geometric
reducedness, affine tensor sections, quasi-coherent finite presentation,
affine germs, Nakayama, flat-lfp openness, the affine flatness and presentation
criteria, finite-presentation base change, local immersion gluing, target
locality, spreading isomorphisms, principal opens, open factorization, and
the quasi-compact-open finite-presentation lemma. Three proof-only nodes
have no recorded Lean declaration or Mathlib match at this reading:
`lem-sfb-local-flat-generic-basis-universal-injectivity`,
`lem-sfb-flat-integral-free-surjection-iso-locus`, and
`lem-trf-closed-immersion-finite-presentation-ideal`. They introduce no
notion needed for this signature, and their eventual imports are omitted
until those proof prerequisites are stated. All seven existing proof steps
and their named dependencies are included in the theorem docstring.

Edge cases checked before writing:

- For empty T, the generic-freeness predicate is vacuous and there is exactly
  one empty-scheme factorization, for every rank. This is required even when
  the locus itself is empty.
- For empty S, necessarily X is empty; the same predicate and empty
  representative handle every test and every r.
- For r = 0 the free sheaf on `ULift (Fin 0)` is the zero sheaf. For E = 0,
  the rank-zero locus is all of S and the positive-rank loci are empty.
- For a trivial free module of rank n, the rank-n locus is S and the other
  loci are empty (with their unique section on an empty test).
- For S = X = Spec(k[ε]/ε²), g the identity and E = O/(ε), the rank-one
  predicate requires ε to vanish on the test scheme; it is represented by
  the closed subscheme Spec k. This checks that ambient freeness retains
  nilpotent information, rather than only testing residue-field rank.
- There is no characteristic restriction or fixed relative dimension.
  Every test scheme in the same scheme universe is quantified, as in the
  project's existing pullback and gluing interfaces; there is no smaller,
  independent test universe that could make the predicate vacuous.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: smooth affine geometrically irreducible fibres,
  finitely presented module, fixed generic-free rank represented by a locally
  closed immersion. Eight hits, including local finite presentation,
  smoothness and immersion target-locality; no exact representability result.
- `msearch.py ... leansearch`: “generic fibre free rank locus representable
  locally closed immersion”. Eight hits: immersion constructors, free locus
  and its rank function; none is this theorem.
- `msearch.py ... loogle`: “IsGenericPoint, IsImmersion,
  IsFinitePresentation”. Zero hits; service reported unknown identifier
  `IsImmersion`. Local declarations were read directly instead.
- `msearch.py ... grep`: “generic.*free.*rank|free.*generic.*represent|
  GenericFreeRank|GenericRankLocus” in AlgebraicGeometry. Zero Mathlib hits.
- `rg` of the project's `lean/WeilConjectures` and `lean/Sheaf` for generic
  free/rank terms found generic-freeness and blowup results, but no exact
  statement. Searching the item id in `WeilConjectures` gave no match;
  searching candidate theorem names and `dag/lean_names_upstream.json`
  also gave no duplicate.
- The search did find `smoothGenericFreeRankCondition` in
  `Sheaf.AlgebraicGeometry.SmoothTopDimensionRankDecomposition`. I read its
  full definition: it is the same objectwise predicate. That downstream
  theorem lists this item as a proof dependency, so importing it here would
  close the intended import graph. The signature therefore writes the
  predicate directly, exactly as defined there, and adds no second definition.

Validation: `scompile.py` passed both sandbox elaboration (3.1 s) and the
library-module compile (3.2 s), with no errors or warnings. The required
`deliver2.py --no-push` returned OK: the packet passes server preflight and
per-file compilation.
No new definition node, dependency repair, disputed statement or source
correction is required.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
