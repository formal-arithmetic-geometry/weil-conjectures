## Worker report

The module `Sheaf.AlgebraicGeometry.NagataQCOpenBasechangedAffineChartFP` states
`AlgebraicGeometry.finitePresentation_qcOpen_basechanged_affine_chart` with one `sorry`.
It defines no new notion and proves nothing. The natural-language statement, dependencies,
and proof are unchanged. Every variable and universe is explicitly bound.

The hypotheses and conclusion match the node as follows:

- Schemes S and T: `(S T : Scheme.{u})`.
- Both are quasi-compact and quasi-separated: `[CompactSpace S] [QuasiSeparatedSpace S]`
  and `[CompactSpace T] [QuasiSeparatedSpace T]`. CompactSpace imposes no separation axiom.
- The arbitrary base map: `(t : T ⟶ S)`, without any finiteness, affineness, or separation
  assumption on t.
- The commutative rings A and B: `(A B : Type u) [CommRing A] [CommRing B]`.
- The given finitely presented A-algebra B: `[Algebra A B] [Algebra.FinitePresentation A B]`.
- The affine open V = Spec A of S: `(j : Spec (CommRingCat.of A) ⟶ S)` with
  `[IsOpenImmersion j]`. An open immersion identifies its source with the open subscheme
  given by its image. Its source is exactly Spec A, so this is the specified affine chart,
  not a hypothesis that S is affine or that j is an affine morphism.
- X is exactly `Spec (CommRingCat.of B)`, and its structure map is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j`; no arbitrary structure map is substituted.
- X_T is exactly `pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t`.
  The second projection `pullback.snd` has codomain T, as required.
- Every open subscheme W of X_T: `(W : Scheme.{u})` and a map `i` into this exact pullback,
  with `[IsOpenImmersion i]`. This is the open-subscheme description in the recorded
  open-immersion definition: W is identified with its open image, with the restricted
  structure sheaf. It includes every canonical open inclusion and its isomorphic presentations.
- W's underlying space is quasi-compact: `[CompactSpace W]`. This is not the stronger
  hypothesis `QuasiCompact i`, which the planned proof must derive using the target's
  quasi-separatedness.
- The composite W -> X_T -> T is exactly
  `i ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ j) t`.
- Finite presentation is the three conjuncts `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated` of that same composite, in the order given in the node.

The common arbitrary universe u is the standard universe of Mathlib's category of schemes
and its commutative rings. There are no quantifications over smaller test schemes or rings.
Any particular collection of the data lies in a common universe; no cardinality or smallness
hypothesis is imposed.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-scheme-conventions`: its convention-only record has no module or declaration.
  We follow its explicit finite-presentation convention, namely the three conjuncts above,
  and its quasi-compact/quasi-separated meanings. No replacement definition is needed.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, from
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`, from
  `Mathlib.RingTheory.FinitePresentation`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; existence for schemes is
  supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`, from `Mathlib.Topology.Defs.Filter`.
- `def-sbc-locally-finite-presentation`: its Mathlib match `AlgebraicGeometry.LocallyOfFinitePresentation`,
  from `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-quasi-separated-morphism`: its Mathlib match `AlgebraicGeometry.QuasiSeparated`,
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. Scheme quasi-separatedness is
  `QuasiSeparatedSpace`, with the equivalence to the terminal-map condition read there.

The proof docstring contains all five DAG steps and their dependency ids. The proof
interfaces were read in Mathlib: `Scheme.isBasis_affineOpens`, `Scheme.compactSpace_of_isAffine`,
`quasiSeparatedSpace_of_isAffine`, `quasiCompact_of_compactSpace`,
`QuasiSeparated.of_quasiSeparatedSpace`, `quasiSeparatedSpace_of_quasiSeparated`, composition
and base-change instances for all three properties, and separatedness of monomorphisms
with its quasi-separatedness instance. Their modules are imported; proof-only modules
`AffineScheme`, `Morphisms.Separated`, and `Morphisms.Proper` are ordinary, non-public imports.
The matching proof nodes are Mathlib leaves and need no separate Lean records or modules.

Sources checked: the local Stacks `morphisms.tex`, finite-presentation definition 01TP,
affine characterization 01TQ, composition 01TR, base change 01TS, open immersion 01TT,
and quasi-compact open immersion 01TU. They agree with the five-step proof. In particular,
quasi-compactness of the space W does not by itself imply quasi-compactness of its inclusion
into an arbitrary target. The DAG correctly first establishes quasi-separatedness of X_T.
There is no statement dispute or statement correction.

Edge cases checked before writing: empty W, zero B (and empty Spec B), zero A with its
necessarily zero A-algebra, empty S or T whenever the maps exist, the identity chart,
identity t, W equal to the whole pullback when compact, zero generators or relations in a
presentation, non-affine and non-Noetherian bases, and non-separated but quasi-separated
S and T. None is excluded. No inhabited/nonzero-ring, finite-type t, or affine W assumption
appears. CompactSpace is the space condition, never Hausdorff compactness.

Searches made through msearch.py (all actual query records are retained in searches.jsonl):

- LeanFinder: "A quasi-compact open subscheme of the base change of Spec B, for a finitely
  presented algebra B over an affine open of a qcqs scheme S, is of finite presentation over
  a qcqs S-scheme T". Eight hits, chiefly `Scheme.Hom.finitePresentation_appLE`,
  `LocallyOfFinitePresentation`, its affine characterization, and base-change stability.
  None states the complete compact-open base-changed chart assertion.
- LeanSearch: "A compact open subscheme of a base changed finitely presented affine chart
  has locally finitely presented quasi-compact quasi-separated structure map". Eight hits:
  the constructor for local finite presentation, stability under base change, compact-source
  quasi-compactness, and quasi-separated-source quasi-separatedness. These are generic
  ingredients, not an exact match.
- Loogle: `AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.QuasiCompact,
  AlgebraicGeometry.QuasiSeparated`. Zero hits.
- Mathlib grep: `quasiCompact_of_compactSpace|locallyOfFinitePresentation_Spec|finitePresentation.*[Ss]pec|basechanged.*[Cc]hart`
  in AlgebraicGeometry. Six hits, including `LocallyOfFinitePresentation.SpecMap_iff` and
  `quasiCompact_of_compactSpace`; none is this whole statement.
- Direct rg in upstream WeilConjectures, side lean/Sheaf and dag/lean_names_upstream.json:
  `lem-nagata-qc-open-basechanged-affine-chart-fp|qcOpen.*[Ff]inite|qcOpen.*[Pp]resentation|basechanged.*[Aa]ffine|basechanged_affine_chart`:
  no matches. Additional finite-presentation searches and reads of upstream
  Mathlib/AlgebraicGeometry/Morphisms/{FinitePresentation,QuasiSeparated,QuasiCompact}.lean
  found cancellation, diagonal, and related generic interfaces, not this assertion.
  Side-project finite-presentation affine-chart files concern descent of modules or maps,
  not this theorem. The proposed full declaration name is new.

The previous worker's duplicate-delivery note refers to Q34's reviewed stage-1 split.
The shared item's current JSON has status split and no lean record. This delivery supplies
only its stage-2 statement and does not redo that split.

Validation: scompile.py compiled the delivered module in both sandbox and library mode
within the 60-second per-file limit, without errors or warnings. The required deliver2.py
`--no-push` dry run then passed compilation and server preflight with OK. No new nodes or
dependency repairs were necessary.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
