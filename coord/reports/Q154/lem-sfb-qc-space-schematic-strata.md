## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCompactSpaceSchematicStrata` states
`AlgebraicGeometry.AlgebraicSpace.exists_schematic_strata_of_quasiCompact_atlas`.
Its only theorem proof is `sorry`; it adds no definitions or helper theorems.
The node is unchanged except for its `lean` record. No statement correction or dispute.

Hypothesis and conclusion correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`; the algebraic space over it is
  `(X : AlgebraicSpace S)`. The fixed universe is exactly that of the existing
  algebraic-space framework and all scheme tests and field representatives.
- The node explicitly defines quasi-compactness by an atlas. `hqc` existentially
  quantifies `A : Over S` and `a : yoneda.obj A ⟶ X.obj.obj`, with
  `CompactSpace A.left`, `IsRepresentable a`, `IsSurjective a`, and `IsEtale a`.
  Thus quasi-compactness is of the atlas source, not of its identity map or of S.
- `U : ℕ → OpenSubspace X` uses the recorded open-subfunctor definition and its
  inherited inclusion order. Lean index p is the source's positive index p+1.
  `(U 0).val = ⊤` is U_1 = X; `∀ p, U (p+1) ≤ U p` gives every successive inclusion.
- `T : ℕ → Over S` supplies the schemes representing the strata, and
  `i : ∀ p, yoneda.obj (T p) ⟶ (U p).val.toFunctor` supplies their inclusions.
  `IsRepresentableWith (fun _ _ f ↦ IsClosedImmersion f.left) (i p)` is exactly
  the node's closedness after every scheme test. Such a representable closed
  immersion is monomorphic and hence identifies its source with its image
  subfunctor; this is a presentation of the closed subspace, without replacing
  the recorded open subfunctor or introducing another notion of closedness.
- `AlgebraicGeometry.IsReduced (T p).left` is reducedness of the representing
  scheme, using the recorded Mathlib definition (all section rings reduced,
  equivalently all local rings reduced). It is not reducedness of an arbitrary
  base change of a reduced space.
- The composite `i p ≫ (U p).val.ι` maps each stratum to X. Injectivity of its
  `schemePointMap` and the equation for its `Set.range` identify its ordinary
  scheme points with exactly
  `pointImage (U p).val.ι \ pointImage (U (p+1)).val.ι` in `Point X.obj.obj`.
  These are the recorded field point classes and open-subspace images.
- Coverage quantifies over every `K : Type u` with `[Field K]`, every base map
  `s : Spec (CommRingCat.of K) ⟶ S`, and every section
  `x : X.obj.obj.obj (op (Over.mk s))`. Yoneda's equivalence turns x into the
  corresponding field-spectrum morphism `yonedaEquiv.symm x`. Its hypothesis
  `IsRepresentableWith (fun _ _ f ↦ QuasiCompact f.left)` says that after each
  scheme test, the representing projection has quasi-compact inverse images
  of quasi-compact opens, exactly as the node requires. Representability is
  automatic for scheme-source maps to algebraic spaces, so this adds no
  mathematical condition. Its point class is
  `Quot.mk _ (PointRepresentative.mk K s x)`; the conclusion places it in the
  point image of some T p. Quantifying over representatives also covers any
  point admitting at least one such representative, without demanding that
  all its representatives be quasi-compact.
- There is no finite-termination assertion, no quasi-separatedness hypothesis,
  no Noetherian hypothesis, and no separatedness hypothesis on X or the base.
  The stronger atlas conclusion in Stacks 0BBN(1) is used in the proof plan,
  but is not added to this node's conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`; `Mathlib.Algebra.Field.Defs`: `Field` (the latter is
  available through the scheme/algebraic-space imports).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `IsSurjective`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`; its imported `AlgebraicSpacePointClasses` supplies
  `Point`, `PointRepresentative`, and `schemePointMap`. Their full source
  definitions were read, including the common-field relation defining points.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace` and its
  inclusion partial order.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`, whose
  full signature explicitly requires compact preimages of compact opens.

Every recorded proof-dependency module is included as a plain import; Mathlib
proof leaves use Separated, Etale, Pullbacks and QuasiSeparated. Three proof
nodes have neither a Lean record nor a Mathlib match in the read repository:
`lem-sfb-qc-space-affine-etale-atlas`, `lem-sfb-space-separated-fp-composition`,
and `lem-sfb-separated-lqf-affine-finite-set`. They are not needed to type this
statement and have no module to import yet. Their mathematical uses remain
explicit in the theorem's eleven-step docstring. No import was omitted for a
cycle. The maintained source proof has eleven steps (including its absolute
change-of-base step); all are reproduced in the docstring.

Source check: read the full statement and proof of Stacks
`literature/stacks-project/decent-spaces.tex`, lemma-filter-quasi-compact,
Tag 0BBN. Its Z_p → T_p isomorphism gives exactly the schematic reduced strata
used here. The statement requests only the resulting schematic differences
and coverage, as recorded in the node.

Edge cases checked before writing:

- Empty X permits all U p and T p empty; there is no field representative.
- For a scheme X with its identity atlas, the first stratum is X_red and
  subsequent strata may be empty. Nonreduced schemes are included.
- For an n-sheeted split atlas, the only nonempty stratum may occur at n;
  the index shift p ↔ p+1 includes the source's first stratum.
- Infinite atlas fibres are permitted for non-quasi-separated spaces; coverage
  is required only for quasi-compact field representatives, whose geometric
  fibres are finite. No uniform bound or finite filtration was introduced.
- Arbitrary characteristic, including characteristic dividing p!, is retained:
  the proof uses a free constant symmetric-group action, not linear reductivity.
- Repeated opens and empty differences are allowed; reduced empty schemes are
  not excluded by any Nonempty or positivity hypothesis on Lean's index.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder query: "A quasi compact algebraic space has decreasing open subspaces
  with reduced schematic differences covering quasi compact field valued points".
  Eight hits concern `QuasiCompactCover`, `isCompact_iff_exists`, compact-open
  induction, quasi-affine schemes, quasi-sobriety and retrocompact basic opens.
  None states this filtration for algebraic spaces.
- Loogle query: `AlgebraicGeometry.AlgebraicSpace, IsReduced`.
  Zero hits; AlgebraicSpace is unknown to its Mathlib-only index.
- Mathlib grep query: `schematic.strat|AlgebraicSpace|schem.*filtration`, scoped
  to AlgebraicGeometry. Zero hits.
- LeanSearch query: "A quasi compact algebraic space admits a decreasing filtration
  by open subspaces with reduced schematic differences containing every quasi
  compact field point". Eight hits are scheme quasi-separated covers,
  quasi-affineness, Noetherian compactness, `QuasiCompact`, and affine-test
  characterizations. None supplies this statement.
- Direct rg in Mathlib AlgebraicGeometry for schematic strata and schematic
  filtrations: no hits. Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  schematic strata, schematic filtrations, and this blueprint id: only the
  downstream proof docstring in `ReducedSingletonFieldFactorization.lean`
  names the item; there is no existing theorem. The chosen theorem name also
  has no hit in those trees or `dag/lean_names_upstream.json`.

Validation: the prescribed scompile.py compiled both the sandbox and library
module forms cleanly on the server (1.7 seconds each). `autoImplicit false`
ensures every variable and universe is bound. No definitions contain sorry;
the named main theorem has the sole postponed proof.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
