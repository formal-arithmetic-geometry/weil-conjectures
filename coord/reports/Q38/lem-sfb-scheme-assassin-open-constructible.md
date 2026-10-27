## Worker report

Module `Sheaf.AlgebraicGeometry.SchemeAssassinOpenConstructible` states
`AlgebraicGeometry.Scheme.Modules.isConstructible_fiber_associatedPoints_subset_open`.
Its only postponed proof is `sorry`; no definition or helper is added. The node is
unchanged except for its `lean` record. Source read: Stacks Project,
`literature/stacks-project/more-morphisms.tex`, Tag 05KR,
`lemma-relative-assassin-constructible`, lines 7050–7101. This is exactly the affine
reduction in its proof: the source first reduces to an affine base and then proves
constructibility there. No statement correction or dispute is needed.

Hypothesis and conclusion correspondence:

- Schemes T and B: `{T B : Scheme.{u}}`, with arbitrary explicitly bound universe u.
- The specified morphism: `(g : T ⟶ B)`.
- Finite presentation of g: `[LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g]`, exactly Stacks 01TP as fixed by
  `def-weil-pbc-scheme-conventions`. No separatedness, flatness or Noetherianity
  is imposed.
- Affine base: `[IsAffine B]`.
- The Zariski structure-sheaf module: `(F : T.Modules)`.
- Quasi-coherence and local exact finite-free presentation:
  `[F.IsFinitePresentation]`. Read the full Mathlib definition in
  `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267`: locally the cokernel of
  a morphism between two finite coproducts of the ring sheaf. The instance at
  line 277 supplies `F.IsQuasicoherent`; thus the same hypothesis includes both
  requirements, without a redundant additional binder. It also supplies finite
  type for the later generic-point inputs.
- The open subscheme H: `(H : T.Opens)` represents the canonical restriction
  `H.toScheme`, whose inclusion is `H.ι`. Every open subscheme has this
  presentation up to its canonical isomorphism; no choice of open subscheme is
  excluded. `Scheme.Opens.toScheme` and `Scheme.Opens.ι` were read in Mathlib
  `AlgebraicGeometry/Restrict.lean:46–53`, together with `IsOpenImmersion` in
  `AlgebraicGeometry/OpenImmersion.lean:38`.
- Quasi-compactness of H over B: `[QuasiCompact (H.ι ≫ g)]`, a genuine condition
  on this composite, not on an identity morphism.
- Scheme-theoretic fibre T_b: `g.fiber b`, defined in Mathlib
  `AlgebraicGeometry/Fiber.lean:38` by pullback along `B.fromSpecResidueField b`.
  Its projection is `g.fiberι b`.
- Tensor pullback F_b: `(tensorPullback (g.fiberι b)).obj F`, using the recorded
  actual tensor construction, not Mathlib's differently encoded module pullback.
- Fibre assassin: `associatedPoints ((tensorPullback (g.fiberι b)).obj F)`.
  The recorded definition checks the maximal ideal of each fibre local ring
  against element-annihilator associated primes of the fibre module stalk.
- Underlying open fibre |H_b|: `(g.fiberι b) ⁻¹' (H : Set T)`, exactly the
  base change of the open subscheme on underlying spaces.
- The locus is the set comprehension `{b : B | ... ⊆ ...}` with the preceding
  two sets. `Topology.IsConstructible` of this set is the entire conclusion.
  This uses open retrocompact Boolean constructibility, including over
  non-Noetherian affine B, not the broader finite-union-of-locally-closed notion.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom` (full signatures and docstrings read).
- `def-weil-pbc-scheme-conventions`: a declaration-free convention record;
  its finite-presentation interpretation is the three morphism classes above,
  publicly imported from Mathlib `Morphisms.FinitePresentation` and
  `Morphisms.QuasiSeparated`, with `QuasiCompact` transitively available.
- `pqf-def-coherent`: public import
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing the recorded Mathlib
  `SheafOfModules.IsQuasicoherent` and `IsFiniteType`, as well as
  `Scheme.Modules.IsQuasiCoherentFiniteType` and `RingedSpace.IsCoherent`.
  The last two predicates are not additional assumptions: the node requests
  quasi-coherence and finite presentation, not coherence or only finite type.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the canonical open inclusion above uses it.
- `def-trf-relative-assassin`: `Sheaf.AlgebraicGeometry.RelativeAssassin`,
  `Scheme.Modules.associatedPoints` and `relativeAssassin`. The absolute
  fibre associated-points declaration is the one used here; its complete
  stalk-annihilator definition and the fibrewise relative definition were read.
- `def-pc-module-pullback`: public import
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; it publicly exposes
  `WeilConjectures.AlgebraicGeometry.TensorPullback` and the exact
  `Scheme.Modules.tensorPullback` construction. Its `tensorPullbackObj` is
  change of rings of the abelian inverse image, implementing the stated tensor.
  The section-normalized adjunction and its signature were also read.
- `def-weil-constructible-subset`: `Mathlib.Topology.Constructible`,
  `Topology.IsConstructible`, the Boolean subalgebra generated by open
  retrocompact subsets (full signature and docstring read).

The module plainly imports every recorded proof-dependency module, deduplicated
when already a public statement import. Mathlib proof leaves are imported by
their recorded files. The proof docstring carries all seven node proof steps
and names their inputs. `lem-sfb-generic-fibre-assassin-noncontainment-spreads`
has no Lean declaration in the supplied DAG, so there is no module to import
for it yet; this is a proof prerequisite only, not a missing notion needed for
this stage-2 statement. Its natural-language use is retained in Step 6.

Edge cases checked before writing: empty B gives the empty locus; empty T and
zero F give all B, since the fibre assassin is empty. The open H can be empty
(the condition is then absence of associated fibre points), and H can be all T
(the conclusion gives all B). Empty fibres satisfy the containment vacuously.
No nonemptiness or nonzero condition is introduced. For a point base the locus
is either empty or all the point. No field characteristic is specified or
restricted. General non-Noetherian affine bases remain covered, and no
flatness assumption is added. A quasi-compact open over an affine base is
exactly the compact-open case used in descent; this is only a proof consequence,
not an extra hypothesis in Lean.

Searches actually run:

- `msearch.py ... leanfinder`, query: “For a finitely presented morphism to an
  affine scheme and finitely presented quasicoherent module, the locus where
  fibre associated points are contained in a quasicompact open is constructible”.
  Eight hits: scheme Chevalley image/preimage constructibility, prime-spectrum
  Chevalley, finite-presentation local data and affine section maps. None states
  the assassin containment locus theorem.
- `msearch.py ... loogle`, query: “Topology.IsConstructible,
  AlgebraicGeometry.Scheme.Modules.associatedPoints”. Zero hits; the service
  reports the project-local `associatedPoints` identifier as unknown. This
  does not establish absence from the project; the local searches below do.
- `msearch.py ... grep`, regex `assassin|associatedPoints|IsFinitePresentation`,
  Mathlib `AlgebraicGeometry/Modules`: zero hits. The finite-presentation notion
  was found separately in `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for assassin, associatedPoints,
  relativeAssassin, and constructibility combinations: existing associated-point
  definitions, base change and generic containment spreading, but no theorem
  for this constructibility locus. The recorded modules were opened and read.
- `grep -rn` of the item id in `lean/WeilConjectures`: no hits.
- `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  for the proposed declaration name and assassin/constructible combinations:
  no matches; no duplicate declaration is introduced.

Validation: the prescribed `scompile.py` compiled the sandbox and exact library
module independently on the server (1.8 seconds each), with no diagnostics.
Auto-implicit and relaxed auto-implicit binding are explicitly disabled. Every
line is at most 87 characters. The sole theorem deliberately has a `sorry`
proof, as required for this stage. Dry-run and delivery results follow below.

Delivery dry run: `deliver2.py Q38 lem-sfb-scheme-assassin-open-constructible --no-push`
returned `OK (dry run): commit 826ed35ae7c passes the preflight and compiles; nothing pushed`.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
