## Worker report

The module `Sheaf.AlgebraicGeometry.ProOpenGlobalSectionExtension` states
`AlgebraicGeometry.exists_globalSection_extension_of_quasiCompact_flat_mono`.
Its only theorem proof is `sorry`; it introduces no definitions or helper axioms.
The original node is unchanged except for its `lean` record.

Source checked: the primary Numdam scan of Raynaud, *Un critère d'effectivité de
 descente*, https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf,
Propositions 1.1 and 1.2(i), printed pages 1–2, and Proposition 2.3(i), printed
pages 4–5. The last proposition concerns sections of the induced ringed subspace;
its surjectivity applies to the whole quasi-compact image via Proposition 1.2(i).
The whole proof route of the node, including the empty-image case, is retained in
the theorem docstring.

Hypothesis and clause correspondence:

- Schemes and the given morphism: `{Z Y : Scheme.{u}} (j : Z ⟶ Y)`. Universe `u`
  is explicitly declared, and `set_option autoImplicit false` is used in the file.
- The morphism is quasi-compact, flat and a monomorphism:
  `[QuasiCompact j] [Flat j] [Mono j]`. These are the recorded Mathlib notions.
  Flatness is equivalent to flatness of all stalk maps by `Flat.iff_flat_stalkMap`.
  `Mono j` says precisely that postcomposition with j is injective on Hom sets.
- Quasi-compact source: `[CompactSpace Z]`. Mathlib's compactness is finite-subcover
  compactness without any Hausdorff hypothesis.
- Quasi-separated target: `[QuasiSeparatedSpace Y]`. On schemes this is equivalent
  to the affine-intersection formulation in the node, and to quasi-compactness of
  the diagonal (`quasiSeparatedSpace_iff_quasiSeparated`).
- `E = j(|Z|)` is `Set.range j`, using the underlying-point-map coercion of a
  scheme morphism. The first conjunct quantifies `e y : Y`, assumes `e ∈ Set.range j`
  and `e ∈ closure ({y} : Set Y)`, and concludes `y ∈ Set.range j`. The direction
  of specialization agrees literally with the node.
- Every global section is `∀ s : Γ(Z, ⊤)`.
- The required open subscheme is `∃ V : Y.Opens`, with underlying scheme
  `V.toScheme` and its canonical open immersion `V.ι`.
- Quasi-compactness of that open is `IsCompact (V : Set Y)`. This is equivalent
  to compactness of the open subspace, with no separation assumption.
- Containment of E is `hV : Set.range j ⊆ Set.range V.ι`. By the existing theorem
  `Scheme.Opens.range_ι`, the right-hand side is exactly the subset V of Y.
- The extended function is `t : Γ(V.toScheme, ⊤)`.
- The canonical factorization j_V is the existing construction
  `IsOpenImmersion.lift V.ι j hV`, whose composite with `V.ι` is j by `lift_fac`;
  uniqueness is `lift_uniq`. Its actual structural pullback on global sections is
  `.appTop`. The final equality `.appTop t = s` is precisely j_V^*(t) = s.
- There is no finite-presentation, Noetherian, separatedness, affine-target,
  nonempty-image, or quasi-compact-target assumption.

Statement dependencies used, with source signatures and docstrings inspected:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, declaration
  `AlgebraicGeometry.Flat`, with the stalkwise equivalence at line 106.
- `def-weil-pbc-scheme-conventions`: a convention record with no owning
  declaration or module. Its quasi-compact and quasi-separated notions are
  `AlgebraicGeometry.QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
  and `QuasiSeparatedSpace` from the QuasiSeparated imports. No replacement
  definition is supplied.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, declaration
  `AlgebraicGeometry.IsOpenImmersion`; this same module supplies
  `AlgebraicGeometry.IsOpenImmersion.lift`. `Scheme.Opens.toScheme`, `ι`, and `range_ι`
  are in `Mathlib.AlgebraicGeometry.Restrict`, publicly imported by OpenImmersion.
  `Scheme.Hom.appTop` is the existing pullback from `Mathlib.AlgebraicGeometry.Scheme`.

All recorded proof dependencies that have modules or Mathlib matches are available
through imports. The module explicitly imports as proof-only dependencies
`Mathlib.Topology.Constructible`, `Mathlib.Topology.Spectral.Basic`,
`Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
`WeilConjectures.Topology.PresheafModuleStalkFunctor`,
`WeilConjectures.Topology.InverseImageStalk`,
`WeilConjectures.Topology.ProconstructibleClosureSpecialization`, and
`Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`.
The affine-open-basis and affine-qcqs Mathlib matches are already available through
the scheme/morphism imports. The open-factorization match is the same lift used
in the signature. `lem-sfb-qc-flat-monomorphism-ringed-image` has no recorded Lean
module or Mathlib declaration on the read base; it is a proof dependency only,
so no import for it can be added and it is not needed to state this theorem.

Edge cases checked mathematically before drafting:

- Empty Z: the generalization clause is vacuous; take the empty open V, which is
  quasi-compact, and its unique global section. No binder rules this out.
- j the identity on a quasi-compact quasi-separated scheme: take V = Y and t = s.
- Localization of an affine scheme at an arbitrary multiplicative set: a section
  has a single denominator; it extends to the corresponding principal open.
  This includes localizations not of finite presentation.
- No affine-overlap assumption: the node uses quasi-compact intersections, exactly
  what `QuasiSeparatedSpace Y` provides. The target need not be quasi-compact.
- A single explicit universe covers arbitrary schemes in any common universe;
  there is no test-object universe restriction and no extra universe equation.

Searches actually run with `msearch.py`, group Q82 and this item:

- LeanFinder: `Every global regular function on a quasi-compact flat monomorphism
  into a quasi-separated scheme extends to a quasi-compact open neighbourhood of
  its image`. Eight hits: denominator-clearing and qcqs restriction lemmas,
  `isLocalization_basicOpen_of_qcqs`, and `Scheme.Hom.toImage_app_injective`.
  These do not give extension along an arbitrary quasi-compact flat monomorphism.
- Loogle: `"Flat", "Mono"`. Twelve hits include
  `IsOpenImmersion.of_flat_of_mono`, which additionally assumes
  `LocallyOfFinitePresentation f`, and unrelated flat/mono lemmas. Its full
  signature was read; it does not cover this node.
- Mathlib grep: `(flat.*mono|mono.*flat|pro.?open|section.*neigh|neigh.*section)`
  restricted to AlgebraicGeometry. Fifteen hits, including `FlatMono.lean`,
  `Flat.lean`, `Limits.lean`, and `SchemeTheoreticallyDominant.lean`; no exact match.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `proopen|proOpen|pro.open|global.section.extension|lem-sfb-proopen-global-section-extension|flat.*mono|mono.*flat`
  found existing finite-presentation open-immersion applications and unrelated
  pro-etale functor names, but no matching statement. A separate exact-node-id
  `grep -rn` of `lean/WeilConjectures` found no match. Exact proposed declaration
  and module-name searches in both roots and `dag/lean_names_upstream.json` also
  found no collision.
- Candidate qcqs lemmas were located in
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean`, including
  `exists_of_res_eq_of_qcqs` and
  `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated`; their scope is restriction
  to principal opens/clearing denominators, not this node's arbitrary image.

No statement correction, disputed statement, new node, or dependency repair is needed.

## Second reading by Q82

This dispatcher-started worker is forbidden to start another agent. The maintainer's
independent review therefore remains the independent second reading; this paragraph
records a final self-check and does not claim an independent reviewer.
I reread the node against the signature: all five properties in the hypotheses
(quasi-compact j, flat j, mono j, quasi-compact Z, quasi-separated Y) occur, and
both conclusions occur. The only representation requiring explanation is image
containment via `Set.range V.ι`, justified by `Scheme.Opens.range_ι`. The map in the
last equality is the canonical open-immersion lift, rather than a chosen arbitrary
map. The closure quantifiers preserve the node's generalization direction. No
mismatch was found and no statement text was changed.

## Validation

`scompile.py Q82 lem-sfb-proopen-global-section-extension` compiled the delivered
file successfully in both sandbox and library module modes, including the final
version with `autoImplicit false`. There were no compiler errors or warnings.
The node's signature was checked verbatim against the file, and only the `lean`
field differs from the original node. The Lean file's maximum line width is 89.
