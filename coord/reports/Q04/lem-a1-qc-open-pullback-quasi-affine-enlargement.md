## Worker report

The module `Sheaf.AlgebraicGeometry.QcOpenPullbackQuasiAffineEnlargement` states
`AlgebraicGeometry.qc_open_pullback_quasi_affine_enlargement`, with one `sorry` and
no definitions or additional theorems. The node's mathematical statement is unchanged.

Hypotheses and clauses, individually:

- Schemes X, A and B: `{X A B : Scheme.{u}}`, with the scheme morphisms
  `(a : X ⟶ A)` and `(b : B ⟶ A)`.
- A and B affine: `[IsAffine A] [IsAffine B]`.
- Every quasi-compact open of X is quasi-affine: `hX` quantifies over every
  `U : X.Opens`, assuming `IsCompact (U : Set X)` and concluding
  `U.toScheme.IsQuasiAffine`. Mathlib's quasi-affineness includes quasi-compactness
  and means an open immersion into the affine spectrum of global sections.
- Z and its projection p: `pullback a b` and `pullback.fst a b`.
- An arbitrary quasi-compact open L of Z: `(L : (pullback a b).Opens)` and
  `(hL : IsCompact (L : Set (pullback a b)))`.
- A finite affine family, allowing zero members: `∃ (n : ℕ) (Wj : Fin n → X.Opens)`
  together with `∀ j : Fin n, IsAffineOpen (Wj j)`.
- Its union W: an open `W : X.Opens` with `W = iSup Wj`.
- W quasi-compact: `IsCompact (W : Set X)`.
- The containment p(|L|) ⊆ W: `Set.MapsTo (pullback.fst a b) L W`.
- W times_A B: `pullback (W.ι ≫ a) b`, using the restricted structure map W -> A.
- Both this pullback and L quasi-affine: the two conjuncts
  `(pullback (W.ι ≫ a) b).IsQuasiAffine` and `L.toScheme.IsQuasiAffine`.
- The projection W times_A B -> B quasi-affine: the conjunct
  `IsQuasiAffineHom (pullback.snd (W.ι ≫ a) b)`.
- The induced map L -> W times_A B is open: an existential morphism `i` with
  `IsOpenImmersion i`. Its two projection equations specify its composites to X
  and B as the original maps from L. Thus this is precisely the induced map:
  the open inclusion W -> X is a monomorphism, so the first equation fixes the
  projection to W, and pullback uniqueness fixes i. The equations supply the
  canonical map specification, rather than an unrelated open embedding.
- No quasi-compactness, separatedness, or finite type assumption is made on X or a.
  There are no additional hypotheses and no file-local instances or notation.

Recorded statement dependencies used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme` (publicly available via the imports).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd`, from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  scheme pullbacks exist through `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, from
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `def-nagata-quasi-affine-morphism`: `AlgebraicGeometry.IsQuasiAffineHom`, from
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`. Its field asserts
  quasi-affineness of the preimage of every affine open, exactly the node's notion.
  Absolute quasi-affineness uses `AlgebraicGeometry.Scheme.IsQuasiAffine`, from
  `Mathlib.AlgebraicGeometry.QuasiAffine`.

Proof dependencies were also read and their modules are imported: the affine-open basis
`Scheme.isBasis_affineOpens` and `Scheme.compactSpace_of_isAffine` in
`Mathlib.AlgebraicGeometry.AffineScheme`; `quasiSeparatedSpace_of_isAffine` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; open-immersion base change in
`Mathlib.AlgebraicGeometry.OpenImmersion`; `isQuasiAffineHom_iff_of_affine_open_cover`
in `Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality`; and
`isQuasiAffineHom_baseChange` in `Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`.
The last two are plain proof imports. No dependency repair or new node is needed.

Edge cases checked before writing: if L is empty, take n = 0 and W empty; the empty
union is allowed by `Fin 0`, and both the empty schemes and their structural maps
have the asserted properties. This includes empty X and empty B (Spec of the zero
ring). For b = identity the conclusion is the usual finite affine enlargement of L.
A non-quasi-compact X is allowed: only the image of the compact L needs a finite
cover. A non-separated X is not excluded by any extra typeclass; the given compact-open
hypothesis controls the finite union used in the argument. No independent universe
for a test scheme or finite index can make any hypothesis vacuous.

Sources read: `literature/stacks-project/more-morphisms.tex`,
`lemma-ind-quasi-affine-composition` (finite union of affine neighbourhoods of a compact
image) and `lemma-base-change-ind-quasi-affine` (Tag 0AP7, reduction to affine bases);
`literature/stacks-project/morphisms.tex`, `lemma-characterize-quasi-affine` and
`lemma-base-change-quasi-affine` (Tags 01SM and 01SO). The theorem docstring follows
the node's four proof steps, including its explicit identification of the open pullback.

Searches performed on 2026-10-22:

- `msearch.py ... leanfinder`: "Every compact open of a scheme pullback over affine
  schemes is contained in the base change of a finite union of affine opens and is
  quasi affine if every compact open of the source is quasi affine". Eight results,
  including `IsAffineOpen.isCompact_pullback_inf`, compactness of pullbacks, and
  `Scheme.exists_isQuasiAffine_of_isLimit`; none states this finite enlargement result.
- `msearch.py ... loogle`: `"IsQuasiAffine", "pullback"`. Zero results.
- `msearch.py ... grep`: `IsQuasiAffine|finite.*affine|affine.*finite` in
  `AlgebraicGeometry/QuasiAffine.lean`. Five displayed hits for the definition and
  basic immersion properties; no finite affine enlargement statement.
- `rg` on the project and upstream Lean for the item id, `qc_open.*pullback`,
  `finite.*enlargement`, and the proposed declaration names. No duplicate of this
  statement or declaration; unrelated finite-type module enlargements were found.
  Read the upstream quasi-affine module and the project's target-locality and
  base-change modules in full for their relevant interfaces.

No statement dispute or node correction was found. The existing stage-1 PASS from NG
is a proof-splitting review, not a stage-2 binding; this delivery adds the missing Lean
record. The sandbox initially contained only dispatcher marker files, so there was no
previous Lean module to repair.

Validation: `scompile.py Q04 lem-a1-qc-open-pullback-quasi-affine-enlargement`
compiled this file in both sandbox and library module modes, with no errors or warnings.
An initial elaboration ambiguity in `Set (pullback a b)` was repaired by specifying
`Set (pullback a b : Scheme.{u})`; it now unambiguously uses the scheme pullback,
not a limit in the category of types. The Lean record contains the final signature
verbatim. All universes and variables are explicit; `autoImplicit` is disabled.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
