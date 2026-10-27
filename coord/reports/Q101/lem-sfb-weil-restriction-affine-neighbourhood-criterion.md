## Worker report

States `AlgebraicGeometry.weilRestriction_representable_of_affineNeighbourhood` in
`Sheaf.AlgebraicGeometry.WeilRestrictionAffineNeighbourhood`, with its sole proof `sorry`.
Only the item's `lean` field changes. No new definitions, dependency repairs, statement
corrections, additional assumptions, or disputed statements are needed.

Source checked: BLR, Néron Models, §7.6 Theorem 4, printed pp.194–195, PDF pages
200–201 (zero-based), in the primary-source scan
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
The source describes the restriction functor at the start of §7.6 (printed p.191).
The current blueprint unit was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`;
this is an auxiliary criterion in its existing DAG refinement, not that unit's statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes S, S', Z: `{S S' Z : Scheme.{u}}`, with the universe `u` explicitly declared.
- Finite locally free p: `(p : S' ⟶ S) [p.IsFiniteLocallyFree]`, using the exact
  dependency's existing class (finite, flat, locally of finite presentation).
- Z over S': `(q : Z ⟶ S')`. The composite to S is `q ≫ p`.
- Each point s of S: the hypothesis `h` begins `∀ (s : S)`.
- The actual fibre `Z ×_S Spec κ(s)` is
  `pullback (q ≫ p) (S.fromSpecResidueField s)`.
  `fromSpecResidueField` is the existing canonical residue-field point map.
- Every finite subset of that fibre: `(P : Set ↥(pullback ...)), P.Finite → ...`.
  This quantifies over sets of points of the scheme pullback, not pairs of points,
  geometric points, or an unrelated test algebra universe. The explicit `↥` makes
  Lean elaborate the carrier of a scheme rather than a pullback in `Type`.
- An affine open subscheme of Z: `∃ U : Z.Opens, IsAffineOpen U ∧ ...`.
  Mathlib's `IsAffineOpen U` means that the corresponding open subscheme is affine;
  its inclusion is the standard open immersion, not additional input data.
- Containment via the natural map to Z:
  `(pullback.fst (q ≫ p) (S.fromSpecResidueField s)) '' P ⊆ (U : Set Z)`.
  Thus containment concerns the image in Z, exactly as in the node.
- Existence of a scheme over S: `∃ W : Over S` bundles the scheme and structure map.
- The functor F is written directly as
  `(Over.pullback p).op ⋙ yoneda.obj (Over.mk q)`.
  On `op X` its value is `((Over.pullback p).obj X ⟶ Over.mk q)` in `Over S'`.
  The source is `Over.mk (pullback.snd X.hom p)`, hence the value is precisely
  `Hom_{S'}(X ×_S S', Z)`. `Over.pullback` maps a test morphism to its canonical
  base-change morphism. Yoneda then acts by precomposition, as required.
- Natural bijections `Hom_S(X,W) ≃ F(X)`: the conclusion is
  `Nonempty (yoneda.obj W ≅ (Over.pullback p).op ⋙ yoneda.obj (Over.mk q))`.
  This is a natural isomorphism of set-valued functors on `(Over S)ᵒᵖ`; its
  components are bijections for every test scheme, and its naturality is part of
  the isomorphism. `Nonempty` merely makes existence of the isomorphism a proposition.
- No quasi-compactness, separatedness, smoothness, nonemptiness, affine-base,
  finite-type, fixed-degree, positive-rank, or surjectivity assumptions occur on Z or p.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (the existing locally ringed-space definition).
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
  Scheme pullback existence comes from the dependency imports.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`; it appears through `S.fromSpecResidueField s`, whose
  domain is `Spec (S.residueField s)`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the open subscheme is encoded by `Z.Opens`,
  with its standard inclusion. `Mathlib.AlgebraicGeometry.AffineScheme` supplies
  `AlgebraicGeometry.IsAffineOpen` for these opens.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField` and `Scheme.fromSpecResidueField`.

Other existing APIs used: `CategoryTheory.Over.pullback` from
`Mathlib.CategoryTheory.Comma.Over.Pullback`, and `CategoryTheory.yoneda` from
`Mathlib.CategoryTheory.Yoneda`. No copy of either functor is defined.

All stated proof dependency modules are imported, with proof-only imports private:
Restrict (open preimage fibre product); Gluing (morphism gluing); Finite, Affine,
Proper, UniversallyClosed and QuasiFinite (finite permanence and finite closed maps
with finite fibres); PullbackCarrier (base-change image); AffineScheme (affine-open
basis and affine basic opens); Spectrum.Prime.Topology (localization/basic opens);
Ideal.Operations (prime avoidance); ResidueField (evaluation vanishing);
Fiber (scheme-theoretic fibre); and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`
(`AlgebraicGeometry.isRepresentable_of_isSheaf_of_zariskiCovers`). Statement imports
are public even when also used by the proof. The sole as-yet-unstated proof dependency
`lem-sfb-affine-weil-restriction-charts` has no `lean` or `mathlib_match` and therefore
no module to import at delivery preparation; its step is recorded explicitly in the
docstring. It is not a statement prerequisite of this item. The maintainer adds its
proof import once it lands, according to stages/2-statements.md §3.7.
The theorem docstring carries all five proof steps, including the prime-avoidance
refinement over a base affine open, the arbitrary-base-change bad-locus identity,
and the empty finite subset case.

Edge cases checked mathematically before writing:

- Empty P is permitted; the empty open subscheme of Z is affine and contains its image.
- If S is empty, all test S-schemes are empty and the statement remains meaningful.
- If S' is empty (rank zero), then Z is empty, F is the terminal presheaf, and S
  represents it. No positive rank or surjectivity is imposed.
- If Z is empty and p has varying rank, F consists exactly of tests whose pullback
  is empty, represented by the open rank-zero locus. The statement allows this.
- For p the identity, F is the Yoneda functor of Z over S; the conclusion specializes
  to its usual representability. The affine-neighbourhood premise is retained exactly.
- Non-quasi-compact, nonseparated, nonsmooth and nonreduced Z are not excluded.
- Test morphisms are all morphisms in `Over S`, including nonflat and nonreduced
  base changes. No finite-set witness, scheme carrier, or test object uses a smaller
  independent universe. A common arbitrary scheme universe covers all the inputs.

Searches for an existing statement (2026-10-24, using prescribed msearch.py):

1. LeanFinder: “Weil restriction along a finite locally free morphism is representable
   by a scheme if every finite subset of each fibre lies in an affine open”. Eight hits:
   generic local representability, finite fibres, finite morphisms and finite presentation;
   no result for this restriction-of-scalars criterion.
2. Loogle: `"WeilRestriction"`. Zero hits.
3. Mathlib grep: `WeilRestriction|weilRestriction|restriction of scalars`, subdirectory
   `AlgebraicGeometry`. Zero hits.
4. LeanSearch: “Restriction of scalars along a finite locally free morphism of schemes
   is representable if finite subsets of fibres have affine open neighbourhoods”.
   Eight hits about restriction to opens, affine opens, and finite morphisms; no match.
5. Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `WeilRestriction|weilRestriction|weil[Rr]estriction`: only unrelated constant-Weil
   restriction maps and a henselian-inertia kernel declaration. No scheme Weil
   restriction representability declaration. Additional concept searches in their
   AlgebraicGeometry subdirectories found only restriction of module scalars and
   unrelated Yoneda/base-change statements. Searching the item id in
   `lean/WeilConjectures` and `dag/lean_names_upstream.json` found no attachment.
6. The chosen declaration name and module basename were searched in Mathlib, both
   project libraries, and `dag/lean_names_upstream.json`; no collision was found.

Validation: compiled with the prescribed server `scompile.py`; see final dry-run
validation below. The first elaboration revealed that a plain `Set (pullback ...)`
was interpreted using pullbacks of types; making the scheme carrier explicit as `↥`
repairs that elaboration without changing the mathematical statement.

## Second reading by Q101

A separate in-thread reading reopened the node, the full Lean file, the six dependency
records and their source declarations. No other agent was started, as required by the
dispatcher; the maintainer performs the independent review of the delivered statement.

Checked each binder against the node: three arbitrary schemes, a finite locally free
p, the structure map q, every base point, every finite subset of the actual fibre,
and one affine open of Z containing its projected image. Checked the conclusion:
W is an S-scheme, and a single natural isomorphism supplies all the required
bijections simultaneously with precomposition naturality. There is no arbitrary
replacement map or assumption supplying the desired representation. Universes and
all variables are explicit. No mathematical mismatch was found and the node's
statement remains unchanged. The only revision was the explicit scheme-carrier
coercion required by Lean's elaborator. All proofs remain `sorry`; no definitions
or axioms were introduced.
