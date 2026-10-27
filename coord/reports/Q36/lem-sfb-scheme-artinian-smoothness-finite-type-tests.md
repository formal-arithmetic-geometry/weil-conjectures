## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeArtinianSmoothnessFiniteTypeTests`
states `AlgebraicGeometry.smooth_of_artinian_lifting_finite_type_tests`, with
`sorry` as its sole proof. It introduces no definitions and changes only the
item's `lean` field. The statement and its four-step proof docstring follow
Stacks Project, More on Morphisms, Tag 02HY (2) implies (1), read in
`literature/stacks-project/more-morphisms.tex`, lemma-lifting-along-artinian.

Every hypothesis and clause is rendered as follows:

- The schemes and morphism are `{W V : Scheme.{u}} (f : W ⟶ V)`.
- Local finite type of `f` is `[LocallyOfFiniteType f]`; local Noetherianity
  of the target is `[IsLocallyNoetherian V]`.
- Every pair of commutative test rings is quantified as
  `∀ (B' B : CommRingCat.{u})`. Commutativity is part of the bundled rings.
- Artinianness is `[IsArtinianRing B'] [IsArtinianRing B]`, the descending
  chain condition on ideals; locality is `[IsLocalRing B'] [IsLocalRing B]`,
  equivalent to a unique maximal ideal. These are the existing Mathlib notions.
- The small extension is `(q : B' ⟶ B)` with `Function.Surjective q.hom`,
  `(RingHom.ker q.hom) ^ 2 = ⊥`, and
  `Module.length B' (RingHom.ker q.hom) = 1`. The ideal's inherited module
  structure is its natural `B'`-module structure. No coefficient algebra or
  residue-field marking is imposed.
- The map called `i` in the node is precisely `Spec.map q`; it is expanded
  directly rather than introduced as a statement-local let.
- The solid square has `(b : Spec B ⟶ W) (c : Spec B' ⟶ V)` and commutativity
  `b ≫ f = Spec.map q ≫ c`, using Lean's left-to-right composition convention.
- Finite type of the bottom map is `LocallyOfFiniteType c → QuasiCompact c →`.
  These two hypotheses are the exact conjunction prescribed by the recorded
  `def-weil-finite-type-morphism` interface; no quasi-compactness of `f` occurs.
- The lift is `∃ b' : Spec B' ⟶ W`; its restriction is
  `Spec.map q ≫ b' = b`, and its composite with `f` is `b' ≫ f = c`.
- The conclusion is `Smooth f`. There is no converse or uniqueness claim.
- The final sentence of the node is respected: no residue-field, separation,
  or quasi-compactness hypothesis on `f` is present.

Dependency declarations read and used, with their full signatures and source
docstrings checked in the pinned source:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`,
  `AlgebraicGeometry.Spec.map` (def-pc-scheme, def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact` (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian` (pqf-def-locnoeth).
- `Mathlib.RingTheory.Length`: `Module.length`
  (def-weil-pbc-module-length, a Mathlib leaf with no `lean` record).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.RingTheory.Artinian.Module`: `IsArtinianRing` and
  `IsArtinianRing.isMaximal_of_isPrime`; and
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`: `IsLocalRing` and
  `IsLocalRing.eq_maximalIdeal`. The predicates occur in the statement and the
  latter declarations implement lem-weil-pbc-artinian-local-unique-prime.

The following modules are ordinary proof imports, as required by stage 2:

- `Mathlib.AlgebraicGeometry.AffineScheme` for
  `AlgebraicGeometry.Scheme.isBasis_affineOpens`
  (lem-weil-pbc-affine-opens-basis).
- `Mathlib.AlgebraicGeometry.OpenImmersion` for
  `AlgebraicGeometry.IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`
  (lem-weil-pbc-morphism-factors-through-open-subscheme).
- `Mathlib.AlgebraicGeometry.Morphisms.Basic` for
  `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`
  (lem-weil-pbc-smooth-local-on-source).
- `Sheaf.RingTheory.ArtinianFiniteTypeResidueCriterion` for
  `RingHom.finiteType_iff_residue_of_isArtinianRing` and
  `AlgebraicGeometry.Spec.finiteType_iff_residue_of_isArtinianRing`
  (lem-sfb-artinian-finite-type-residue-criterion).
- `Sheaf.AlgebraicGeometry.SmoothFixedResidueArtinianTest` for
  `AlgebraicGeometry.smooth_near_of_fixed_residue_artinian_lifting`
  (lem-sfb-smooth-fixed-residue-artinian-test).

The other recorded proof interface `AlgebraicGeometry.locallyOfFiniteType_iff`
(lem-weil-pbc-lft-affine-pairs) is in the public FiniteType import. The node
lem-sfb-finite-type-points-detect-open has no Lean record or Mathlib match in
the read repository, so there is no stated module to import for it; its role
remains explicit in the four-step proof docstring. It is a proof dependency,
not a missing notion needed to type this statement. No dependency repair or
new node is needed.

Edge cases checked before writing:

- An empty source is allowed; the conclusion is smoothness of the empty-source
  map, as in the empty-cover case of the node's proof.
- No nonemptiness, quasi-compactness, or separatedness of either scheme is
  assumed. Non-Jacobson locally Noetherian bases are included.
- Zero rings are Artinian but are not local rings in the source's unique-maximal-
  ideal sense; Mathlib's `IsLocalRing` correctly includes nontriviality. The
  identity extension has kernel length zero and is correctly excluded.
- Length one is not silently replaced by arbitrary square-zero kernels. Both
  requested conditions are explicit, even though square-zero follows from
  the other small-extension hypotheses.
- Residue fields and characteristics are unrestricted; no identification of
  the residue field with a fixed field occurs in this global criterion.
- The tests and schemes share `u`, matching the scheme category and the recorded
  fixed-residue criterion. In particular the test universe is never smaller
  than that of the schemes, so the lifting assumption is not vacuous for
  universe reasons. Every universe and variable is explicitly bound, with
  `set_option autoImplicit false`.

Searches for an existing exact statement, all on 2026-10-24:

- `msearch.py ... leanfinder`, query: "A locally finite type morphism to a
  locally Noetherian scheme is smooth if it lifts small Artinian local
  extensions with finite type bottom maps". Eight hits, all general smoothness
  definitions, relative-dimension variants, or local standard-smooth criteria;
  none is the reverse Artinian criterion with finite type bottom maps.
- `msearch.py ... loogle`, query:
  `"AlgebraicGeometry", "IsArtinianRing", "IsSmooth"`: zero hits.
- `msearch.py ... grep`, query:
  `artinian.*lift|lift.*artinian|artinian.*smooth|smooth.*artinian`: zero hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `artinian.*smooth|smooth.*artinian|Artinian.*[Ll]ift|[Ll]ift.*Artinian|small.extension|SmallExtension`
  found the already-recorded pointwise and fixed-residue criteria, Artin-stack
  consumers, and different deformation-ring constructions. None states the
  present global finite-type-bottom-map criterion. The recorded pointwise
  dependency was reused as a proof import.
- Direct search for the node id in `lean/WeilConjectures` found no declaration.
  Direct search across Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the
  chosen declaration name found no collision.

The prescribed `scompile.py Q36 <item> <module file>` passed both its sandbox
and library-module compilation, each in 1.4 seconds, without errors or warnings.
No statement dispute or node fault was found. No original node field other
than `lean` was changed.

## Second reading by Q36

This dispatcher-started worker was expressly instructed not to start another
agent; the maintainer performs the independent delivery review. No independent
worker reading is claimed here. A final self-check with the node and module
open matched the schemes, local finite type of `f`, locally Noetherian target,
both Artinian local rings, surjectivity, square-zero kernel, length one, both
solid maps, commutativity, finite type of `c`, existence of the lift, both lift
identities, and smoothness of `f` against the clause mapping above. No mismatch
or statement change was found. The only proof is `sorry`, and the docstring
retains each of the four accepted proof steps and its dependencies.
