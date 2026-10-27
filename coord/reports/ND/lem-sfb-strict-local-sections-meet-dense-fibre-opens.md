## Worker report

The delivery states `AlgebraicGeometry.strictLocal_sections_meet_dense_fibre_opens` in
`Sheaf.AlgebraicGeometry.StrictLocalSectionsMeetDenseFibreOpens`. Its only postponed
proof is the named theorem, with the node's five-step natural-language argument in
its docstring. No definition, new node, dependency repair, or statement correction
is needed. The node is unchanged except for `lean`.

Hypotheses and conclusions, clause by clause:

- The commutative ring A is `(A : Type u) [CommRing A]`.
- Noetherianity is `[IsNoetherianRing A]`, the recorded Mathlib predicate.
- Strict henselianity is `[IsStrictlyHenselianLocalRing A]`, the recorded upstream
  class. It extends `HenselianLocalRing A`, which extends `IsLocalRing A`; this
  supplies both locality and nonzeroness. A separate `[Nontrivial A]` was removed
  after the overlapping-instance warning: the nonzero hypothesis is still present
  through the class, rather than omitted.
- S is literally `Spec (.of A)`. Y is `{Y : Scheme.{u}}`, and p is
  `(p : Y ⟶ Spec (.of A))`.
- Smoothness and surjectivity are `[Smooth p] [Surjective p]`. Finite type is
  `[LocallyOfFiniteType p] [QuasiCompact p]`, exactly the conjunction recorded on
  `def-weil-finite-type-morphism`.
- A section is the existing Mathlib record `SplitEpi p`: its `section_` is a map
  S to Y and its `id` is `section_ ≫ p = 𝟙 S`. Thus the first conjunct
  `Nonempty (SplitEpi p)` says precisely that Y(S) is nonempty. No section is a
  hypothesis and no arbitrary section is fixed in advance.
- `∀ (s : Spec (.of A))` covers every point of S.
- `(L : Type u) [Field L] [Algebra ((Spec (.of A)).residueField s) L]` is every
  field extension of the scheme residue field at that point. There is no finite,
  algebraic, separability, or algebraic-closure assumption. All schemes and spectra
  use Mathlib's common, arbitrary universe u; all variables and u are explicit.
- The map from Spec L to S is exactly
  `Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of A)).residueField s) L)) ≫
  (Spec (.of A)).fromSpecResidueField s`, using the extension embedding followed
  by the canonical residue-field point map. O is an open of the actual
  `pullback p` along this map, namely Y_L; no abstract substitute fibre is used.
- O being open is its `.Opens` type; `Dense O.carrier` says it is Zariski dense
  in that fibre product.
- The final `∃ a : SplitEpi p` is inside all the quantifiers on s, L, and O.
  Membership in O is evaluated on `sectionBaseChange p a.section_ a.id (Over.mk …)`
  at `(default : Spec (.of L))`. The spectrum of a field has its existing Unique
  instance, so this is the underlying point of exactly the canonical induced
  L-point, with no auxiliary choice or map assumption. `sectionBaseChange` is
  the unique lift with projections `T.hom ≫ a.section_` and `𝟙 T.left`.
- There are no assumptions of geometric irreducibility, connectedness, constant
  relative dimension, reducedness of A, separatedness of Y, or a chosen section.
  Constant dimension occurs only in the docstring's local proof argument.

Statement-dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing` (and its inherited `HenselianLocalRing`).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme homs,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and the existing
  canonical `Scheme.fromSpecResidueField`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded base-change
  conventions, using `Limits.pullback` and `sectionBaseChange` (defined in its
  public dependency `WeilConjectures.AlgebraicGeometry.Picard.Defs`). The recorded
  `baseChange_section_characterization` confirms the projection characterization.

The modules of all recorded proof dependencies are imported with plain imports,
including the henselian smooth lifting, separable-point density, constant local
component dimension, nowhere-dense dimension drop, and the Mathlib base-change,
open immersion and Noetherianity tools. The already public statement imports
supply smooth open composition and smoothness under base change. Three proof
nodes have no recorded Lean declaration or Mathlib match at inspection time, so
no nonexistent module is imported for them:
`lem-sfb-smooth-space-dimension-strata`,
`lem-sfb-section-value-closure-dimension-specialization`, and
`lem-sfb-rational-density-field-extension`. They are proof prerequisites only,
not missing notions of this statement; their uses are spelled out in the docstring.

Source checked: the primary BLR scan linked in the node was opened and read online
at printed p.47 (2.3 Proposition 5), pp.125–126 (5.3 Lemma 6 field-extension
paragraph), and pp.126–127 (Lemma 7). Proposition 5 supplies lifting from the
closed fibre; Lemma 7 supplies the section-value dimension argument. The
field-extension paragraph explicitly has the dense-open conclusion for an
arbitrary extension of the point's residue field. The proof in the node applies
these tools to an affine open in one relative-dimension stratum, so the Lean
statement does not inherit separatedness or normality from the surrounding
birational-group-law construction.
Source link: https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf

Edge cases checked before writing: the zero ring is excluded by strict
henselianity/locality; the empty Y is excluded by surjectivity over nonempty
Spec A. Each scalar-extended fibre is nonempty, so its empty open cannot satisfy
the density premise. O equal to the whole fibre is allowed. Relative dimension
zero, disconnected fibres, and components of different relative dimensions are
all allowed. Only one stratum is used in the proof, and the conclusion does not
claim density on every component. The identity extension and arbitrary
inseparable or transcendental extensions are allowed. The closed point, generic
points, and intermediate points s are all covered. An imperfect separably closed
residue field does not need to be algebraically closed. Nilpotents in A are
allowed. Choosing `default` introduces no point restriction since Spec L is a
singleton.

Searches for an exact existing statement (2026-10-24):

- `msearch.py ... leansearch`, query `smooth surjective morphism strictly henselian
  local ring sections dense open fibre`: eight hits for smoothness definitions,
  their constructors, and ordinary dominance; none states this result.
- `msearch.py ... leanfinder`, query `Over a Noetherian strictly henselian local
  ring sections of a smooth surjective scheme meet every dense open in every
  field extension of a fibre`: eight hits, including residue surjectivity,
  standard-smooth presentations, HenselianLocalRing.TFAE, and dominance; no match.
- `msearch.py ... loogle`, query `"IsSmooth", "section"`: zero hits.
- `msearch.py ... grep`, pattern
  `henselian.*smooth|smooth.*henselian|section.*dense`, in AlgebraicGeometry:
  one irrelevant hit `section DenseOpen` in Mathlib birational geometry.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with those patterns and
  `sections.*[Dd]ense|strict.*[Ll]ocal.*[Ss]ection`: existing strictly henselian
  étale section/lifting and cohomology results, unrelated sheaf sections and
  birational dense-open sections; no smooth arbitrary-fibre dense-open result.
  The node-id search of `lean/WeilConjectures` has no hits.
- Name/concept checks in both AlgebraicGeometry source trees and
  `dag/lean_names_upstream.json` find no existing declaration with the proposed
  name or this signature. Existing `sectionBaseChange` and `SplitEpi` are reused.

Validation: every compile is through `scompile.py`. The first server compile
identified an underdetermined coercion `Dense (O : Set _)`; using the existing
`Opens.carrier` fixes it. The next compile identified the redundant nonzero
instance described above; it was removed. The wrapper's local path encountered
`OSError(28, 'No space left on device')`, and its authorized server confirmation
compiled the actual module. Final clean compile and delivery preflight are run
after these repairs.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
