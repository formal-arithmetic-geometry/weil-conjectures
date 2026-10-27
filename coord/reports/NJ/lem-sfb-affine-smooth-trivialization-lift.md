## Worker report

The module `Sheaf.AlgebraicGeometry.AffineSmoothTrivializationLift` states
`AlgebraicGeometry.exists_affine_smooth_trivialization_lift`, with `sorry` as
its entire proof. It introduces no definition, extra node or dependency repair.
The natural-language statement, dependencies and proof are unchanged.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The commutative k-algebra is
  `(R : Type u) [CommRing R] [Algebra k R]`. There is no `Nontrivial R`.
- The ideal and specified positive nilpotence exponent are `(I : Ideal R)` and
  `(N : ℕ) (hN : 1 ≤ N) (hI : I ^ N = ⊥)`. Bottom is the zero ideal.
- The quotient base is exactly `R ⧸ I`, with quotient map `Ideal.Quotient.mk I`
  and its canonical induced k-algebra structure. No arbitrary quotient map or
  algebra structure is supplied.
- The affine k-scheme is `(T : Scheme.{u}) [IsAffine T]` with structure map
  `(t : T ⟶ Spec (CommRingCat.of k))` and `[Smooth t]`.
- For B equal to R or R/I, `T_B` is precisely
  `pullback t (Spec.map (CommRingCat.ofHom (algebraMap k B)))`.
- The deformation is an arbitrary `(D : Scheme.{u})` with
  `(d : D ⟶ Spec (CommRingCat.of R)) [Flat d]`. There is no affineness,
  finite-presentation, separatedness or finite-type hypothesis on D.
- `θ₀` is the specified isomorphism from the pullback of d along
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))` to `T_(R/I)`.
  `hθ₀` is its compatibility with the second projections, so it is an
  R/I-isomorphism. Compatibility for its inverse follows from the iso laws.
- The existential `θ : D ≅ T_R` supplies the desired isomorphism. Its first
  equation, `θ.hom ≫ pullback.snd ... = d`, says it is over R.
- The second equation says that, on `D_(R/I)`, the composite of θ with the
  projection `T_R → T` equals the corresponding composite of θ₀ with
  `T_(R/I) → T`. This is precisely equality with the specified marking:
  use the canonical reassociation
  `(T ×_k Spec R) ×_R Spec(R/I) ≅ T ×_k Spec(R/I)`.
  The two maps to the latter pullback agree after projection to T by this
  equation, and after projection to Spec(R/I) by the over-R equation and
  `hθ₀`. Pullback uniqueness gives equality of morphisms and hence of
  isomorphisms. Conversely an extension of θ₀ satisfies both equations.
  This formulation avoids selecting a comparison map or an extra isomorphism.

Dependency declarations read and used (no private copies):

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and `IsAffine`,
  Mathlib.AlgebraicGeometry.Scheme and Mathlib.AlgebraicGeometry.AffineScheme.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth. Its affine-local smooth ring-map
  definition is the recorded equivalent definition, not a finite-type-only
  replacement for formal smoothness.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback;
  the existence instance for schemes is in Mathlib.AlgebraicGeometry.Pullbacks.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat (equivalent to stalkwise flatness).

All already stated proof dependencies are imported, with plain imports when
needed only for the proof: WeilConjectures.AlgebraicGeometry.Thickening,
FirstOrderThickeningBaseChange, ThickeningAffineScheme;
Sheaf.AlgebraicGeometry.AffineFormallySmooth;
WeilConjectures.RingTheory.NakayamaNilpotent;
Mathlib.RingTheory.TensorProduct.Quotient; Mathlib.RingTheory.Flat.Equalizer.
The public Pullbacks and Flat modules also give `pullbackSpecIso` and
`Flat.SpecMap_iff`; TensorProduct is provided by the tensor-product imports.
The theorem docstring records all seven proof steps, including the elementary
quotient-tensor identification, the use of flatness of C rather than flatness
of P → C, and the preservation of the marking on taking spectra.

Source reading: Stacks more-morphisms.tex, lemma-thickening-affine-scheme
(06AD), definition-formally-smooth (02H0), lemma-affine-formally-smooth (02H4),
and examples-defos.tex, lemma-glueing-smooth (0DZN). These support the direct
ring argument already recorded in the node. The current blueprint unit
sk-thm-sf-ctf-stability and its direct-images proof were read as route context;
this node is a supporting lemma, not that unit's statement.

Edge cases checked before writing:

- N = 1 means I = 0; the statement lifts every given marking, with no
  induction step. N = 0 is excluded exactly by hN, as in the node.
- T may be empty: IsAffine and Smooth do not imply nonemptiness. The special
  fibre is empty, and nilpotence forces D to be empty as well.
- R may be the zero ring: Algebra k R is allowed and no nontriviality is
  imposed. Both schemes over Spec R are empty.
- D need not be affine in the input. The thickening argument obtains this in
  the eventual proof rather than changing the statement's hypotheses.
- No reducedness, Noetherianity, characteristic, or finite generation of R or
  D is imposed. Nilpotent Nakayama does not require finite generation.
- All rings and schemes live in a common arbitrary universe u, the usual
  Mathlib scheme convention. No quantification over test schemes/algebras in
  a smaller independent universe occurs. Enlarging u accommodates the full
  input data; no cardinality bound or universe equality is assumed in the
  mathematical content.

Searches for an existing declaration:

- `msearch.py leanfinder`, query "A marked trivialization of a flat deformation
  of a smooth affine scheme lifts across a nilpotent ideal of the base ring":
  eight hits, including Algebra.FormallySmooth.lift/exists_lift and
  Algebra.Smooth.formallySmooth. They lift algebra maps, not the marked
  scheme isomorphism with an arbitrary flat source; no exact match.
- `msearch.py leansearch`, query "flat deformation of smooth affine scheme
  trivialization nilpotent ideal lift isomorphism": eight hits on the same
  algebra-map lifting results and formal unramifiedness; no exact match.
- `msearch.py loogle`, query
  "AlgebraicGeometry.Smooth, AlgebraicGeometry.Flat, IsNilpotent": zero hits.
- `msearch.py grep`, query "trivialization|trivialisation|deformation|nilpotent"
  restricted to Mathlib/AlgebraicGeometry: 13 hits on affine space imports,
  formally unramified hom extensionality, and nilpotent sections; none is this
  trivialization theorem.
- `rg` of WeilConjectures and Sheaf for smooth/trivialization combinations,
  `trivialization.*lift|trivialisation.*lift`, and the proposed declaration
  name: no matching theorem. Hits about etale-cover/sheaf trivializations and
  local free frames concern different objects.
- `grep -rn` of WeilConjectures for the node id: no hits. `rg` of
  dag/lean_names_upstream.json and Mathlib/project sources for the proposed
  name also found no declaration. The DAG's existing node is the assigned
  one; no additional notion or node was needed.

Validation: scompile.py compiled the file separately in sandbox and library
module contexts (6.8 s and 1.9 s), with no errors or unexpected warnings.
All Lean lines are at most 100 characters, and every variable and universe is
explicitly bound. No statement dispute or node fault was found.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
