## Worker report

The module `Sheaf.AlgebraicGeometry.StackUniversalInjectivityCriteria` states
`CategoryTheory.stack_universalInjectivity_criteria`, with proof `sorry`.
Source read: Stacks `stacks-morphisms.tex`, definition-universally-injective
(lines 2663 onward) and Tag 0CPN, lemma-universally-injective (2694–2760).
Its docstring includes every step of the accepted DAG proof, including the
common-field argument and the nonempty affine chart rational-point argument.
No mathematical statement correction, new definition, or dependency repair is needed.

Hypotheses and clauses:

- The base scheme is `{S : Scheme.{u}}`. `universe u v w` is explicit, and
  `set_option autoImplicit false` prohibits undeclared variables. The total
  categories have hom universe `max u v` and object universe `max (u+1) w`;
  these bounds include the scheme base and its discrete representables. They
  permit arbitrary larger bounds, without making field tests smaller than S.
- X and Y are categories over `Over S`, and `f : BasedFunctor X Y` is the
  given morphism over S. `hX : IsAlgebraicModuliStack X` and `hY` impose
  precisely stack descent, algebraic-space diagonal, and existence of a
  representable smooth surjective scheme atlas. There is no representability,
  separation, finiteness, or DM condition on f.
- Criterion (1) quantifies over every `Z`, `IsAlgebraicModuliStack Z`, and
  `g : BasedFunctor Z Y`. `moduliTwoFiberFst g f` is the projection
  `Z ×_Y X → Z`. Its `moduliPointMap` is required to be injective. The order
  of the fibre factors follows the source definition and is the canonical
  swap of the node's displayed `X ×_Y Z → Z`.
- Criterion (2) is `Function.Surjective (moduliPointMap
  (moduliRelativeDiagonal f))`. The existing relative diagonal sends an
  object to `(x,x,id)`, rather than using an arbitrary comparison morphism.
  Existing point classes are the quotient of field objects by arrows and
  their equivalence closure; for fibred groupoids this is precisely the
  common-extension/isomorphism relation in the node. No topology predicate
  is needed for these injectivity and surjectivity assertions.
- Criterion (3) binds `K : Type u`, `[Field K]`, `[IsAlgClosed K]`, and the
  structural map `a : Spec (.of K) ⟶ S`. Objects x₁ and x₂ lie in
  `Functor.Fiber X.p (Over.mk a)`. The iso β is between their images under
  `moduliFiberMap f (Over.mk a)`. The conclusion `∃ α : x₁ ≅ x₂,
  ...mapIso α = β` lifts that exact β and imposes no uniqueness.
- The conclusion is `(1 ↔ 2) ∧ (2 ↔ 3)`, exactly equivalence of all three
  conditions. Neither implication nor the specified-isomorphism clause is
  omitted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  morphisms; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsModuliStack`,
  `IsFibredInGroupoids`, `HasAlgebraicSpaceDiagonal`, `HasSpaceBaseChange`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `moduliFiberMap`. These are
  the existing total-category, triple, and fibre functor constructions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its scheme-test representability/étale/surjectivity predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliFieldObject`,
  `ModuliFieldRelation`, `ModuliPoints`, `moduliPointMap`, `moduliRelativeDiagonal`.
  These point and diagonal constructions are general and impose no DM
  hypothesis. Added its already landed definition node and the already landed
  algebraic-moduli-stack definition node to stmt_deps, as permitted by §5.
- `Mathlib.Algebra.Field.Defs`: `Field`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`. The algebraic closure
  proof input is `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- Recorded Mathlib proof inputs are imported: `LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `residueFieldIsoBase`/`SpecMap_residueFieldIsoBase_inv` from
  `Mathlib.AlgebraicGeometry.AlgClosed.Basic`,
  `Scheme.SpecToEquivOfField` and the residue-field point maps from
  `Mathlib.AlgebraicGeometry.ResidueField`, and
  `MaximalSpectrum.instNonemptyOfNontrivial` from
  `Mathlib.RingTheory.Spectrum.Maximal.Basic`.
- The five stack-specific lemma proof dependencies have no recorded Lean
  statements in the read snapshot, so there are no corresponding proof imports
  yet. They are proof inputs, not missing notions of this statement. All
  statement dependencies have usable existing interfaces; the size convention
  is metatheoretic and is rendered by the explicit universe binders.

Edge cases checked: X empty makes the point tests and geometric fullness vacuous,
while the empty diagonal target is surjected onto. The identity morphism has
identity projection/diagonal up to the canonical isomorphisms and lifts every β.
For `BG → Spec K`, there is one geometric isomorphism class and fullness asks
existence only; automorphism uniqueness is correctly not required. Conversely,
`Spec K → BG` must lift each automorphism of the trivial torsor, illustrating why
mere injectivity on geometric isomorphism classes would be too weak. All field
characteristics are allowed. No quasi-compactness is imposed on diagonal fibres.

Searches (the wrapper saved their actual results in searches.jsonl):

- LeanFinder: "Universal injectivity of an algebraic stack morphism is
  equivalent to surjectivity of the diagonal and fullness on geometric fibre
  groupoids" returned eight scheme-only results, including
  `AlgebraicGeometry.UniversallyInjective.iff_diagonal`; none apply to stacks.
- Loogle: `"UniversallyInjective", "diagonal"` returned
  `AlgebraicGeometry.universallyInjective_eq_diagonal` and
  `AlgebraicGeometry.UniversallyInjective.iff_diagonal`, both for schemes.
- Mathlib grep: `AlgebraicStack|ModuliPoints|moduliRelativeDiagonal|universally.injective.*stack`
  returned zero hits.
- The inherited LeanSearch query about universal injectivity and fullness on
  geometric point groupoids returned eight scheme-only results (saved log).
- rg on project `lean/Sheaf/AlgebraicGeometry` and upstream
  `lean/WeilConjectures/AlgebraicGeometry` found scheme universal-injectivity
  results and unrelated references, with no stack criterion. Search for this
  node id in `lean/WeilConjectures` found no declaration.

The interrupted predecessor's stage-1 gate refusal does not apply to this
stage-2 task: the live queue has stage 2, and the item has no Lean record.
The brief's explicit 2026-10-22 stage handoff authorizes continuing. No delivery
was present in the sandbox at restart (only the draft Lean file and search log).

Validation: the saved module compiled successfully through scompile.py in both
sandbox and library mode. The final packet is also compiled by deliver2.py's
required dry run; expected sorry warnings alone are permitted.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
