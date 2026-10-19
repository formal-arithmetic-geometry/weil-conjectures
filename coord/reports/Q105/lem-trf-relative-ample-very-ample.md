## Worker report

Item: `lem-trf-relative-ample-very-ample`, group Q105, stage 2.

Delivered `Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple`, declaration
`AlgebraicGeometry.Scheme.Modules.relative_ample_very_ample`, with its sole proof `sorry`.
The new definition module is `Sheaf.AlgebraicGeometry.RelativelyVeryAmple`; it contains
no theorem and no `sorry`. No dependency record is repaired and no statement is corrected.

The source was read locally in `literature/stacks-project/morphisms.tex`: Definitions
01VH (`definition-relatively-ample`) and 01VM (`definition-very-ample`), Lemma 01VR
(`lemma-relatively-very-ample`), and Lemma 01VU (`lemma-finite-type-ample-very-ample`).
The original node statement and all eight proof steps are preserved. The only item-node
changes are `lean` and adding the new definition node to `stmt_deps`.

Hypothesis and clause correspondence:

- Schemes and the specified morphism `f:Y→X`: `{Y X : Scheme.{u}} (f : Y ⟶ X)`.
  The single arbitrary universe is the usual scheme/module universe; it imposes no
  dimension, characteristic, separatedness, nonemptiness, or Noetherian assumption.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two conditions
  in the dependency's record. Mathlib has no bundled finite-type morphism class here.
- Quasi-compact base: `[CompactSpace X]`, with no Hausdorff requirement.
- The invertible module: `(M : Y.Modules) [M.IsInvertible]`.
- Relative ampleness: each left side of an iff is `QuasiCompact f ∧ ∀ V : X.Opens,
  IsAffineOpen V → ...`. Its final term is the dependency's absolute
  `@IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj M) hM`.
  The existential `hM` supplies only the proof argument of the absolute definition;
  restriction of an invertible module is invertible, so no extra hypothesis is introduced.
- Tensor powers are the existing `M.tensorPow n`, including the structure module at zero.
- Some positive power: `∃ n : ℕ, 1 ≤ n ∧ IsRelativelyVeryAmple f (M.tensorPow n)`.
- Every sufficiently large power: `∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
  IsRelativelyVeryAmple f (M.tensorPow n)`. A natural-number threshold exactly expresses
  eventuality; it does not require the zeroth power to be very ample.
- The theorem asserts both iff clauses in a conjunction, so all three conditions are
  equivalent. It also conjoins the independent final assertion.
- In that assertion, `∀ (Z : Scheme.{u}) (g : Z ⟶ X) [QuasiCompact g]
  (N : Z.Modules) [N.IsInvertible]` quantifies over every quasi-compact morphism over
  the same base, with no finite-type assumption on `g`.
- The premise `IsRelativelyVeryAmple g N` is exactly the projective-bundle immersion
  notion defined below, without finite-type conditions on its module witness.
- Quasi-separatedness is `QuasiSeparated g`.
- Evaluation is the actual counit `(tensorPullbackSectionAdjunction g).counit.app N`.
  `Epi` states sheaf surjectivity (equivalently surjectivity on stalks), not surjectivity
  on all open-section groups. The normalized unit is the actual section `1 ⊗ m`.
- `∃ hF : ((pushforward g).obj N).IsQuasicoherent` supplies the quasi-coherence needed
  to form the canonical projective bundle of `g_*N`; it is a conclusion, not an assumption.
- `r` targets that exact bundle. The composite equality says it is over `X`.
  `ProjectiveBundleQuotientGeometry.IsCanonicalMap` applied to the evaluation counit
  fixes its homogeneous-fraction formula. Thus this is the associated evaluation map,
  not an arbitrary immersion with the same pulled-back line. `IsImmersion r` is the
  final claimed property.

Dependency declarations used and inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, its morphisms and open subschemes.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (compactness without Hausdorffness).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.IsAmple`; its full live
  source was read via `scompile.py --source` because it is absent in the older source
  checkout. This is the absolute nonvanishing-locus definition, not the upstream
  projective/closed-immersion variant named `AlgebraicGeometry.IsAmple`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`; its
  canonical symmetric-algebra relative Proj is used, while its finite-type and
  closed-immersion requirements are not imposed on relative very ampleness.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: `Scheme.Modules.IsQuasiCoherentFiniteType`;
  its first factor is the existing `SheafOfModules.IsQuasicoherent`, used for `E` and
  `g_*N`. There is no finite-type assumption on these modules in the statements.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion`; the latter is the
  immersion notion in the dependency's final paragraph.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the existing
  `tensorPullback`, `tensorPullbackSectionAdjunction`, and normalized comparisons.
  The counit of this recorded normalized adjunction is the evaluation arrow.
- For `def-pur-sheaf-tensor-product`, the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` interface was read.
  This theorem needs only the existing scheme-module tensor powers, already used by
  the absolute `IsAmple` dependency and defined on the same sheaf tensor product;
  it neither constructs cochain tensors nor needs the cochain-universe instances.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry`: `TautologicalQuotient`,
  `IsCanonicalMap`, and `projective_bundle_quotient_geometry`, with the full signatures
  and docstrings read. `TautologicalQuotient` includes chart isomorphisms to the actual
  degree-one twist and a generator normalization; its line cannot be an arbitrary
  invertible module. Its existence is the recorded theorem's conclusion.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData`, the existing symmetric algebra and relative
  Proj construction, with no alternate symmetric algebra or projective bundle.

All recorded project proof-dependency modules are imported for the eight-step proof plan,
including the affine ample immersion, finite global generation, Segre, graded immersion
criterion, normalized adjunction, invertible tensor-pullback, and qcqs pushforward modules.
The Mathlib immersion, finite-type, separation and locality APIs are present in their
import closures. No downstream consumer is imported, so no import cycle is introduced.

Edge cases checked: `n=0` is excluded only from the positive-power existential; the
threshold in the eventual statement may be increased to one. Empty `X` forces empty `Y`;
the finite-cover maximum includes one. Empty `Y`, `Z`, and affine opens are allowed,
with the invertibility and ampleness point conditions vacuous where appropriate. There
is no finite coordinate dimension or finite-generation restriction on projective-bundle
witnesses. The evaluation assertion does not add finite type on `g`, even though the
first part assumes it for `f`. Positive characteristic and arbitrary base schemes remain
allowed. Global sections of a sheaf quotient need not be surjective, which is why the
statement correctly uses `Epi` on the sheaf morphism.

Searches (all run through the prescribed wrapper where applicable):

- LeanFinder: “Relative ampleness for finite type scheme morphisms over quasi compact
  base is equivalent to a positive power being relatively very ample”; eight unrelated
  finite-type/quasi-compactness hits, no matching statement.
- LeanSearch: “relative ample invertible sheaf finite type scheme morphism positive
  powers relatively very ample”; eight finite-type, generators and basic-open hits,
  no matching theorem.
- Loogle: `IsAmple, IsVeryAmple`; zero hits, unknown `IsAmple`.
- Mathlib grep: `relative.*[Aa]mple|[Ii]sVeryAmple|relatively.*very` in
  `AlgebraicGeometry`; zero hits.
- For the new definition, LeanSearch: “Relative very ample invertible sheaf immersion
  projective bundle of arbitrary quasi coherent module”; eight quasicoherent and
  projectivization hits, no relative very ample definition.
- Loogle: `IsRelativelyVeryAmple`; zero hits, unknown identifier. Mathlib grep:
  `IsRelativelyVeryAmple|IsRelativeVeryAmple|def IsVeryAmple`; zero hits.
- `rg` of both named project trees for relative ampleness, very ampleness and this
  item found several different theorems, and upstream `Modules/VeryAmple.lean:60`.
  Reading that definition showed it requires a closed immersion into FINITE projective
  space. It does not match the arbitrary-module immersion notion here.
- DAG grep found this theorem and `lem-trf-proper-fibrewise-ample-projective`, but no
  definition node for relative very ampleness. `tools/blueprint_refs.py search
  'relatively very ample'` returned zero blueprint matches. The ancestor command
  returned `lem-trf-local-term-locality`. Proposed names are absent from
  `dag/lean_names_upstream.json` and the searched Lean source trees.

Validation: `scompile.py Q105 lem-trf-relative-ample-very-ample` with both delivered
files passed separately in dependency order (about 3.2 to 3.6 seconds per check).
No errors or unexpected warnings. No `#check`, local notation, local instances,
auto-bound variables, or proofs other than the expected theorem `sorry` remain.
No `STATEMENT-DISPUTED` finding.

## New nodes

`def-trf-relatively-very-ample` supplies exactly the missing notion of Stacks Definition
01VM: immersion over the base into P(E) for an arbitrary quasi-coherent E, pulling the
canonical normalized O(1) back to the module. Its module defines
`Scheme.Modules.IsRelativelyVeryAmple` by the existence of E, its quasi-coherence proof,
a normalized `TautologicalQuotient` D from the already recorded quotient geometry,
and an immersion i over the base with the required line isomorphism. This definition
uses actual pre-existing relative Proj, tensor pullback, and chart-normalized twists;
it chooses no data from a bare existence axiom and contains no sorry. Its search records
include the wrapper outputs verbatim as JSON plus the Mathlib/upstream/side/DAG searches.
The only upstream candidate uses closed finite-projective-space embeddings and is
strictly different in the nonproper cases allowed here. The node is in the item's
chapter and unit, with its ancestor and full ancestry path, and is cited by the item.

## Second reading by Q105

Author's second pass, with both node JSON files and both final modules open; this is
not represented as the maintainer's independent review. The independent delivery review
is performed by the maintainer under the dispatcher's instructions.

Rechecked the finite-type pair of instances, compact base, invertibility, and both
copies of the affine-open ampleness condition against the original statement. Both
biconditionals use the same condition; positive and eventual exponent quantifiers match.
Rechecked the new predicate's quasi-coherent E, unrestricted module size, immersion,
base composite, and normalized O(1) pullback. No finite-type condition on E or closedness
was imported from the similarly named upstream definition. Rechecked that the final
g-quantifier does not inherit finite type, its evaluation is a normalized counit, and
its canonical-map predicate uses this very counit with target P(g_*N). The three claimed
properties are all present; quasi-coherence of g_*N is supplied as a conclusion to type
the target. The arbitrary universe and empty cases remain allowed. No statement mismatch
was found and no mathematical clause was changed. The new record adds only the needed
definition; all existing item fields are preserved apart from lean and that dependency.
