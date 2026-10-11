## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.Smooth` defines the three notions in the node. `SmoothMorphism f` is exactly the conjunction `LocallyOfFinitePresentation f ∧ FormallySmooth f`; the first conjunct renders locally of finite presentation and the second uses the dependency declaration `AlgebraicGeometry.FormallySmooth` (module `Sheaf.AlgebraicGeometry.FormallySmooth`). `SmoothMorphismOfRelativeDimension n f` retains smoothness and binds every point `x : X`, requiring `topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)`, which is the dimension of the fibre at x. `EtaleMorphism f` is the n=0 specialization.

The scheme morphism binders are `{X Y : Scheme.{u}}` and `f : X ⟶ Y`. The affine first-order lifting quantifiers are rendered by the dependency `FormallySmooth`, which imports `IsFirstOrderThickening` from `Sheaf.AlgebraicGeometry.Thickening`; its affine and over-base typeclass hypotheses are explicit there. The fibre is `Scheme.Hom.fiber` and the point on it is `f.asFiber x` from Mathlib `AlgebraicGeometry.Fiber`. The local dimension is the existing `topologicalKrullDimAt` from `WeilConjectures.Mathlib.Topology.KrullDimension`. No hypotheses or clauses are added or omitted.

Dependency declarations used: `AlgebraicGeometry.FormallySmooth` in `Sheaf.AlgebraicGeometry.FormallySmooth`; `AlgebraicGeometry.IsFirstOrderThickening` in `Sheaf.AlgebraicGeometry.Thickening`; `AlgebraicGeometry.LocallyOfFinitePresentation` in Mathlib `AlgebraicGeometry.Morphisms.FinitePresentation`; `AlgebraicGeometry.Scheme.Hom.fiber` and `Scheme.Hom.asFiber` in Mathlib `AlgebraicGeometry.Fiber`; and `topologicalKrullDimAt` in `WeilConjectures.Mathlib.Topology.KrullDimension`. The scheme conventions dependency fixes the ambient scheme/morphism meanings and introduces no additional Lean binder.

Edge cases checked: `n = 0` gives the stated étale specialization; arbitrary `x : X` covers empty and nonempty schemes without an implicit nonemptiness assumption; the fibre point is well-typed through `asFiber`; and `WithBot ℕ∞` admits the natural-number coercion.

Searches made: LeanFinder for “smooth morphism formally smooth locally finite presentation schemes” found Mathlib's `Smooth` and equivalence lemmas but no lifting-property declaration; Loogle for `AlgebraicGeometry.Smooth, SmoothOfRelativeDimension, Etale` returned no result; grep of Mathlib smooth morphism files found `AlgebraicGeometry.Smooth`, `SmoothOfRelativeDimension`, and `Etale`. Existing Mathlib `Smooth` uses the affine-local ring definition, so it is not reused as an exact statement of the node's formal-smooth definition.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, `SmoothMorphism` has precisely the two required clauses in the same order. The relative-dimension definition includes the smoothness clause and quantifies every point, using the scheme-theoretic fibre through that point and the local Krull dimension. The final definition is exactly relative dimension zero. The only naming adaptation is `SmoothMorphism`/`SmoothMorphismOfRelativeDimension`/`EtaleMorphism`, since Mathlib already occupies the shorter names; this does not change the rendered notions.


## Second reading by K1

I independently opened the node, the sandbox module, all six statement-dependency
nodes and their declarations. The worker module renders the clauses correctly,
but violates H4: it defines three notions already defined in Mathlib. A different
but equivalent presentation of the same notion does not justify a second definition.
I removed the sandbox module and changed only the item's `lean` record to
`existing: true`, recording `AlgebraicGeometry.Smooth`,
`AlgebraicGeometry.SmoothOfRelativeDimension`, and `AlgebraicGeometry.Etale`.
The Worker report above describes the superseded module; this section describes
the final delivery. No node statement correction, new node, or dependency module.

Source reading: the repository's Stacks checkout is absent on this machine. I
read the local Stacks .tex copy at `/home/ubuntu/c1-stacks-review/`, using its
`tags/tags` mapping: 02H0 = more-morphisms-definition-formally-smooth,
02H6 = more-morphisms-lemma-smooth-formally-smooth,
01V4 = morphisms-section-smooth, 02G1 =
morphisms-lemma-smooth-omega-finite-locally-free, 02G2 =
morphisms-definition-smooth-relative-dimension. The relevant sections impose no
field, characteristic, Noetherian, separatedness, quasi-compactness or surjectivity
assumption. In particular 02H6 applies to any morphism of schemes.

Objects, hypotheses and clauses, matched independently:

1. Schemes X,Y and morphism f:X→Y: Mathlib Smooth's ambient binders are
   `{X Y : Scheme.{u}} (f : X ⟶ Y)`, with arbitrary universe u. The conventions
   dependency introduces no further requirement. Verdict: same objects.
2. Smooth means locally of finite presentation AND formally smooth.
   `Smooth f` has field `smooth_appLE`, asserting smooth ring maps on every pair
   of affine opens. Stacks 02H6 proves precisely the equivalence with the node's
   conjunction, with no extra assumptions. The forward direction obtains finite
   presentation on affines and fills every affine square; the reverse restricts
   formal smoothness to affine opens, obtains formally smooth finite-presentation
   ring maps, and hence smooth ring maps. Verdict: same property; reuse mandatory.
3. The formal lifting clause quantifies affine first order thickenings T⊂T' over Y,
   then every a:T→X over Y, and asks for a lift over Y restricting to a. I opened
   `Sheaf.AlgebraicGeometry.FormallySmooth`: its `FormallySmooth f` quantifies
   `{T T'}`, i, `[IsAffine T] [IsAffine T'] [T'.Over Y]`,
   `IsFirstOrderThickening i`, a, the commuting-square equality, and then
   `∃ a', i ≫ a' = a ∧ a' ≫ f = T' ↘ Y`. This is exactly 02H0. I also opened
   `Sheaf.AlgebraicGeometry.Thickening`: the predicate is
   `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`, the node's square-zero ideal sheaf.
   These definitions are the meanings used in the 02H6 comparison, not additional
   hypotheses on f. Verdict: no quantifier, triangle, or affine restriction lost.
4. Nonnegative integer n: Mathlib's relative-dimension declaration has `(n : ℕ)`.
   Verdict: precisely all the node's n≥0, including zero.
5. At a point x, dimension means dimension of the fibre at x, not dimension of
   the local ring at x. The worker correctly used `topologicalKrullDimAt` and
   `f.asFiber x`. I opened the dimension dependency: it is the infimum of dimensions
   of open neighbourhoods. I opened `Scheme.Hom.fiber` and `asFiber`: the former
   is the pullback along `Y.fromSpecResidueField (f x)` and the latter is the
   corresponding point. The base-change dependency's report/signatures distinguish
   this scheme fibre from its module-base-change declaration. Verdict: correct
   original clause; no private or special-case fibre/dimension was used.
6. Smooth of relative dimension n means smooth AND dimension n at EVERY x.
   `SmoothOfRelativeDimension n f` requires, for every `x : X`, affine chart
   neighbourhoods with `RingHom.IsStandardSmoothOfRelativeDimension n`.
   I opened that ring predicate and `Algebra.IsStandardSmoothOfRelativeDimension`:
   they require a submersive presentation of dimension n. On such a chart the
   differentials are free of rank n. Stacks 02G1 equates their rank at x with
   dim_x of the fibre, and 02G2 defines smooth of relative dimension n by constant
   rank n. Conversely, a smooth morphism admits standard-smooth charts (the
   Stacks smooth-locally-standard-smooth lemma and Mathlib
   `Smooth.iff_forall_exists_isStandardSmooth`); restricting around x with
   differential rank n gives charts of relative dimension n. Mathlib
   `SmoothOfRelativeDimension.smooth` explicitly retains smoothness.
   Verdict: same notion, not only a global fibre dimension or a closed-point test.
   The node's explanatory pointwise notion needs no separate global predicate:
   on a smooth f it is the stated fibre-dimension equality at x.
7. Étale means smooth of relative dimension zero. `Etale f` is the affine-local
   étale-ring property in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
   The existing `Etale.iff_smoothOfRelativeDimension_zero` has exactly
   `Etale f ↔ SmoothOfRelativeDimension 0 f`. I opened its proof and the source's
   paragraph immediately after definition-etale, which states the same equivalence.
   Verdict: exact final clause, no new EtaleMorphism definition needed.

Edge cases: with empty X the pointwise chart and dimension conditions are
vacuous; it is smooth of every n, matching the nonempty-fibres wording of 02G2.
There is no requirement that every fibre be nonempty or that f be surjective.
An empty target forces the source empty. The zero ring represents the empty affine
scheme and is not excluded. n=0 is explicitly handled by the existing étale
comparison. No characteristic or field binder is introduced. `Scheme.{u}` for
arbitrary u is the same universe convention as the dependency declarations;
finite presentation indices in Type are harmless, since finite generators and
relations can always be reindexed by Fin. There is no index family in this item
requiring a nonempty or finite index set.

Independent searches (2026-10-11), with queries different from the first worker:
LeanFinder via msearch for "scheme morphism smooth fixed relative dimension etale"
returned the smooth/relative-dimension/étale declarations (some indexed names use
older Is-prefixed aliases). Loogle for `AlgebraicGeometry.SmoothOfRelativeDimension`
returned the current declaration, its field, `.smooth`, and base-change results.
LeanSearch for "smooth morphism of schemes relative dimension n standard smooth"
was attempted and reported unavailable (Internal Server Error); no verdict is
inferred from it. I searched Mathlib's Smooth/Etale files, `WeilConjectures/`, and
repository `lean/Sheaf/` for `SmoothMorphism`, `SmoothOfRelativeDimension`,
`class Smooth`, `class Etale`, and "smooth ... relative dimension". Mathlib
contains all three notions; the source project already uses SmoothOfRelativeDimension
in cohomology and zeta-function modules. The project also already reuses Etale
in its scheme conventions. I read the defining class bodies, not only their names.

H5/H6/H8/H9: the removed module contained no hollow definition and no theorem
proof; its docstrings and binders were otherwise acceptable. The final delivery
adds no Lean declaration, no proof, no sorry and no module; upstream declarations
retain their existing source documentation. The primary `lean.statement` is
verbatim `class Smooth (f : X ⟶ Y) : Prop` from Smooth.lean; its ambient binders
and the other two declaration signatures are explained above and in `lean.note`.
The `lean.declarations` entry for Etale is in the separate Etale module, explicitly
named in the note. Final verification compiles a scratch import of Etale (which
imports Smooth) and checks all three declarations and both comparison lemmas.
