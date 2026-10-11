## Worker report

The module `lean/Sheaf/AlgebraicGeometry/DescendFinite.lean` states
`AlgebraicGeometry.exists_isFinite_baseChange_stage`. It uses an inverse system
`D : Iᵒᵖ ⥤ Scheme` with affine transition maps, a cone `c` and `hc : IsLimit c`
for its limit, and an initial index `i₀`. The schemes `X₀`, `Y₀`, and `D.obj (op i₀)`
carry the quasi-compact and quasi-separated instances represented by
`CompactSpace` and `QuasiSeparatedSpace`. The maps `x₀` and `y₀` are the structure
maps to the stage base, and `h₀ : x₀ = f₀ ≫ y₀` says that `f₀` is over that base.
`[LocallyOfFiniteType f₀]` renders the locally-finite-type hypothesis.

The limit-base-change morphism in `hfinite` is the canonical
`pullback.map x₀ (c.π.app (op i₀)) y₀ (c.π.app (op i₀)) f₀ (𝟙 _) (𝟙 _)`, with the
commutativity proofs discharged by `simp [h₀]`. The conclusion is
`∃ (i : I) (hi : i₀ ≤ i), IsFinite (...)`; its morphism is the corresponding
`pullback.map` along `D.map (homOfLE hi).op`, so `hi` explicitly renders `i ≥ i₀`
and the pullbacks render the specified base changes `X_i`, `Y_i`, and `f_i`.
The finite hypothesis is `IsFinite` from Mathlib, matching the dependency's
finite morphism notion.

Dependency declarations used:

- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (Mathlib), for
  schemes and scheme morphisms (`def-pc-scheme`).
- `AlgebraicGeometry.IsAffineHom` (Mathlib, `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean`),
  for affine transition morphisms (`pqf-def-affine-morphism`).
- `AlgebraicGeometry.exists_limit_affine_transition` from
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`, for the inverse-limit cone
  and affine projections (`lem-weil-pbc-limit-affine-transition`).
- `CompactSpace` and `QuasiSeparatedSpace` (Mathlib topology instances), as
  recorded by `def-weil-pbc-scheme-conventions`.
- `CategoryTheory.Limits.pullback` and `pullback.map` from
  `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`, for fibre
  products and induced base-change maps (`def-pc-fibre-product`).
- `AlgebraicGeometry.IsFinite` from
  `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`, for finite morphisms
  (`def-weil-finite-integral-morphism`).
- `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`, for the finite-type
  hypothesis (`def-weil-finite-type-morphism`).

Searches made: `msearch.py K1 lem-weil-pbc-descend-finite leanfinder` for
"finite morphism descends along inverse limit affine transitions" (no existing
project declaration); `msearch.py ... loogle` for
`IsFinite, IsAffineHom, LocallyOfFiniteType, pullback.map` (only the Mathlib
notions); `msearch.py ... grep` and `rg` over Mathlib and
`WeilConjectures/` for descend-finite/01ZO (no matching theorem). I also searched
`lean/Sheaf` for `descend.*finite`, `exists.*finite`, and inverse-limit pullback
statements; no existing statement of this node was found.

Edge cases checked: `I` is only required to be a directed preorder and remains
nonempty; the conclusion retains the explicit lower-bound witness `hi`, so it
includes the case `i = i₀`. No nonempty or finite cover is imposed on the schemes
beyond the node's quasi-compact/quasi-separated hypotheses, and no characteristic
or field assumption is introduced. The pullback formulation permits zero or empty
schemes and arbitrary universe `u`.

## Earlier second reading (a previous round; superseded)

I reread the node and the generated signature clause by clause. The directed index,
base stage, inverse-system cone, affine transitions, and the three qcqs schemes are
all explicit binders. The equations `h₀` and the two `pullback.map` constructions
render the structure maps, fibre products, and induced morphisms; `LocallyOfFiniteType`
and `IsFinite` render the two morphism hypotheses and the finite conclusion. The
existential conclusion retains both the stage and its `i₀ ≤ i` witness. The module
compiles on the server with only the expected `sorry` proof warning (and no linter
warnings). No statement correction or extra dependency module was needed.

## Second reading by K1

Read the sandbox node and module against the server's actual
`literature/stacks-project/limits.tex`, lines 1739–1796 (the local literature
checkout has no copy), including Situation 081D and Lemma 01ZO. The official
pages https://stacks.math.columbia.edu/tag/081D and
https://stacks.math.columbia.edu/tag/01ZO confirm the same assumptions. No
statement correction is present or necessary, and there are no new nodes or
dependency modules in this delivery.

Object/hypothesis/conclusion inventory and correspondence (H3):

1. A directed index set I: `{I : Type u} [Preorder I]
   [IsDirected I (· ≤ ·)]`. Correct, including non-antisymmetric directed
   preorders as required by the standing convention. Removed the redundant
   `[Nonempty I]` binder: the explicit `i₀ : I` already supplies an element.
   It excluded no mathematical case but needlessly requested an instance.
2. An inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Correct;
   functoriality supplies identity and composition of transitions.
3. Every transition affine: the dependent instance binder
   `[∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]`. Correct;
   `homOfLE hi` goes from i₀ to i and its opposite goes from op i to op i₀.
4. Its limit S and projections: `c : Cone D`, `hc : IsLimit c`, S = c.pt,
   and `c.π.app (op i₀)`. Correct for any chosen limit, without imposing
   additional affine-projection hypotheses. Opened the dependency module
   `Sheaf.AlgebraicGeometry.LimitAffineTransition` and read
   `AlgebraicGeometry.exists_limit_affine_transition`: its directed-preorder
   system and affine transitions are precisely these, and its cone uses
   these projections. No substitute inverse-limit definition is introduced.
5. The initial index 0: `i₀ : I`. Correct; 0 is a designated index, not a
   least element or a natural number.
6. X₀, Y₀ and S₀ quasi-compact and quasi-separated: `{X₀ Y₀ : Scheme.{u}}`
   and the six `CompactSpace`/`QuasiSeparatedSpace` instances, the last pair
   on `D.obj (op i₀)`. Correct; no such assumptions are imposed on every
   Sᵢ, and no separatedness, Noetherianity, or finite presentation is added.
7. A morphism over S₀: `x₀`, `y₀`, `f₀`, and
   `h₀ : x₀ = f₀ ≫ y₀`. Correct, with exactly the commutative triangle.
8. X, Y and f obtained by base change to S: the source/target of the
   `pullback.map` in `hfinite` are `pullback x₀ (c.π.app (op i₀))` and
   `pullback y₀ (c.π.app (op i₀))`. Its components are f₀, identity on S,
   identity on S₀. Correct: opened `pullback.map` in HasPullback.lean and
   checked all three map arguments and both commutativity proofs.
9. f finite: `hfinite : IsFinite (...)`. Correct: opened Finite.lean;
   `IsFinite` extends `IsAffineHom` and requires finite induced ring maps
   on every affine open, exactly def-weil-finite-integral-morphism.
10. f₀ locally of finite type: `[LocallyOfFiniteType f₀]`. Correct: opened
    FiniteType.lean; its all-affine-pairs condition matches the recorded
    dependency via the affine-local equivalence, with no finite-presentation
    assumption. The instance binder represents a proposition hypothesis.
11. Conclusion, an index at or above 0 with finite base change:
    `∃ (i : I) (hi : i₀ ≤ i), IsFinite (pullback.map ... )` along
    `D.map (homOfLE hi).op`. Correct; the two pullback objects are exactly
    Xᵢ and Yᵢ, and the map has components f₀, identity on Sᵢ and identity
    on S₀. Both existential witnesses precede finiteness, with no uniform
    index claimed across differing input morphisms.

Read each stmt_dep node, its recorded lean/mathlib_match, and the used
source signatures. `def-pc-scheme` uses Mathlib Scheme and Scheme.Hom;
`pqf-def-affine-morphism` uses IsAffineHom's affine-open inverse-image
condition; `def-pc-fibre-product` uses pullback and pullback.map;
`def-weil-pbc-scheme-conventions` is explicitly a convention, not a new
predicate. The quasi-separated-space/diagonal equivalence in
Morphisms/QuasiSeparated.lean confirms the scheme interpretation. All
used dependencies are usable as recorded; there are no private copies.

Edge cases: an empty I cannot carry the source's distinguished 0, and
Lean excludes it for exactly that reason (`i₀ : I`). A singleton index and
`i = i₀` are permitted. Empty schemes and spectra of the zero ring are
permitted; in the proof's empty-cover case choose a stage at least the
already selected k. There is no natural-number parameter, characteristic,
field, nontrivial-ring, or nonempty-scheme hypothesis. Universe u is
arbitrary; any set-sized diagram and its schemes can be accommodated in
one common universe, as in the dependency's signature. No quantified
test universe is used, and every variable/universe is explicitly bound.

Independent searches, with queries distinct from the worker's:

- msearch leanfinder: `finite scheme morphism at a directed inverse limit
  descends to some index` gave eight hits, chiefly affine-transition-limit
  equality-descent lemmas and basic finiteness notions. None states this
  finiteness-at-a-stage result; inspected AffineTransitionLimit.lean too.
- msearch loogle: `IsFinite, pullback` returned no hits and reported an
  unknown unqualified identifier, so it supplies no absence evidence.
- msearch leansearch: `A morphism locally of finite type whose base change
  to a directed inverse limit is finite is finite at some stage` returned
  service unavailable (Internal Server Error), recorded as unavailable.
- msearch grep in AlgebraicGeometry:
  `IsFinite.*(limit|stage)|finite.*inverse.*limit|01ZO` gave three basic
  finite pullback/coproduct instances, no exact statement.
- rg over Mathlib AlgebraicGeometry, upstream WeilConjectures, and project
  lean/Sheaf for `descend.*finite|finite.*descend|01ZO` and the full
  declaration name found other descent statements (fpqc, closed immersion,
  local constancy, algebra descent) and citers, no duplicate of this lemma.
  Checked the related compactification and affine-transition-limit sources;
  their finite-presentation and equality assertions are different.

Repairs: removed only the redundant Nonempty index instance from the
signature and synchronized lean.statement verbatim. Expanded the proof
docstring's six compressed steps to the node's eight steps, including
base-change tensor-product identifications, transported generators,
persistence to larger indices, and the empty finite-cover case. The
only proof remains `sorry`; no definitions, instances, or mathematical
proofs were added. Header, namespace, source/blueprint docstrings and
100-character line limit were checked. Clean single-file compilation and
the delivery dry run are required below before push.

Validation: scompile.py compiled the revised 70-line module in 1.7 seconds,
exit code 0, with no warnings. deliver2.py --no-push printed OK: the
preflight passed and the module compiled. The recorded signature equals
the file verbatim up to the proof's `:=`.
