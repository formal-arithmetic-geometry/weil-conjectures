## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent` states
`AlgebraicGeometry.isIntegralHom_of_fpqcPrecoverage_pullback`, with `sorry` as its
only proof. It states the descent direction of Stacks Project, Descent,
Lemma 35.23.24, Tag 02L9. No definitions, extra nodes, dependency modules or
statement corrections are needed. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- The schemes X and S and the morphism f:X → S are `{X S : Scheme.{u}}`
  and `(f : X ⟶ S)`.
- The index set I is `{I : Type v}`. It is arbitrary, including empty, finite
  and infinite sets; its universe is independent of the schemes' universe.
- The schemes S_i and maps g_i:S_i → S are `(S' : I → Scheme.{u})` and
  `(g : ∀ i, S' i ⟶ S)`.
- The fpqc covering hypothesis is
  `hcover : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`. This uses the
  dependency's recorded Mathlib definition, not a topology-covering sieve.
  Its flatness and quasi-compact covering conditions express the node's
  finite-affine-open-image condition. Mathlib's
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` gives finite affine
  opens with exactly the required union of images over an affine open.
  Conversely, the node's affine opens are compact and open, giving
  `IsCompactOpenCovered`; covering all affine opens also gives joint
  surjectivity. The node does not require each g_i itself to be quasi-compact,
  and neither does this hypothesis.
- The fibre product X ×_S S_i is `pullback f (g i)`. Its second projection,
  with target S_i, is `pullback.snd f (g i)`; no arbitrary comparison squares
  or extra hypotheses were introduced.
- Every f_i integral is `hintegral : ∀ i, IsIntegralHom (pullback.snd f (g i))`.
  Mathlib's class gives affineness and integrality of the ring maps on each
  affine open, exactly the integral clause of the dependency node.
- The conclusion f integral is `IsIntegralHom f`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`. The category notation is its Hom.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc` (direct import).
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; scheme
  pullbacks are supplied transitively by the algebraic geometry imports.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsIntegralHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Integral` (direct import). The node
  also records `IsFinite`, whose signature was read; its finite clause is
  not used in this item.

The theorem docstring records all four proof steps: integral gives affine
and universally closed (01WM, pqf-lem-integral-univclosed); descend universal
closedness (02KS, lem-weil-pbc-fpqc-descend-universally-closed); descend
 affineness (02L5, lem-weil-pbc-fpqc-descend-affine); apply 01WM backwards.
The proof dependencies need no imports at stage 2 because none is used in
elaboration of the statement.

Edge cases checked before writing: an empty index family is an fpqc covering
only when the base is empty, in which case X is empty too and f is integral.
An empty source over any base is integral, and all its pullbacks are empty.
Repeated arrows or empty components do not affect the covering predicate.
An identity covering reduces to integrality of a pullback isomorphic to f.
No nonemptiness, finiteness of I, Noetherian, separatedness, finite type or
characteristic assumption is added. Arbitrary universes u and v are declared
and all variables are explicitly bound; no testing universe can make a
universal test-scheme hypothesis vacuous because there is no such hypothesis.

Searches (msearch.py, group H1, this item):

- Lean Finder: `Integral morphisms of schemes descend along fpqc covering families`:
  eight hits, including integral coproducts, composition and base-change
  properties in Integral.lean, but no exact descent-family declaration.
- Loogle: `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.Scheme.fpqcPrecoverage`:
  zero hits.
- Mathlib grep: `IsIntegralHom.*(fpqc|escend)|isIntegralHom_of|02L9` under
  AlgebraicGeometry: zero hits. Additional local reads of Descent.lean and
  FlatDescent.lean found no integral-descent declaration.
- LeanSearch: `integral morphism descends under fpqc covering of schemes`:
  unavailable, Internal Server Error; no search verdict assigned to the
  unavailable service.
- `rg` over WeilConjectures and lean/Sheaf for fpqc/descent/integrality and
  the exact node id: no exact statement or name clash. The source's
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` has the generic
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`, whose full signature
  was read. It assumes a morphism property with Zariski locality,
  faithfully-flat-quasi-compact descent and base-change stability and takes
  a covering sieve with arbitrary pullback squares; it does not directly
  supply this node's unconditional integrality-descent statement.
- Read Scheme.lean, Integral.lean, Finite.lean, Fpqc.lean,
  Cover/QuasiCompact.lean and the recorded pullback module to verify the
  dependency definitions and signatures rather than relying on names.

The local Stacks checkout is absent on this machine. The source was read
at https://stacks.math.columbia.edu/tag/02L9, which confirms the same route:
01WM plus 02KS and 02L5. No statement fault or disputed claim was found.

Server validation: scompile.py compiled the 40-line module in 1.7 seconds,
exit code 0, with no compiler warnings or errors. Delivery dry run follows;
the independent second reader will supply its own report section.

## Second reading by H1

I independently read the base node, sandbox node and Lean file, all four
statement-dependency nodes, and their recorded declarations. Verdict: the Lean
states exactly the node's descent direction; no hypothesis or conclusion needs
repair. No new definition nodes, dependency modules, or statement correction
are present or needed. The Lean module and node record are left unchanged.

Object/hypothesis/conclusion checklist (H3):

- Arbitrary schemes X and S: `{X S : Scheme.{u}}`; these are Mathlib's
  schemes (Scheme.lean, structure extending LocallyRingedSpace), as
  def-pc-scheme records. Pass.
- The morphism f:X -> S: `(f : X ⟶ S)`, the scheme category Hom. Pass.
- Arbitrary index set I: `{I : Type v}`, with no Finite or Nonempty binder.
  Pass.
- Schemes S_i and arrows g_i:S_i -> S: `(S' : I → Scheme.{u})` and
  `(g : ∀ i, S' i ⟶ S)`. Pass.
- The family is an fpqc covering:
  `(hcover : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`.
  I opened Fpqc.lean, Sites/QuasiCompact.lean, Sites/MorphismProperty.lean,
  Cover/QuasiCompact.lean and Topology/Sets/CompactOpenCovered.lean.
  `fpqcPrecoverage` is `qcPrecoverage ⊓ Scheme.precoverage @Flat`.
  Thus the arrows are flat and jointly surjective, with the finite
  compact-open-image condition for every affine open of S.
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` replaces those
  compact opens by finitely many affine opens, permitting repeated indices.
  Conversely finitely many affine opens can be grouped by index into compact
  opens. Joint surjectivity follows from the node's affine-open condition.
  This is def-weil-pbc-fpqc-covering, without requiring each g_i to be
  quasi-compact. Pass.
- X times_S S_i and its second projection f_i: the chosen `pullback f (g i)`
  is supplied by Mathlib's `HasPullbacks Scheme`; `pullback.snd f (g i)`
  has domain that pullback and codomain S' i. I read the recorded pullback
  and projection signatures and the scheme pullback instance. These are
  def-pc-fibre-product, with no arbitrary-square assumption. Pass.
- Every f_i is integral:
  `(hintegral : ∀ i, IsIntegralHom (pullback.snd f (g i)))`.
  Integral.lean's `IsIntegralHom` extends `IsAffineHom` and requires
  `(f.app U).hom.IsIntegral` for every affine open U. This is precisely the
  integral clause of def-weil-finite-integral-morphism, not its finite clause.
  Pass.
- Conclusion f is integral: `IsIntegralHom f`, the same predicate and no
  additional conclusion. The quantifiers introduce the whole family before
  requiring each second projection to be integral. Pass.

Source check: the local Stacks .tex checkout is absent. I read the actual
`descent.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex
at `lemma-descending-property-integral` and
`definition-property-morphisms-local`, and checked Tags
[02L9](https://stacks.math.columbia.edu/tag/02L9),
[02KO](https://stacks.math.columbia.edu/tag/02KO) and
[022B](https://stacks.math.columbia.edu/tag/022B).
02KO's reverse implication is exactly this item (the order of factors is
immaterial, with the projection to the covering scheme fixed). Integrality
imposes no fixed ground field, characteristic, Noetherian or finiteness
assumption throughout this source. A separate ambient base in 02KO imposes
no restriction here: schemes and arrows can all be viewed over the terminal
scheme. The four docstring proof steps reproduce the 02L9 proof: 01WM
forwards, 02KS, 02L5, then 01WM backwards.

Edge cases: if I is empty, the covering condition forces S empty; the map
f then forces X empty, and integrality holds. An empty source over an arbitrary
base is integral (the empty scheme is affine, and maps to the zero ring are
integral). Empty covering components, repeated arrows, infinite I, and the
n = 0 finite subcover of the empty affine open are all allowed. There is no
characteristic restriction or exclusion of the zero ring. Universes u and v
are explicit and independent; schemes of any sizes can be placed in a common
universe u. No universal test-scheme hypothesis uses a smaller universe.
There are no unbound variables or hidden geometric instances beyond the
standard scheme-category pullback instance.

Independent H4 searches, using different wording from the first reader:

- `msearch.py ... leanfinder "Integral scheme morphism follows from integral
  second projections over a flat quasi compact cover"`: eight hits, including
  integral base-change, coproduct, composition and universal-closedness
  declarations; none states descent along a family.
- `msearch.py ... loogle "AlgebraicGeometry.IsIntegralHom"`: twelve hits;
  I checked the returned signatures. None states this descent theorem.
- `msearch.py ... grep "02L9|isIntegralHom_of|IsIntegralHom.*[Dd]escend"`:
  zero hits.
- Direct `rg` for `IsIntegralHom`, `02L9`, `integral.*local` and
  `integral.*descent` in WeilConjectures, lean/Sheaf and Mathlib's
  Descent/FlatDescent/LocalFlatDescent/Integral modules: no exact existing
  statement and no name clash. I opened the source's
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`: it requires general
  property descent and locality instances and a covering sieve, rather than
  stating unconditional integrality descent along this covering family.
  It is a possible stage-3 tool, not an existing exact statement of this node.

H5-H9: there are no definitions, hollow data or private copies. The only
proof is the required named theorem's `sorry`. The source/blueprint docstrings,
namespace, imports, header and line widths conform. Both imports are needed
for the signature. The node's `lean.statement` was programmatically checked
verbatim against the signature before `:= by`: equal.

Mismatches found: none. Changes made: only this independent second-reading
report; the correct Lean and node were preserved. Validation:
`scompile.py H1 lem-weil-pbc-fpqc-descend-integral
lean/Sheaf/AlgebraicGeometry/Morphisms/FpqcIntegralDescent.lean` returned
exit code 0 (1.7 seconds), with no errors or warnings.
