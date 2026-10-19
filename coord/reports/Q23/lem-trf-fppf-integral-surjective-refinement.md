## Worker report

Repaired the returned stage-2 delivery of
`lem-trf-fppf-integral-surjective-refinement` (returned immutable head
`be32733b814f`). The retained sandbox contained only dispatcher marker files,
with no Lean module, node copy, or report. The current shared node likewise has
no `lean` record. This delivery supplies the missing artifacts rather than
rebasing or repushing the empty delivery.

The module `Sheaf.AlgebraicGeometry.FppfIntegralSurjectiveRefinement` states
`AlgebraicGeometry.exists_integral_surjective_fppf_refinement`. Its sole proof
is `by sorry`; it adds no definitions or auxiliary theorems. The module and
declaration docstrings cite Stacks Project, More on Morphisms, Tag 0CNZ,
`lemma-dominate-fppf-integral`, and the node id. The declaration docstring gives
all five DAG proof steps, including their cited prerequisite nodes. I read
`more-morphisms.tex` at the exact lemma and its proof (lines 13725–13754): the
source has no quasi-compactness or quasi-separatedness hypothesis.

The item's natural-language statement, source, statement dependencies, proof,
proof dependencies, and all other existing fields are unchanged. Only `lean`
is added, with the complete module, declaration, file, signature, branch,
author, UTC date, and `existing: false` fields. The signature is copied verbatim
from the theorem keyword up to `:=`. The JSON uses one-space indentation,
Unicode text, and a final newline. No new nodes or dependency modules are needed.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering and reading |
| --- | --- |
| Let `X` be a scheme | `{X : Scheme.{u}}`; this is an arbitrary scheme, with no geometric property assumed. |
| Size convention and a small index set | `universe u`, `{I : Type u}`, and `Xi : I → Scheme.{u}` put the family in the chosen small universe. The conclusion uses `Y : Scheme.{u}` and `A : Type u` in the same bound. The theorem is polymorphic in `u`; no countability or finiteness is imposed. |
| The family of scheme morphisms `f_i : X_i → X` | `(f : (i : I) → Xi i ⟶ X)`. |
| Every `f_i` is flat | `[hflat : ∀ i, Flat (f i)]`. |
| Every `f_i` is locally of finite presentation | `[hlfp : ∀ i, LocallyOfFinitePresentation (f i)]`. |
| The family is jointly surjective | `(hjoint : ∀ x : X, ∃ i y, f i y = x)`. Every point of `X` is in some member's image. Together with the preceding two hypotheses, these are exactly the fppf covering conditions. |
| There exist `Y` and `q : Y → X` | `∃ (Y : Scheme.{u}) (q : Y ⟶ X), …`. |
| `q` is integral | `IsIntegralHom q`; this includes affineness and integrality on every affine open. |
| `q` is surjective | `Surjective q`; this is surjectivity on underlying points. |
| A small open covering `Y = ⋃ W_α` | `∃ (A : Type u) (W : A → Scheme.{u}) (j : (a : A) → W a ⟶ Y), …`, with `(∀ a, IsOpenImmersion (j a))` and `(∀ y : Y, ∃ a w, j a w = y)`. An open immersion identifies `W a` with its open image in `Y`; joint surjectivity says these images cover. Thus these are the open subschemes in the node, represented by their canonical kind of inclusion. |
| An index `i(α)` for every open | The existential binder `(i : A → I)` supplies the indices together, including when `A` is empty. |
| Morphisms `h_α : W_α → X_{i(α)}` | The existential binder `(h : (a : A) → W a ⟶ Xi (i a))`. |
| The lifts are over `X`: `f_{i(α)} ∘ h_α = q` restricted to `W_α` | `(∀ a, h a ≫ f (i a) = j a ≫ q)`. Lean composition is left to right, and `j a ≫ q` is exactly restriction along the open inclusion. |
| No quasi-compactness or quasi-separatedness assumption on `X` | No corresponding binders or instances occur. |
| No finiteness or finite-presentation assertion about `q` | The properties asserted for `q` are precisely `IsIntegralHom q ∧ Surjective q`. |
| Empty scheme and empty covering permitted | No `Nonempty`, `Inhabited`, `Finite`, or `Fintype` binder appears for either index type or any scheme. |

Dependency declarations were read at their recorded source locations:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` in
  `Mathlib.AlgebraicGeometry.Scheme` (lines 35–47 and 73–76). The scheme's
  locally affine structure and the locally ringed space morphisms are used
  directly.
- `def-weil-size-convention`: its record is a metatheoretic convention with
  no declaration or module; explicit universe polymorphism implements it.
- `def-pc-fppf-site`: `Scheme.fppfPrecoverage` and `Scheme.fppfTopology` in
  `Mathlib.AlgebraicGeometry.Sites.Fpqc` (lines 38–54), and
  `Scheme.overGrothendieckTopology` in `Mathlib.AlgebraicGeometry.Sites.Small`
  (lines 103–107). I also read `Scheme.precoverage` and
  `Scheme.ofArrows_mem_precoverage_iff` in
  `Mathlib.AlgebraicGeometry.Sites.MorphismProperty` (lines 82–94).
  These identify membership with exactly joint surjectivity and the morphism
  properties. The family is supplied explicitly by those three conditions,
  without defining a second fppf covering predicate. The over-site is not
  otherwise needed for this assertion about a family over `X`. Flatness and
  local finite presentation are Mathlib's `AlgebraicGeometry.Flat` and
  `AlgebraicGeometry.LocallyOfFinitePresentation`, read with their docstrings
  in `Morphisms.Flat` (lines 37–45) and `Morphisms.FinitePresentation`
  (lines 42–48).
- `def-weil-finite-integral-morphism`: the recorded integral declaration
  `AlgebraicGeometry.IsIntegralHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral` (lines 32–37). The node's
  finite-morphism notion is not used by this theorem.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (lines 56–60).
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion` (lines 34–39), with the associated
  open-image interpretation read at `isOpen_range`, `Scheme.Hom.opensRange`,
  and `Scheme.Hom.mem_opensRange` (lines 69–87).

All four public imports supply those statement notions. The Mathlib instances
for composition of integral and surjective morphisms are present in the
corresponding imported modules. The other five non-Mathlib proof prerequisite
nodes have no `lean` or `mathlib_match` on the inspected base, so there are no
recorded modules for them to import yet. They are named in the proof docstring;
their proofs or statements are not needed to type this theorem. I did not
create statements of unrelated proof prerequisites.

Edge cases checked before writing:

- If `I` is empty, `hjoint` forces `X` to have no points. Taking `Y = X`,
  `q` its identity, and the empty family of opens satisfies the conclusion:
  the index function from the empty family to `I` exists and the lift and
  covering conditions are vacuous. Nothing requires an index in an empty
  family.
- For an empty scheme with any covering family, the same empty open family
  works. All quantification over points is vacuous; integral and surjective
  identity morphisms include the empty case.
- For a nonempty base, the output cover cannot accidentally be empty: its
  joint-surjectivity clause and `Surjective q` force a member over every base
  point. This is a consequence, not an added hypothesis.
- Infinite index types are allowed, and no affine, separated, quasi-separated,
  quasi-compact, Noetherian, or characteristic condition on `X` is introduced.
- The identity singleton covering has the expected identity refinement, so
  the direction of the local factorization equation agrees with the source.

Searches actually run during this repair (all services returned successful results):

- `msearch.py … leanfinder`, query `An arbitrary small fppf covering of any
  scheme admits an integral surjection with an open cover whose members lift
  over the base to the covering family`: eight hits for joint surjectivity,
  precoverages, cover objects, and coproduct surjectivity. None constructs the
  required integral refinement. An earlier semantic phrasing likewise gave
  only precoverage and jointly surjective cover interfaces.
- `msearch.py … loogle`, query
  `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.Surjective`: zero hits.
- `msearch.py … grep`, query
  `fppf.*(integral|refin)|integral.*fppf|dominate.*fppf`, subdirectory
  `AlgebraicGeometry`: zero hits.
- `msearch.py … leansearch`, query `A jointly surjective family of flat
  locally finitely presented scheme morphisms admits an integral surjective
  refinement with open local lifts`: eight hits for joint surjectivity,
  open-immersion lifts, flatness, and construction of a cover from explicit
  conditions. None states the item.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`, query
  `fppf.*(integral|refin)|integral.*fppf|dominate.*fppf`: the project has finite
  and affine refinement theorems. The upstream hits concern fppf sites or
  integral base change. I read the finite-refinement module: its base is
  required to be quasi-compact and quasi-separated and its conclusion differs,
  so it does not state this arbitrary-base theorem.
- `rg` in `dag/lean_names_upstream.json`, upstream, and project sources, query
  the item id, `exists_integral_surjective_fppf_refinement`, and
  `FppfIntegralSurjectiveRefinement`: no existing declaration for this item.
- `grep -rn` in upstream `WeilConjectures`, query
  `lem-trf-fppf-integral-surjective-refinement`: no matches.
- `rg` across Mathlib, upstream, and project sources, query
  `exists_integral_surjective_fppf_refinement`: no name collision.
- `scompile.py --source Sheaf.AlgebraicGeometry.FppfIntegralSurjectiveRefinement`:
  module source unavailable. This was a lookup for a potentially newer
  declaration, not a failed compilation of the delivered module.

No node fault or `STATEMENT-DISPUTED` remains. No statement correction was made.

Compilation evidence: the required command

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q23 lem-trf-fppf-integral-surjective-refinement /home/ubuntu/weil-newtargets-stage2-sandbox/Q23/lem-trf-fppf-integral-surjective-refinement/lean/Sheaf/AlgebraicGeometry/FppfIntegralSurjectiveRefinement.lean
```

exited 0. It compiled the sandbox copy `Sheaf/Stage2/Sandbox0.lean` in 2.2 s
and the actual module path
`Sheaf/AlgebraicGeometry/FppfIntegralSurjectiveRefinement.lean` in 2.0 s.
Both passes had no errors and no warnings. No direct Lean/Lake command or
global build was run. Every theorem proof is the expected `sorry`.

## Second reading by Q23

This is the author's second reading with the current node, source lemma, and
new Lean file open; it is not represented as an independent agent review.
The maintainer performs the independent review under the direct-delivery brief.

For the returned H2, I checked the node's `lean.declaration` against the actual
full declaration name, its module against the file path, and its recorded
signature against the entire binder and conclusion text up to `:=`. The new
module and complete record are now both present. Only the `lean` field differs
from the current shared node.

For H1/H11, the report now has both required sections. Reading each clause
again: `{X : Scheme.{u}}` is arbitrary; the family is `Xi` and `f`; `hflat`
and `hlfp` quantify over every input member; `hjoint` quantifies over every
point of `X`; the existential `Y, q` has integral and surjective properties;
the existential `A, W, j` gives open subschemes whose images cover all of `Y`;
the existential function `i` chooses one original member for every open;
the dependent morphism family `h` has precisely those targets; and the final
equality states that both composites to `X` agree. The pointwise coverage
clause does not assert that each inclusion is surjective. The integral and
surjective properties belong to `q`, not to the maps `j` or `h`.

I separately checked the final two sentences of the node: the theorem has
no extra property binder on `X`, asserts no finiteness or finite presentation
of `q`, and has no nonemptiness binder on either index set or any scheme.
In the empty-input case `hjoint` forces an empty base and allows an empty
output family, so the index function `A → I` does not exclude that case.
The use of an open immersion to represent an open subscheme is exactly the
recorded `def-weil-open-immersion`, not a new covering notion. The explicit
covering hypotheses coincide with the recorded fppf precoverage definition.
No mathematical mismatch was found, and no node statement or dependency
needed changing. The substantive repair is the added theorem, its source
and five-step proof docstring, its complete binding, this clause reading,
and clean per-file compilation evidence.
