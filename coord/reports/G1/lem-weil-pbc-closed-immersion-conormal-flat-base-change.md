## Worker report

The module defines `AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_flat_base_change`.
It binds schemes `X Z X' Z'`, closed immersions `i` and `i'`, morphisms `g` and `f`, and the
commutativity equation `h`. The cartesian-square clause is rendered by
`hc : IsLimit (PullbackCone.mk i f h)`. The conormal map has the tensor-pullback type
`(tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
(tensorPullback i).obj i.ker.toModules`. Its canonical characterization is the equality to the
unique map selected from `closedImmersion_conormal_functorial`; the conclusion is `Epi c` and,
under `Flat g`, `IsIso c`.

Dependency used: `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`, declaration
`AlgebraicGeometry.Scheme.Modules.closedImmersion_conormal_functorial`. Mathlib leaves used in
the statement are `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.Flat`, and
`CategoryTheory.Limits.IsLimit`/`PullbackCone`.

Edge cases checked: no nonempty or finiteness assumptions are introduced; the flat implication
is conditional and the cartesian square is represented by the universal pullback cone.

Searches made: `msearch.py leanfinder "conormal sheaf under flat base change"` (no exact scheme
statement); `msearch.py loogle "Ideal.Cotangent Module.Flat"` (ring-level cotangent base-change
lemmas only); `msearch.py grep "conormal" Mathlib/AlgebraicGeometry` (no conormal sheaf); and
`rg -n "conormal.*base|closedImmersion_conormal_flat_base_change"` in the project (only the
functorial dependency).

## Earlier second reading (a previous round; superseded)

The node hypotheses and conclusion were checked against the theorem signature: the square uses the stated pullback universal property, and the exact canonical-map selection from the functorial dependency is present. No extra hypotheses or cases were added.

## Second reading by G1

Read the sandbox node, the full Lean declaration, the dependency node and its landed
module, and Stacks Morphisms `lemma-conormal-functorial-flat` (0473), together with
`lemma-conormal-functorial` (01R4), `lemma-affine-conormal` (01R3), and Schemes
`lemma-fibre-product-immersion` (01JU). The Stacks text was available locally in
`/home/ubuntu/c1-stacks-review/morphisms.tex` and `schemes.tex`; the repository's
literature source directory is absent. The source assumes arbitrary schemes and
immersions; this node explicitly specializes to closed immersions, without any
Noetherian, finite presentation, separatedness, or characteristic hypotheses.

Object/hypothesis/conclusion inventory and matching:

- Four schemes Z, X, Z', X': `{X Z X' Z' : Scheme.{uc}}`. Exact; an arbitrary
  universe is bound explicitly, and any finite collection of schemes fits a common
  universe. No affine restriction is made in the theorem.
- Closed immersions i: Z to X and i': Z' to X': morphism binders and
  `[IsClosedImmersion i] [IsClosedImmersion i']`. Exact. Read the Mathlib class:
  closed embedding plus surjective stalk maps, matching def-weil-closed-immersion.
- Ambient map g and subscheme map f: `(g : X ⟶ X') (f : Z ⟶ Z')`. Exact.
- Commutativity: `(h : i ≫ g = f ≫ i')`. Exact orientation in composition notation.
- Ideal sheaves and conormals: `i.ker.toModules`, `i'.ker.toModules`, and their
  `tensorPullback` along i and i'. Read Scheme.Hom.ker/ker_apply, the upstream
  IdealSheaf.Module definition of toModules as a genuine kernel, the project's
  TensorPullback definition, and affine_conormal_sections. These are the recorded
  ideal sheaves and tensor module pullbacks, with affine sections I/I²; exact.
- Canonical c: the displayed morphism binder has source `f* (i'* I')` and target
  `i* I`. `hcanonical` equates it with the chosen unique c from
  closedImmersion_conormal_functorial. Read that full signature: its chosen gamma
  is fixed on ideal sections, and its unique c satisfies the pullback-adjunction
  equation and affine quotient-map characterization. Taking choose_spec of its
  existential gamma and then `.2` extracts precisely this unique c. This hypothesis
  identifies the named canonical map; it does not posit an arbitrary map or add
  a mathematical assumption. Exact.
- Cartesian square: `hc : IsLimit (PullbackCone.mk i f h)`. Read PullbackCone.mk:
  the cone has vertex Z, projections i and f, over g and i'; IsLimit is exactly
  the universal property in def-pc-fibre-product. Exact, including non-chosen
  realizations of the fibre product.
- Surjectivity of c: `Epi c` in the module-sheaf category, the categorical form
  of a surjective sheaf map (local/stalk surjectivity). Exact; no requirement of
  surjectivity on sections over every open is imposed.
- Additional flat case: `(Flat g → IsIso c)` in the conjunction with Epi c.
  Read Flat and iff_flat_stalkMap: the predicate is the recorded stalkwise flatness,
  with no stronger assumption. IsIso is an isomorphism of O_Z-module sheaves.
  Exact, and flatness is only conditional, leaving the nonflat surjectivity clause.
- The parenthetical affine calculation is the local description/proof of these
  clauses, not an independently quantified second ring theorem; it is recorded
  in the expanded docstring and delegated to the existing ring-result node.

Edge cases: empty schemes and zero conormals (including identity immersions,
zero ideals and the unit ideal) are admitted by all binders. No nonempty,
nontrivial-ring, positive-dimensional, finiteness, regularity or characteristic
condition occurs. There is no index set or n parameter. All universes and variables
are explicitly bound; no small-test-universe hypothesis appears. The order is
arbitrary schemes and square, then its canonical map, then the two conclusions.

Independent searches used different wording: LeanFinder via msearch.py,
`closed subscheme ideal sheaf cotangent epimorphism cartesian square`, returned
closed-immersion quotient/lifting and ring-cotangent maps, no exact scheme theorem.
Loogle `"tensorCotangentHom"` returned Ideal.tensorCotangentHom, its surjectivity,
injectivity under flatness and pure-tensor formula; opened CotangentBaseChange.lean:
these are ring results, not this module-sheaf statement. LeanSearch via msearch.py,
`conormal sheaf pullback cartesian closed immersion flat isomorphism`, was unavailable
(Internal Server Error); no verdict assigned to the unavailable service. Direct rg
for `conormal` and `cotangent.*base.?change` in Mathlib AlgebraicGeometry, upstream
WeilConjectures and the project's lean/Sheaf found no duplicate of this theorem.
The project has the functorial and affine conormal dependencies and a diagonal
conormal specialization; these are different statements. The exact declaration
name is also absent from dag/lean_names_upstream.json. No new definition node or
dependency module is needed; no statement correction was made.

Mismatch found: H8, the theorem docstring lacked its source place and compressed
three node proof steps into a single sentence. Expanded it with Stacks 0473/01JU
and all three steps, including the affine charts, extended ideal, ring calculation,
quasi-coherence, cokernel and locality arguments, with the cited node ids. The
signature, imports, canonical-map selection and node lean.statement were correct
and are unchanged. No definitions or proofs were added; the sole theorem retains
`by sorry`. Initial server compilation was clean. Final compilation and delivery
preflight are recorded below.

Validation: final scompile.py completed with exit code 0, no warnings, in 2.2 s.
The deliver2.py --no-push dry run printed OK: preflight passed and compilation
passed (candidate 63475872d). The recorded lean.statement is unchanged and matches
the unchanged declaration signature verbatim under the project signature reader.
