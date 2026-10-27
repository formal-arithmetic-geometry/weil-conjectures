## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeAmpleExistence` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_finiteLocallyFree_surjective`.
Its proof is exactly `by sorry`. It introduces no definitions or additional nodes.
The node is unchanged except for its `lean` record.

Source checked directly: `literature/stacks-project/divisors.tex`,
`proposition-push-down-ample`, Tag 0BD4, case (1), and `lemma-norm-ample`, Tag 0BD0.
The source assumes precisely finite surjective and finite locally free in case (1).
The declaration docstring records all six DAG proof steps, including assembling the
norm family on the open and closed degree pieces before constructing the norm line.

Hypothesis and conclusion correspondence:

- Schemes and the named morphism `f : Y → X` are `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  The universe `u` is explicitly declared and arbitrary.
- Surjectivity is `[Surjective f]`, the Mathlib class asserting surjectivity on points.
- Finite locally free is `[f.IsFiniteLocallyFree]`, the recorded upstream class extending
  `IsFinite f`, `Flat f`, and `LocallyOfFinitePresentation f`. No constant-degree
  hypothesis or chosen positive degree is imposed.
- The existence of an ample invertible module on `Y` is the single hypothesis
  `hY : ∃ M : Y.Modules, ∃ hM : M.IsInvertible, @IsAmple Y M hM`.
  Invertibility is existentially supplied and explicitly passed to the ampleness predicate.
- The existence asserted on `X` is
  `∃ N : X.Modules, ∃ hN : N.IsInvertible, @IsAmple X N hN`.
  This asserts existence, with no descent datum or identification of a pullback.
- Absolute ampleness on both schemes is the recorded `Scheme.Modules.IsAmple`:
  quasi-compactness and positive-power global sections with affine nonvanishing loci
  around every point. It is not a relative ampleness predicate.
- There are no normality, Noetherianity, properness, finite-type-over-a-field, or
  additional base-scheme binders. The properness import is only a proof dependency
  supporting the finite closed-map/finite-fibres step and supplies no hypothesis.

Recorded statement dependency declarations used, with their full signatures and
source docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (the schemes and their morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (Zariski local rank-one trivializations).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (absolute ampleness).

These are all public imports. Already recorded proof modules are plain imports:
finite-locally-free degree locally constant, function norm, trivialization upstairs,
finite-map properness/closedness/finite fibres, ample finite principal affine, and
intersection with a section nonvanishing open. The proof nodes
`lem-sfb-norm-frame-tensor-section-gluing` and
`lem-sfb-finite-function-norm-nonvanishing` have no Lean record in the read checkout,
so their absent modules cannot be imported; their mathematical uses are retained
in the proof docstring. Neither notion occurs in the theorem signature.

Edge cases checked mathematically before writing:

- The empty scheme is allowed: no nonemptiness binder occurs. Its structure sheaf
  is invertible and the ampleness point condition is vacuous.
- Degree zero is not excluded by an extra binder; surjectivity makes any degree-zero
  target piece empty. Varying positive degrees on different components are allowed.
- Identity morphisms give the immediate existence implication.
- Nonreduced schemes and arbitrary characteristic are included. There is no field,
  reducedness, normality, or characteristic binder.
- Quasi-compactness of `Y` is already part of `hY` through `IsAmple`; that of `X`
  follows by surjectivity rather than being assumed independently.

Searches for an existing statement:

- `msearch.py`, LeanFinder: "A finite locally free surjective morphism of schemes
  descends existence of an ample invertible module". Eight results concerned affine
  covers, general morphism descent, affine-space surjectivity, and finite affine-section
  maps. None states existence of an ample invertible module on the target.
- `msearch.py`, Loogle: `"IsAmple"`. Zero results.
- `msearch.py`, LeanSearch: "Existence of an ample invertible sheaf descends under
  finite locally free surjective morphisms". Eight results concern general fpqc
  morphism-property descent, surjectivity, and faithful sheaf pushforward; no match.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`:
  `IsAmple|norm_ample|push_down_ample`. Zero results.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`: ampleness together with finite
  morphisms or surjectivity. Inspected the nearby finite-normal ample descent,
  characteristic-p reduction, field-extension existence, finite-surjective ampleness
  reflection, and upstream module degree-pullback statements. These have different
  hypotheses/conclusions; none is the present general existence statement.
- `grep -rn 'lem-sfb-finite-locally-free-ample-existence' lean/WeilConjectures`:
  no hits. A corresponding search of `dag/lean_names_upstream.json` and both geometry
  trees for the proposed name, norm-ample, and finite-locally-free/ample combinations
  found no duplicate declaration.

No statement dispute or node fault was found. No dependency interface repair is needed.

## Second reading by N5

Performed a separate self-reading of the node and completed file; no second agent
was started, as the dispatcher brief forbids that. Checked the named `Y ⟶ X`
direction, both independent existential module witnesses and invertibility proofs,
and that `@IsAmple` explicitly uses the matching witness on each side. Checked
that the finite locally free class has no constant-degree field, and that both
ampleness occurrences resolve inside `AlgebraicGeometry.Scheme.Modules` to the
absolute definition read above. Compared every hypothesis against the statement:
no extra base, normality, finiteness over a field, Noetherianity, properness,
nonemptiness, or compatibility of the two modules appears. The proof description
includes the varying-degree assembly and fixes a single norm module before all
powers and sections. No mismatch was found and no statement correction was made.

## Validation

All compilation uses the prescribed `scompile.py` wrapper. The delivery dry run
and final delivery use `deliver2.py`; no direct Git command, live-source edit, or
global build is performed.
