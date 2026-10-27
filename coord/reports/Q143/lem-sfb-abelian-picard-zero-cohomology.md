## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.PicardZeroCohomology` states
`AlgebraicGeometry.IsAbelianVariety.isZero_moduleCohomology_of_algebraicallyTrivial_nontrivial`.
Its only proof is `sorry`, as required for stage 2. No definition, helper theorem,
new node, or dependency repair is introduced. The item's mathematical statement is unchanged.
Its `stmt_deps` gains the already landed `def-sfb-line-algebraic-equivalence`, whose
recorded definition supplies exactly the notion described in the item's statement.

Hypothesis and clause correspondence:

- An algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`.
  The universe is explicit and arbitrary.
- A/k an abelian variety is `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. The recorded class says proper, smooth and connected;
  `GrpObj` separately supplies the group scheme structure, exactly as its docstring requires.
- L an invertible O_A-module is `(L : A.left.Modules) [L.IsInvertible]`, using
  the recorded ordinary Zariski module category and local rank-one predicate.
- L algebraically equivalent to O_A is
  `algebraicallyTrivial : Scheme.Modules.AreAlgebraicallyEquivalent A L
  (𝟙_ A.left.Modules)`. Reading both this definition and
  `LineAlgebraicEquivalenceStep` confirms that it is the equivalence closure of
  isomorphic pairs and fibres of one invertible family over a smooth connected
  separated finite-type parameter variety. The two fibre maps are rational points.
  Smoothness supplies local finite type; quasi-compactness supplies finite type.
  It is not replaced by numerical equivalence, degree zero, or an arbitrary
  classifying point in a chosen dual.
- L not isomorphic to O_A is `nontrivial : ¬ Nonempty (L ≅ 𝟙_ A.left.Modules)`.
  The monoidal unit of this recorded module category is the structure sheaf.
- Every integer i >= 0 is `(i : ℕ)`, covering exactly the nonnegative integers.
- H^i(A,L) = 0 is
  `IsZero ((RingedSpace.moduleCohomology A.left.toRingedSpace i).obj L)`.
  This functor is R^i global sections on ordinary O_A-modules, the cohomology
  recorded by `pqf-def-cohomology`. It is a ModuleCat object, so `IsZero` is
  categorical vanishing, equivalently a trivial underlying group.
- Every characteristic and every dimension are included: there is no characteristic
  or dimension binder, lower bound on dimension, or upper bound on degree.

Recorded statement dependencies read and used:

- `def-weil-field`: Mathlib `Field`, read in `Mathlib/Algebra/Field/Defs.lean`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`, identified explicitly by
  its `mathlib_match.how`; full signature/docstring read in
  `Mathlib/FieldTheory/IsAlgClosed/Basic.lean`. Only algebraic closedness, not a
  chosen algebraic closure, is needed here.
- `def-sc-abelian-variety`: `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`; full class and docstring read.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; full class and docstring read.
- `lem-sfb-abelian-polarization-calculus`:
  `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`,
  `AlgebraicGeometry.IsAbelianVariety.exists_dual_polarization_calculus`;
  complete theorem signature/docstring read, including its imported dual datum and
  the underlying algebraic-equivalence definition. This is a public import as
  required for a recorded statement dependency.
- `pqf-def-cohomology`: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; full signature/docstring
  read, together with `AlgebraicGeometry.RingedSpace.moduleCohomology` in
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- Added landed notion `def-sfb-line-algebraic-equivalence`:
  `Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence`,
  `AlgebraicGeometry.Scheme.Modules.AreAlgebraicallyEquivalent` and
  `LineAlgebraicEquivalenceStep`; both full definitions/docstrings read.

All recorded, available proof-dependency modules are imported without `public`.
For `lem-pc-h0-proper-variety`, both modules in its `lean.modules` are imported.
For the closed-immersion Mathlib leaf, the named Mathlib files are imported.
The proof docstring follows all five DAG steps and their canonical maps: geometric
fibre verification and Poincare biadditivity; antidiagonal restriction; the generic
nonzero-section argument; strong induction via Kunneth; and the identity section
of addition with the canonical cohomology composition comparison.

Source check: opened the cited primary book scan
https://djvu.online/file/2tC7xp3dbqGCh, OCR lines 2374–2443, printed pp.74–77.
The section expressly postpones the characteristic-zero hypothesis. Property
(vii) and its Kunneth/section proof occur before that restriction; properties
(i) and (vi) give the relation to the algebraic-equivalence convention.
The local book remains WANTED as already recorded by the node; no literature
or shared-repository files were changed.

Edge cases checked before writing:

- Degree zero is included. Nontriviality is necessary because the trivial line
  has H^0 = k, which is nonzero. The stated negative isomorphism hypothesis
  excludes exactly that case.
- Dimension zero is included, with a vacuous nontriviality hypothesis: a connected
  smooth proper zero-dimensional group over an algebraically closed field is
  Spec k, whose invertible modules are trivial.
- Positive characteristic is unrestricted. The argument uses neither division
  by a degree nor characteristic-zero vanishing.
- Degrees above the dimension remain quantified; no artificial bounded interval.
- Empty A is impossible already from connectedness and the group identity, so no
  additional nonemptiness hypothesis is added.
- Algebraic equivalence includes isomorphic representatives and arbitrary finite
  chains, rather than requiring one family or one link.

Searches for an existing statement (all through the prescribed wrappers or rg):

- `msearch.py ... leanfinder "A nontrivial algebraically trivial invertible sheaf on
  an abelian variety has zero coherent cohomology in every degree"`: 8 hits on
  group cohomology, Ext classes and cotangent cohomology; no matching statement.
- `msearch.py ... leansearch "A nontrivial algebraically trivial line bundle on an
  abelian variety has zero coherent sheaf cohomology"`: 8 unrelated group,
  Hom-complex and cotangent cohomology hits; no match.
- `msearch.py ... loogle '"cohomology", "Picard"'`: 0 hits.
- `msearch.py ... grep 'Picard|AbelianVariety|Poincare' AlgebraicGeometry`:
  3 Weierstrass-model comments mentioning Picard groups; no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `AlgebraicEquiv|AlgebraicallyEquiv|AlgebraicallyTrivial|algebraicEquiv|algebraicallyEquiv|algebraicallyTrivial`:
  found the existing `AreAlgebraicallyEquivalent` definition, dual datum and
  multiplication algebraic-equivalence statement, all reused or inspected.
- `rg -n 'lem-sfb-abelian-picard-zero-cohomology' lean/WeilConjectures`: no match.
- `rg` for vanishing/zero/subsingleton in the two abelian-variety directories:
  found `isZero_moduleCohomology_of_homogeneous_nontrivial`. Its hypothesis is
  invariance under all rational translations, not the item's algebraic-equivalence
  hypothesis, so it is not an exact existing statement of this node.
- `rg` in both trees for
  `isZero_moduleCohomology_of_algebraically|PicardZeroCohomology`: no collision.
- `rg -l 'AreAlgebraicallyEquivalent|LineAlgebraicEquivalence|LineAlgebraicEquivalenceStep'
  dag/nodes`: identifies the already landed definition node and related consumers.
- `coord/repair-notes` inventory: no repair note named for this item.

No statement dispute or unusable dependency was found.

## Second reading by Q143

A second, separate pass through the node and the finished module was performed by
this worker. No other agent was started, in accordance with the dispatcher's
explicit instruction; this is a self-review, not a claim of independent authorship.

The checked binders are Field plus IsAlgClosed, the group-object and abelian-variety
instances, the actual invertible module L, algebraic equivalence to the module
unit, and the negative existence of a module isomorphism. Each matches the node.
The conclusion uses ordinary ringed-space module cohomology, includes i = 0,
and does not restrict characteristic or dimension. The monoidal unit and
nontriviality condition refer to exactly the same module category. The shared
algebraic-equivalence definition was reopened and checked for arbitrary chains,
smooth connected parameter varieties and rational endpoint points. The nearby
homogeneous-acyclicity theorem was reopened to verify it is not an exact match.
The original polarization-calculus dependency remains imported; the precise
already landed algebraic-equivalence node is additionally cited. No mathematical
mismatch or correction was found. No new or dependency modules require review.
