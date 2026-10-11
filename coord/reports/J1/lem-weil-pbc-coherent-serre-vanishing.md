## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentSerreVanishing` states
`AlgebraicGeometry.Scheme.Modules.exists_isZero_moduleCohomology_tensorPow_of_ample`.
It is a single theorem with `sorry`; it introduces no definitions or extra hypotheses.
The node is unchanged except for its `lean` record. No dependency module, new node,
statement correction, or disputed statement is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative Noetherian ring A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- A scheme X and the specified map f to Spec A: `{X : Scheme.{u}}`
  and `(f : X ⟶ Spec (CommRingCat.of A))`.
- The map is proper: `[IsProper f]`. Mathlib includes separatedness, universal
  closedness and local finite type; universal closedness implies quasi-compactness,
  so this is finite type as required by the node.
- A coherent O_X-module F: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`. There is no added
  `F.IsQuasicoherent` assumption; coherence on this Noetherian scheme implies it.
- An invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`.
- L is ample: `(hL : IsAmple X L)`, the recorded absolute notion. In particular,
  it supplies the quasi-compactness and the affine nonvanishing neighbourhoods.
- There exists a nonnegative threshold n₀: `∃ n₀ : ℕ`.
- For every positive p and every n at least n₀: `∀ (p n : ℕ), 0 < p → n₀ ≤ n →`.
  The single existential precedes both universal quantifiers; the bound is uniform in p.
- Tensor product and tensor power: `tensorObj F (L.tensorPow n)`. The former is the
  symmetric monoidal sheaf tensor product and the latter recursively uses that same
  structure, with the structure module at n = 0. The scheme operations from Invertible
  use the very same `SheafOfModules.monoidalCategory` recorded by the tensor node;
  no alternative tensor or power is introduced.
- H^p(X,-): `(RingedSpace.moduleCohomology X.toRingedSpace p).obj ...`, the
  right derived functors of O_X-module global sections, as required by the cohomology
  node and standing conventions. Vanishing is `IsZero` on this ModuleCat object,
  equivalent to its underlying module being zero. It is not `IsZero` on a bare Type.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (ideals finitely generated).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  supplied transitively by the geometry imports.
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (via Ample):
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorObj`, and `tensorPow`.
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Sheaf.Paper.PQFCohomology`: read the full signature and docstring of
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; the cohomology functors
  it specifies are `AlgebraicGeometry.RingedSpace.moduleCohomology`, defined in
  its imported `Sheaf.Topology.RingedSpaceModuleCohomology` (also read).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: the recorded
  `SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification` are reused
  through the canonical scheme tensor operations. Its positiveTensorPower only
  covers positive exponents, while the existing scheme tensorPow also covers zero.

Edge cases checked before writing: n = 0 uses O_X and is allowed whenever n₀ = 0;
p = 0 is deliberately excluded, since global sections generally do not vanish.
The empty scheme, zero coherent module, and zero ring are not excluded by any
nonempty/nontrivial assumption; they give vacuous or zero cohomology. A trivial
invertible module is covered when it is ample (in particular on an affine scheme).
A is not specialized to a field, and no characteristic is imposed. One explicit
universe u covers the ring, scheme and module carriers; arbitrary differently sized
input data can be placed in a common larger universe. All variables and universes
are explicitly bound, with no file-local notation or instances.

Source read: this machine has no literature/stacks-project/coherent.tex, so the
actual cited text was opened at https://stacks.math.columbia.edu/tag/0B5T (part 4
and its proof), https://stacks.math.columbia.edu/tag/02O1 (including the uniform
positive-degree bound and the affine-base reduction), and
https://stacks.math.columbia.edu/tag/01VK (relative ampleness equals absolute
ampleness over an affine base). These confirm the node. The module docstring
contains all seven proof steps, including the dependency node names and the
finite-residue maximum that makes the threshold uniform.

Searches made:

- msearch.py leansearch: `Serre vanishing for coherent modules and ample invertible
  modules over a Noetherian affine base`. Service returned UNAVAILABLE, Internal
  Server Error; no negative verdict inferred from this failed service.
- msearch.py leanfinder: `Serre vanishing coherent module proper scheme over
  Noetherian ring ample invertible sheaf`. Eight hits, about restriction of functions
  to basic opens, limits of schemes, or SheafOfModules.IsFiniteType; no match.
- msearch.py loogle: `IsProper, IsNoetherianRing`. Zero hits, unknown identifier
  IsProper; not treated as evidence of absence.
- msearch.py grep in Mathlib/AlgebraicGeometry:
  `serre[Vv]anishing|serre_vanishing|Serre vanishing`. No hits.
- rg of the same Serre patterns and the item id in the source WeilConjectures
  and project lean/Sheaf: found the source Cohomology/Serre.lean field-case theorem
  `Scheme.Modules.exists_subsingleton_H_tensorObj_tensorPow` (full signature and
  docstring read), which assumes a field and uses source ampleness and abelian
  sheaf cohomology, so it is not this Noetherian-ring statement. Project
  RelativeSerreVanishing.lean is a higher-direct-image theorem assuming extra
  quasi-coherence, not this affine-base cohomology theorem. Remaining hits concern
  finite section modules or descriptions in docstrings.
- rg in source WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json:
  `exists_isZero_moduleCohomology_tensorPow|exists_isZero_moduleCohomology_tensor`.
  No collisions with the new declaration name.

Validation: server scompile.py compiled the module cleanly (exit 0, 1.8 seconds).
The mandatory deliver2.py --no-push dry run is run after completing this record.
The second reader supplies the independent second-reading section; no delivery
is pushed by this worker.

## Second reading by J1

I independently read the node statement, its source place, all eight `stmt_deps`, and
`Sheaf/AlgebraicGeometry/CoherentSerreVanishing.lean`. The correspondence is:

- Noetherian ring: `A : Type u`, `[CommRing A]`, `[IsNoetherianRing A]`; exact.
- Proper map to the affine spectrum: `{X : Scheme.{u}}`,
  `f : X ⟶ Spec (CommRingCat.of A)`, `[IsProper f]`; exact.
- Coherent module: `F : X.Modules` with
  `hF : RingedSpace.IsCoherent X.toRingedSpace F`; exact.
- Ample invertible module: `L : X.Modules`, `[L.IsInvertible]`, and
  `hL : IsAmple X L`; exact, using the recorded absolute ample notion.
- Uniform threshold and quantifiers: `∃ n₀ : ℕ, ∀ (p n : ℕ), 0 < p → n₀ ≤ n →`;
  this has precisely one threshold, all positive degrees, and all sufficiently large
  exponents.
- Tensor expression: `tensorObj F (L.tensorPow n)`; this is the canonical scheme
  module tensor and tensor power required by `def-pur-sheaf-tensor-product`.
- Cohomology vanishing: `IsZero ((RingedSpace.moduleCohomology
  X.toRingedSpace p).obj (...))`; this is the recorded O_X-module cohomology functor
  and expresses the zero object, exactly the node's vanishing clause.

No extra finiteness, quasi-coherence, field, characteristic, separatedness, or
universe assumptions occur. The explicit common universe is adequate for the node's
objects, and no variable is unbound. Edge cases checked are `n = 0`, positive versus
zero `p`, zero `F`, the empty scheme, zero ring, trivial ample invertible module, and
absence of characteristic assumptions; all are admitted exactly as in the node.

I searched Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and the upstream name index
using the worker's searches and additional `rg` searches for the declaration and
Serre-vanishing names. The field-case source theorem and the relative
higher-direct-image theorem are distinct statements, so no existing declaration
matches. The dependency declarations were checked for the exact notions, including
`Scheme.Modules.IsInvertible`, `IsAmple`, `tensorObj`, `tensorPow`, and
`RingedSpace.moduleCohomology`.

No mismatch was found. I changed no statement, hypotheses, dependencies, or Lean
code. The module compiles cleanly with `scompile.py`; its only proof is the required
`sorry`, and the node's `lean.statement` is verbatim the theorem signature.
