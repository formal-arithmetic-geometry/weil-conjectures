## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint`
states `AlgebraicGeometry.Scheme.Hom.finiteDimensional_residueField_of_isOpen_singleton_asFiber`.
Its sole proof is `sorry`; no definition or supporting theorem is added. The docstring carries
all four steps of the node's natural-language proof and their dependency IDs.

Hypothesis and clause mapping:

- Schemes X and S: `{X S : Scheme.{u}}`; the arbitrary explicit universe u imposes no
  size restriction beyond Mathlib's category of schemes.
- Morphism f from X to S: `(f : X ⟶ S)`.
- Locally of finite type: `[LocallyOfFiniteType f]`, with no quasi-compactness, separatedness,
  Noetherian, or global finite-type assumption.
- Point x of X: `(x : X)`; the point s is directly `f x`, so no independently chosen
  base point or equality hypothesis is needed.
- Fibre X_s: `f.fiber (f x)`, Mathlib's pullback along `S.fromSpecResidueField (f x)`.
- The corresponding point of X_s: `f.asFiber x`, defined using the inverse of the fibre
  homeomorphism on the pair `⟨x, rfl⟩`.
- Isolatedness means the singleton is open: the binder
  `(hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x))))`.
- The induced extension is precisely `(f.residueFieldMap x).hom` from
  `S.residueField (f x)` to `X.residueField x`. The conclusion's
  `letI := (f.residueFieldMap x).hom.toAlgebra` installs its scalar multiplication;
  no arbitrary algebra structure is assumed.
- Finiteness of that extension is
  `FiniteDimensional (S.residueField (f x)) (X.residueField x)`.
  In Mathlib this is an abbreviation for `Module.Finite` over a division ring, expressing
  finite dimensionality, not finiteness of the underlying set or positivity of finrank.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (imported transitively by Fiber).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (a public import of Fiber).
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberHomeo` and `asFiber`, `Mathlib.AlgebraicGeometry.Fiber`, imported directly.
  `fiber` is the required pullback and `fiberHomeo` identifies its carrier with the set fibre.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`
  (imported transitively by Fiber). The latter is the residue map induced by the stalk map.
- `def-pc-field-extension`: `Algebra` and `RingHom.toAlgebra`,
  `Mathlib.Algebra.Algebra.Defs` (transitive). Both residue fields already have Field instances.
- `FiniteDimensional`, `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, imported directly,
  is the standard finite-vector-space predicate used in the conclusion.

Edge cases checked before writing: an empty X admits no x, so the implication is vacuous;
an empty S admits no morphism with a source point. The identity morphism has singleton
fibres and the induced residue extension has dimension one. Infinite base fields and
positive characteristic are included. No separability is asserted: finite purely
inseparable extensions are allowed. Nonreduced X and disconnected schemes are included.
Local finite type is retained rather than strengthened to global finite type. The
isolatedness concerns the fibre singleton, not the singleton in X. Residue fields at
points are fields, so the zero-ring case creates no artificial field extension.

Source checked online because the local `literature/stacks-project/morphisms.tex` is absent:
[Stacks 01TH](https://stacks.math.columbia.edu/tag/01TH) identifies isolatedness in the fibre
with quasi-finiteness at x under local finite type;
[Stacks 01TG](https://stacks.math.columbia.edu/tag/01TG) gives the finite residue extension.
The node agrees with these sources. No node fault, statement correction, or
STATEMENT-DISPUTED finding.

Searches (2026-10-11):

- `msearch.py ... leansearch "An isolated point of a fibre of a locally finite type morphism
  has finite residue field extension"`: unavailable (Internal Server Error); recorded as
  unavailable, no mathematical verdict inferred.
- `msearch.py ... leanfinder "An isolated point in the fibre of a locally finite type scheme
  morphism has finite residue field extension"`: eight hits. These include
  `Algebra.instFiniteResidueFieldOfQuasiFiniteAt`, `Algebra.QuasiFinite.instFiniteResidueField`,
  `RingHom.EssFiniteType.residueFieldMap`, and the scheme closed-singleton criterion.
  None is the claimed scheme-level implication with the isolated-fibre hypothesis.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.residueFieldMap, FiniteDimensional"`:
  zero hits.
- `msearch.py ... grep "residueFieldMap|isOpen_singleton_asFiber"
  AlgebraicGeometry/Morphisms`: ten hits, including
  `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`, which concludes quasi-finiteness,
  not finite dimensionality of this residue extension.
- `rg -n 'isolated.*residue|finite.*residue|residueField.*[Ff]inite|[Ff]inite.*residueField'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures lean/Sheaf`: no exact statement.
  Read the full nearby `Scheme.Hom.finite_residueFieldMap` in the source's
  `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`: it requires unramifiedness.
  Read `Scheme.Hom.finite_residueField_of_isClosed` in `WeilConjectures/PointCount.lean`:
  it requires a structure map to a field and a closed point. Neither is this statement.
- `rg -n 'lem-weil-pbc-isolated-fibre-point-residue-finite'
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- Collision search for `finiteDimensional_residueField_of_isOpen_singleton_asFiber` and
  `finiteDimensional_residueField_of_isOpen_asFiber` in `dag/lean_names_upstream.json`,
  Mathlib, WeilConjectures, and `lean/Sheaf`: no hits.

Validation: `scompile.py H1 lem-weil-pbc-isolated-fibre-point-residue-finite <module>`
compiled cleanly on the server in 1.6 seconds, exit code 0, no warnings.

## Second reading by H1

Read the item JSON, its complete four-step proof, the delivered Lean module, and
all five statement dependency nodes independently. The node has no statement_change;
there are no new definition nodes or dependency modules in this delivery.

The statement checklist, matched in its quantifier order:

| Node object, hypothesis or conclusion | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary schemes X and S (def-pc-scheme) | `{X S : Scheme.{u}}` | Exact: Mathlib's locally affine locally ringed spaces, with arbitrary universe u. |
| A scheme morphism f : X → S | `(f : X ⟶ S)` | Exact: Scheme.Hom is a morphism of the underlying locally ringed spaces. |
| f locally of finite type (def-weil-finite-type-morphism) | `[LocallyOfFiniteType f]` | Exact: the affine-local finite-type property; no global finite-type or quasi-compactness assumption. |
| A point x ∈ X and s = f(x) | `(x : X)` and `f x` | Exact: s is substituted throughout, rather than independently quantified. |
| Scheme-theoretic fibre X_s (def-pc-scheme-fibre) | `f.fiber (f x)` | Exact: pullback of f along `S.fromSpecResidueField (f x)`. |
| Its point corresponding to x | `f.asFiber x` | Exact: inverse of `f.fiberHomeo (f x)` on `⟨x, rfl⟩`; `fiberι_asFiber` identifies its projection with x. |
| That point is isolated, meaning its singleton is open | `hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))` | Exact: topology on the fibre, rather than on X. |
| Residue fields κ(s), κ(x) (def-weil-residue-field) | `S.residueField (f x)`, `X.residueField x` | Exact: residue fields of the two stalks. |
| Extension induced by f (def-pc-field-extension) | `letI := (f.residueFieldMap x).hom.toAlgebra` | Exact: residueFieldMap is induced by f.stalkMap, and toAlgebra uses exactly this ring homomorphism. |
| The extension is finite, i.e. κ(x) is finite-dimensional over κ(s) | `FiniteDimensional (S.residueField (f x)) (X.residueField x)` | Exact: this is Module.Finite over the installed algebra's module structure. No separability or underlying-set finiteness is asserted. |

Opened the dependency declarations themselves in Mathlib: Scheme and Scheme.Hom
(Scheme.lean:42,73); LocallyOfFiniteType (Morphisms/FiniteType.lean:43);
fiber, fiberHomeo and asFiber (Fiber.lean:38,103,118); residueField and
residueFieldMap (ResidueField.lean:45,123); Algebra and RingHom.toAlgebra
(Algebra/Algebra/Defs.lean:95,197). All implement the notions in their dependency
nodes; no unusable recorded match or private replacement was found.
FiniteDimensional (LinearAlgebra/FiniteDimensional/Defs.lean:75) is Module.Finite.

The local Stacks .tex directory is absent. Read the upstream morphisms.tex directly:
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
labels lemma-quasi-finite-at-point-characterize and lemma-residue-field-quasi-finite
(01TH and 01TG). The former explicitly assumes only a morphism of schemes, a point,
and local finite type, and identifies isolatedness with an open singleton in the
fibre. The latter gives precisely finiteness of the induced residue extension.
Read the surrounding proof and section context: no implicit Noetherian,
separatedness, characteristic or base-field assumption is needed. The docstring's
four steps match the node's proof: base change to the fibre, the isolated-point
field case, identification of the fibre point's residue field compatibly with the
base field action, then transport of finite dimensionality. No clause or proof
step is missing.

Edge cases: an empty X has no x, so the implication is vacuous; an empty S cannot
receive a source point. Empty fibres are impossible at f x. Identity maps give
dimension one. Zero rings can occur in affine charts of empty schemes but do not
produce residue fields at points, so no artificial Field assumption excludes a
nonempty case. Arbitrary characteristic, infinite fields, inseparable extensions,
nonreduced schemes and disconnected schemes are admitted. The universe u is
explicit and arbitrary, and both schemes lie in Mathlib's common universe for the
morphism category; enlarging it covers any pair of sizes. There is no test-object
quantification in a smaller universe. Index sets and n are absent, so their empty
and zero cases are inapplicable. All variables and universes are bound.

Independent duplicate searches used different wording from the worker:

- `msearch.py H1 lem-weil-pbc-isolated-fibre-point-residue-finite leanfinder
  "finite dimensional extension of residue fields at a quasi finite point of a scheme map"`:
  eight hits, including Algebra.instFiniteResidueFieldOfQuasiFiniteAt and
  IsLocalRing.ResidueField.finite_of_module_finite. These are ring-level statements,
  not the scheme statement with its isolated-point hypothesis.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.residueFieldMap, Module.Finite"`:
  zero hits.
- `msearch.py ... grep "residueFieldMap.*Finite|finiteDimensional.*residue"
  AlgebraicGeometry`: zero hits.
- Direct rg over the project's lean/Sheaf and source WeilConjectures for
  `residueField.*[Ff]inite|[Ff]inite.*residueField|isOpen_singleton_asFiber|Isolated`,
  and over Mathlib's QuasiFinite.lean: no exact duplicate. Opened
  Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber (QuasiFinite.lean:395):
  its conclusion is quasi-finiteness. Opened Scheme.Hom.finite_residueFieldMap
  (source Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:153):
  it assumes FormallyUnramified f. Opened Hom.finite_residueField_of_isClosed
  (PointCount.lean:73): it concerns a closed point over a field. None renders
  the item's implication exactly.
- Collision rg of the delivered full declaration's final name in
  dag/lean_names_upstream.json, Mathlib, WeilConjectures and lean/Sheaf: no hits.

No mismatch was found. The Lean module and node record were left unchanged;
only this independent second-reading report was appended. No hollow definition
or extra theorem is present. The only theorem proof is sorry. The two imports
are used by the fibre objects and finite-dimensional predicate; source docstrings,
namespace, naming and line lengths conform to H8/H9. Checked that lean.statement
is verbatim the signature from theorem through the conclusion, excluding :=.

Second-reader validation: scompile.py compiled the delivered module on the server
in 1.6 seconds, exit code 0, with no warnings or errors.
