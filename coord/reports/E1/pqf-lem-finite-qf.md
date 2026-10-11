## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteIsQuasiFinite` states
`AlgebraicGeometry.Scheme.Hom.isQuasiFinite_of_isFinite` with a single `sorry` proof.
No definitions or additional theorems are introduced.

The node says “A finite morphism of schemes is quasi-finite.” Its full hypothesis and
conclusion are rendered as follows:

- “morphism of schemes”: `{X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)`,
  with the universe `u` explicitly declared and arbitrary.
- “finite”: `[AlgebraicGeometry.IsFinite f]`, Mathlib's scheme-morphism predicate,
  which requires affine inverse images of affine opens and finite induced ring maps.
- “is quasi-finite”: `f.IsQuasiFinite`, exactly the landed predicate of
  `pqf-def-quasifinite`. Its definition is `LocallyOfFiniteType f ∧ QuasiCompact f ∧
  ∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x)))`: finite type, and each
  point isolated in its scheme-theoretic fibre. Nothing else is concluded.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`:
  its full class declaration and docstring were inspected.
- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite` (node `pqf-def-quasifinite`):
  its full definition and docstring were inspected, together with the three other
  declarations recorded by that node (`IsQuasiFiniteAtPoint`, `IsLocallyQuasiFinite`,
  `HasFiniteFibres`). Only `IsQuasiFinite` is needed for this statement.

The base item had no statement dependencies, despite using the project's notion of
quasi-finite. Its `stmt_deps` gains the already landed `pqf-def-quasifinite`, as allowed
by STMT_DEPS MAY GAIN LANDED NODES. The mathematical statement and proof remain unchanged.
There are no new nodes and no dependency modules.

The theorem docstring reproduces the complete node proof: finite implies proper and
finite type by clause (1) of `lem-weil-pbc-finite-closed-map-finite-fibres`; finite type
means locally finite type and quasi-compact by `def-weil-pbc-scheme-conventions`; clause
(2) gives finite fibres; the reverse implication of `pqf-lem-qf-finitefibres` finishes.
These are proof dependencies, not imports needed to elaborate a stage-2 statement.
The blueprint source path recorded by the node is not present in this machine's
literature checkout. The statement and proof above are read from the imported node.

Edge cases checked: the empty source is included and the isolated-point condition is
vacuous there; the empty target is included (any morphism into it necessarily has empty
source); arbitrary non-Noetherian schemes, nonreduced schemes, and schemes not over a
field are included. No nonemptiness, reducedness, Noetherian, separatedness, field or
characteristic hypothesis is added. Nonreduced finite fibres still have isolated points:
the assertion concerns the underlying topology, not reducedness. No statement fault
or mathematical dispute was found.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder "A finite morphism of schemes is quasi-finite"`:
  eight hits, including `AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite`,
  `IsFinite.instLocallyOfFiniteType`, `IsFinite`, and properness instances. The candidate
  instance's full source was read in Mathlib's `Morphisms/QuasiFinite.lean`; its conclusion
  is `LocallyQuasiFinite f`, which explicitly omits local finite type and quasi-compactness.
  It is therefore not the item's whole conclusion.
- `msearch.py ... loogle "AlgebraicGeometry.IsFinite,
  AlgebraicGeometry.LocallyQuasiFinite"`: seven hits, including that same instance,
  `IsFinite.iff_isProper_and_locallyQuasiFinite`, and fibre-finiteness results. None
  concludes the project's `Scheme.Hom.IsQuasiFinite` predicate.
- `msearch.py ... grep "IsFinite.*LocallyQuasiFinite|LocallyQuasiFinite.*IsFinite"
  AlgebraicGeometry/Morphisms`: five hits in `QuasiFinite.lean`, including the instance
  at line 90; none is an exact match.
- `msearch.py ... leansearch "A finite morphism of schemes is quasi-finite"`:
  unavailable, Internal Server Error. No verdict is based on this unavailable service.
- `rg -n "pqf-lem-finite-qf|isQuasiFinite_of_isFinite|IsFinite.*IsQuasiFinite|
  IsQuasiFinite.*IsFinite"` over Mathlib, `WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no matches before writing the new file. Earlier
  broader searches for quasi-finite notions found the landed `QuasiFiniteMorphism.lean`
  and source results concerning Mathlib `LocallyQuasiFinite`, but no exact theorem.

Validation: `scompile.py E1 pqf-lem-finite-qf
/home/ubuntu/weil-sandbox/E1/pqf-lem-finite-qf/lean/Sheaf/AlgebraicGeometry/FiniteIsQuasiFinite.lean`
returned exit code 0, compiled in 1.6 seconds, with no warnings or errors. All objects,
variables and universes are bound explicitly. The proof is exclusively `sorry`.

## Second reading by E1

The node introduces a morphism of schemes `f : X ⟶ S` and assumes `[IsFinite f]`; its sole
conclusion is that `f` is quasi-finite. The Lean declaration
`AlgebraicGeometry.Scheme.Hom.isQuasiFinite_of_isFinite` renders these as
`{X S : AlgebraicGeometry.Scheme.{u}}`, `(f : X ⟶ S)`,
`[AlgebraicGeometry.IsFinite f]`, and `: f.IsQuasiFinite`, respectively. The universe is
shared by both schemes, and no field, characteristic, Noetherian, separatedness, or
nonemptiness hypothesis is added. The conclusion is exactly the project predicate from
`pqf-def-quasifinite`, including finite type, quasi-compactness, locally finite type, and
isolated points in each scheme-theoretic fibre; no clause is weakened or strengthened.

The empty source and target, zero and nonreduced schemes, and arbitrary `u` remain covered;
there are no index sets or numerical parameters. The dependency declaration
`AlgebraicGeometry.Scheme.Hom.IsQuasiFinite` in
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` was reread and is the exact notion used.
Searches in Mathlib, `WeilConjectures`, and `lean/Sheaf` found no exact existing theorem;
Mathlib's `LocallyQuasiFinite` consequence of `IsFinite` omits the project's finite-type
and quasi-compact requirements.

The only mismatch was node metadata: `stmt_deps` was empty despite the conclusion using
`pqf-def-quasifinite`. I changed it to `['pqf-def-quasifinite']`; the Lean module and
statement remain unchanged. No new definitions or dependency modules were needed.
