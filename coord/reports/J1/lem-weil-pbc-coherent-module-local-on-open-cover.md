## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CoherentModuleLocalOnOpenCover.lean` states
`AlgebraicGeometry.coherent_module_local_on_open_cover` with a single `sorry` proof.
The statement uses `X : Scheme.{u}`, an `X.Modules` object `F`, an index type
`I : Type u`, and open subschemes `U : I → X.Opens`; `hU : ⨆ i, U i = ⊤`
renders that these opens cover `X`.

The first conjunct is the implication in clause (1): from
`RingedSpace.IsCoherent X.toRingedSpace F`, for every open `W : X.Opens` the
restricted module
`(Scheme.Modules.restrictFunctor W.ι).obj F` is
`RingedSpace.IsCoherent W.toScheme.toRingedSpace ...`. Thus `W.ι` is the open
immersion and Mathlib's `restrictFunctor` renders the restriction
`\mathcal F|_W`; `W.toScheme.toRingedSpace` renders `\mathcal O_W`.
The second conjunct is clause (2): if every indexed restriction
`(Scheme.Modules.restrictFunctor (U i).ι).obj F` is coherent on
`(U i).toScheme.toRingedSpace`, then `F` is coherent on `X`.
`RingedSpace.IsCoherent` is the project's definition from `pqf-def-coherent`; it
contains the finite-type condition and the finite-type kernel condition for
maps from finite free modules, so both clauses retain the node's two defining
conditions. No proof is attempted.

Dependency declarations used:

- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from
  Mathlib (`def-pc-scheme`).
- `SheafOfModules` / `Scheme.Modules` from Mathlib's module-sheaf category
  (`def-weil-sheaf-of-modules-category`).
- `Scheme.Modules.restrictFunctor`, `restrictAdjunction`, and its
  `IsLeftAdjoint` instance from `Mathlib.AlgebraicGeometry.Modules.Sheaf`, the
  recorded declaration for `lem-weil-pbc-module-restriction-open-immersion-colimits`.
- `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `Sheaf.AlgebraicGeometry.Coherent`, the recorded declaration for
  `pqf-def-coherent`.

Edge cases checked: the index universe is `Type u`, matching `Scheme.{u}`;
no nonemptiness, finiteness, separation, or characteristic assumptions are
added. The cover equation permits arbitrary indexed covers (including the empty
index in the degenerate case where `⊥ = ⊤`), singleton covers, repeated opens,
and the empty scheme. `W` may be `⊥` or `⊤`; restriction is expressed by the
canonical open immersion, and the conclusion includes all opens. Zero modules
and zero schemes are allowed by the predicate and no nonzero hypotheses are
introduced.

Searches made: `msearch.py ... leanfinder` and `leanfinder` for coherence of a
module on an open cover (only finite-type and quasicoherent generator notions,
no locality theorem); `msearch.py ... loogle` for
`SheafOfModules.IsFiniteType`, `Scheme.Modules.restrictFunctor`, and
`IsCoherent` (only Mathlib restriction declarations and the project's coherent
definition); `msearch.py ... grep` and `rg -n` over Mathlib, `WeilConjectures`,
and `lean/Sheaf` for coherent/open-cover/restriction declarations (no existing
statement of this node). The node's recorded Mathlib searches were also read;
all reported no matching coherence-locality theorem. No statement correction,
new definition node, or dependency module was needed.

## Second reading by J1

I opened the node and Lean file and matched each object and clause.

- `$X$` is `(X : Scheme.{u})`, with no extra scheme hypotheses.
- `$\mathcal F$` is `(F : X.Modules)`, the canonical module category over `X`.
- `$I$` and the opens are `(I : Type u)` and `(U : I → X.Opens)`; the index
  universe is the scheme universe.
- The cover `$X = \bigcup_i U_i$` is `hU : ⨆ i, U i = ⊤`.
- Clause (1) is the first conjunct: coherence on `X.toRingedSpace` implies,
  for every `W : X.Opens`, coherence of
  `(Scheme.Modules.restrictFunctor W.ι).obj F` on `W.toScheme.toRingedSpace`.
- Clause (2) is the second conjunct: coherence of every indexed restriction to
  `U i` implies `RingedSpace.IsCoherent X.toRingedSpace F`.

The predicate is exactly the recorded `pqf-def-coherent` declaration, retaining
both finite-type and kernel conditions. Restriction is exactly the recorded
Mathlib functor from `lem-weil-pbc-module-restriction-open-immersion-colimits`.
No mismatch was found and no source or Lean change was required.

Edge cases checked: empty, singleton, and repeated covers; `W = ⊥` and `W = ⊤`;
empty schemes; zero modules; and all natural numbers internal to coherence. No
nonemptiness, finiteness, separatedness, characteristic, or nonzero assumptions
are present.

The node's LeanSearch, LeanFinder, Loogle, and grep searches were checked, and
the corresponding searches over Mathlib, `WeilConjectures`, and `lean/Sheaf`
found no existing theorem for this statement. Dependency declarations and source
modules were opened and match their cited notions.
