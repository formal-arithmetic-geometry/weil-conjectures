## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback` states
`AlgebraicGeometry.Scheme.Modules.finiteType_module_support_pullback`, with a single
`sorry` proof and no new definitions. Its statement agrees with the node and with
[Stacks Lemma 056J](https://stacks.math.columbia.edu/tag/056J), read in full online
because the local `literature/stacks-project/morphisms.tex` is absent.

Hypothesis and clause correspondence:

- A scheme X: `{X : Scheme.{u}}`. No Noetherian, separation, finiteness or base-field
  hypothesis is imposed on X.
- An O_X-module F: `(F : X.Modules)`.
- Quasi-coherent: `[F.IsQuasicoherent]`, the Mathlib sheaf-module presentation predicate
  recorded and explained in the dependency module `Coherent`. On schemes this is
  equivalent to the affine-local tilde description in the dependency node.
- Finite type: `[F.IsFiniteType]`, the Mathlib local finite-generators predicate recorded
  in `Coherent`; it means locally a quotient of a finite free sheaf.
- Stalk F_x: `F.presheaf.stalk x`, Mathlib's abelian-group stalk. In the tensor term,
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F` bundles exactly that
  carrier with its O_{X,x}-module structure (the functor definition was read in full).
- Local ring O_{X,x}: `X.presheaf.stalk x`; residue field: `X.residueField x`.
  The explicit last argument of `@TensorProduct` is
  `Module.compHom (X.residueField x) (X.residue x).hom`, giving the canonical scalar
  action through the residue map. It is an actual specified module structure, not an
  extra hypothesis or unspecified algebra structure.
- Support: `{x : X | ¬ Subsingleton (F.presheaf.stalk x)}`, exactly the project's inline
  convention from `def-weil-pbc-closed-subset-proper-over-base`. For a module, being
  the zero module is equivalent to its carrier being subsingleton.
- Part (1): `IsClosed` of this exact support locus.
- Part (2): `∀ x : X`, a conjunction of the membership/nonzero-stalk equivalence
  and the nonzero-stalk/nonzero-residue-tensor equivalence. Both equivalences are
  retained, including the first definitional one that the node explicitly states.
- Part (3): `∀ (Y : Scheme.{u}) (f : Y ⟶ X)`, finite type of
  `((tensorPullback f).obj F)` and equality of its nonzero-stalk locus with
  `f ⁻¹' {x : X | ¬ Subsingleton (F.presheaf.stalk x)}`. No restriction on f is imposed.
  Quasi-coherence of the pullback is used in the natural-language proof but is not
  added as an extra conclusion.

Dependency declarations and modules read:

- `Sheaf.AlgebraicGeometry.Coherent`: the docstring records Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`; their full
  signatures/docstrings were also read in Mathlib's `Sheaf/Quasicoherent.lean` and
  `Sheaf/Generators.lean`. `RingedSpace.IsCoherent` itself is not assumed.
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`: read
  `Scheme.IsClosedSubsetProperOver` and `Scheme.Modules.HasSupportProperOver`;
  only its prescribed inline support convention is needed, so no unused import of
  this properness module is introduced.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`, with
  object formula `tensorPullbackObj`; these are the recorded module pullback, not
  Mathlib's differently named pullback functor.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme` and `Scheme.Hom`, used via the imports.
- `Sheaf.Topology.PresheafModuleStalkFunctor`: the recorded general
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj` were read in full. The module
  follows the project's MODULE STALKS convention for scheme module sheaves, using
  `RingedSpace.moduleStalkFunctor` instead of the general ring-presheaf functor.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  and `Scheme.Hom.residueFieldMap`; full signatures and docstrings were read.
- Added already-landed dependency `def-pc-module-stalk-functor`, module
  `Sheaf.Algebra.Homology.ModuleStalkFunctor`, declaration
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`. Its recorded node, complete
  module and object formula were read. This packages the same stalk carrier as an
  O_{X,x}-module and supplies its scalar action to tensor formation. It is not a new
  node or dependency repair. Apart from this allowed addition to `stmt_deps`, the
  item's node copy changes only its `lean` record.

Edge cases checked before writing: F = 0 has empty support, zero residue fibres and
zero pullback; an empty X has vacuous point assertions and any Y mapping to it is
empty; an empty Y gives empty pullback support and empty inverse image; f = identity
recovers the original support. The tensor nonvanishing criterion requires precisely
the stated finite type hypothesis (Nakayama), not coherence or a Noetherian scheme.
Arbitrary residue characteristics are admitted. The single explicitly bound universe
u ranges over all scheme/module sizes supported by the project's existing encoding;
there is no small test-object universe or restricted affine/finite-type source Y.

Searches performed through `/home/ubuntu/weil-launcher/msearch.py` with group T1 and
this item:

- `leansearch`: `finite type quasi coherent module support closed pullback preimage`:
  service unavailable, Internal Server Error; no mathematical verdict assigned.
- `leanfinder`: `The support of a finite type quasi-coherent sheaf is closed and its
  pullback support equals the preimage`: 8 hits, all ideal-sheaf support results
  (`IdealSheafData.support_map`, `support_comap`, etc.), not this module statement.
- `loogle`: `SheafOfModules.IsFiniteType, Subsingleton`: 0 hits.
- `grep`: `support.*pullback|support.*finiteType|support.*finite_type` in
  `AlgebraicGeometry`: one hit in ideal-sheaf functoriality, not a match.
- `rg -n` with the same support patterns and the item id in the source
  `WeilConjectures` and project `lean/Sheaf`: ideal-sheaf, étale and compact-support
  results, plus citations of this item in ProperSupportDescent and
  ClosedImmersionPushforwardAnnihilated; no existing full statement.
- `grep -rn` of the exact item id in source `WeilConjectures`: no hits.
- `rg -n` of `finiteType_module_support_pullback|FiniteTypeModuleSupportPullback` in
  `dag/lean_names_upstream.json`, Mathlib, source and project Lean: no hits, so the
  new declaration does not collide with an existing declaration.

Validation: the server compiled the final module cleanly (2.7 seconds, exit 0).
The initial compilations exposed scalar-instance inference failures; these were fixed
by using the recorded bundled module stalk and explicitly restricting the residue
field's self-module structure through `Scheme.residue`. No hypotheses or clauses
changed. Every universe and variable is explicitly bound. No statement dispute or
statement correction is needed. The docstring carries all eight DAG proof steps and
names their dependencies. The independent second reading is left to the second reader.

## Second reading by T1

I independently compared the node statement with the module declaration
`AlgebraicGeometry.Scheme.Modules.finiteType_module_support_pullback`.

- Objects: the Lean binders `{X : Scheme.{u}}` and `F : X.Modules` render the
  scheme and its O_X-module; `[F.IsQuasicoherent]` and `[F.IsFiniteType]`
  render the two hypotheses. For each `x : X`, `F.presheaf.stalk x` is the
  stated stalk, `X.residueField x` is κ(x), and the bundled
  `RingedSpace.moduleStalkFunctor` supplies the required O_{X,x}-module
  structure. For `(Y, f)`, `Y : Scheme.{u}` and `f : Y ⟶ X` render an arbitrary
  scheme morphism, and `tensorPullback f` is the recorded module pullback.
- Clause (1): `IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)}` is exactly
  closedness of the support defined as the nonzero-stalk locus.
- Clause (2): `∀ x`, the first equivalence is membership in that support and
  nonzero stalk; the second is nonzero stalk iff nonzero
  `@TensorProduct (X.presheaf.stalk x) ... (X.residueField x) ...`, i.e.
  `F_x ⊗_{O_{X,x}} κ(x)`. Both equivalences and their order are present.
- Clause (3): `((tensorPullback f).obj F).IsFiniteType` gives finite type of
  `f^*F`, followed by exact equality between its nonzero-stalk support and
  `f ⁻¹'` the support of F. No extra morphism or finiteness hypothesis occurs.

The source is Stacks Project, Morphisms of Schemes, Lemma 056J. Its hypotheses
are precisely finite type and quasi-coherence on a scheme, and its three
conclusions are the clauses above. The empty module has empty support and zero
fibre; empty schemes and empty inverse images make the pointwise clauses
vacuous; identity pullback recovers the original support; no characteristic or
Noetherian restriction is introduced. The single universe `u` is the scheme
universe used by the existing `Scheme` and module declarations.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` using LeanSearch,
LeanFinder/Loogle, and `rg` for support, finite-type module, and pullback
patterns. Only ideal-sheaf support results were found; no declaration states
this theorem. The dependency declarations were opened, including the recorded
`tensorPullback` and `RingedSpace.moduleStalkFunctor`; no private replacement
or hollow definition is present. The worker's module and node required no
repair, so no mismatch was changed.
