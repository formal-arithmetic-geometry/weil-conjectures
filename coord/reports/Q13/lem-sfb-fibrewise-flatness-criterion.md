## Worker report

This is the stage-2 statement of `lem-sfb-fibrewise-flatness-criterion`, in
`lean/Sheaf/AlgebraicGeometry/FibrewiseFlatnessCriterion.lean`. The sole declaration is
`AlgebraicGeometry.Scheme.Hom.flatAt_and_base_flatAt_of_fiber_flatAt`; its proof is `sorry`.
There are no definitions, helpers, additional nodes, dependency repairs, or statement changes.
The node copy changes only `lean`.

The previous retry confused the NO stage-1 merge with completion of stage 2. The shared node
has `reviewed` from that proof split but no `lean` or `reviewed_lean`. The NO report is a
natural-language proof split, not a Lean statement. This delivery supplies the missing statement.

I read the full node and every statement dependency, their recorded declarations and docstrings,
and Stacks `more-morphisms.tex`, theorem-criterion-flatness-fibre (039C), statement and proof.
The statement is exactly implication (1) to (2) for F = O_X. The sheaf is quasi-coherent and
finitely presented over itself, and its stalk at a point is nonzero. Thus the original source's
nonzero-stalk condition requires no additional hypothesis. The source's openness conclusion
is not part of this node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes S, X, Y | `{S X Y : Scheme.{u}}`, for arbitrary explicitly bound universe `u` |
| Morphisms p : X -> S, q : Y -> S, f : X -> Y | `(p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)` |
| q composed with f equals p | `(hf : f ≫ q = p)`, using diagrammatic composition |
| p locally of finite presentation | `[LocallyOfFinitePresentation p]` |
| q locally of finite type | `[LocallyOfFiniteType q]` |
| Fixed point x | `(x : X)` |
| y = f(x), s = p(x) | Written directly as `f x` and `p x`, without extra binders |
| X_s and Y_s are scheme-theoretic fibres | `pullback p (S.fromSpecResidueField (p x))` and the same expression with `q`, definitionally `p.fiber (p x)` and `q.fiber (p x)` |
| The induced map f_s | `pullback.map p (S.fromSpecResidueField (p x)) q (S.fromSpecResidueField (p x)) f (𝟙 _) (𝟙 S) ... ...` |
| x as its corresponding point of X_s | `p.asFiber x`, defined by the inverse of `p.fiberHomeo (p x)` |
| p flat at x | `(hp : (p.stalkMap x).hom.Flat)` |
| f_s flat at x | `hfs`, the `.hom.Flat` predicate on that canonical map's `.stalkMap (p.asFiber x)` |
| f flat at x | First conjunct `(f.stalkMap x).hom.Flat` |
| q flat at y | Second conjunct `(q.stalkMap (f x)).hom.Flat` |

The pullback map's first commutativity witness is the equation `p = f ≫ q`, obtained
from `hf.symm` after removing composition with the identity. Its second witness is the
identity square on `S.fromSpecResidueField (p x)`. These prove the input diagram commutes;
they introduce no additional assumptions. `pullback.map` has the canonical projection
composites, so its point over `x` maps to the unique point of Y_s over `f x`. No arbitrary
fibre map or isomorphism is supplied by the caller.

Statement dependency declarations (all their modules are public imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; `Scheme.Hom.stalkMap` is the actual local-ring map.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`. Its quasi-compactness clause is not a hypothesis
  of this node, so no quasi-compactness hypothesis is added.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`. The fibre objects in
  the canonical map's type are definitionally these chosen fibres.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback` and
  `pullback.map`. Scheme pullbacks are already provided by the imported fibre module.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`, which identifies the recorded flatness
  notion with the pointwise `.hom.Flat` predicates used here. Their ring-map predicate
  is `RingHom.Flat`, imported through this module; it fixes the scalar action to the
  given stalk map.

Proof-dependency imports are plain imports, retaining the future proof plan:

- `lem-weil-pbc-scheme-stalk-map-composition`: `Scheme.Hom.germ_stalkMap` and
  `stalkMap_comp` in the already public `Mathlib.AlgebraicGeometry.Scheme`.
- `lem-sbc-scheme-fibre-stalk-quotient`:
  `Sheaf.AlgebraicGeometry.FibreStalkQuotient`,
  `Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`.
- `lem-weil-pbc-affine-open-stalk-localization`:
  `Mathlib.AlgebraicGeometry.AffineScheme` and `Mathlib.AlgebraicGeometry.OpenImmersion`;
  `IsAffineOpen.isLocalization_stalk`, the affine open maps, and their stalk isomorphisms.
- `lem-weil-pbc-finite-presentation-base-change-composition`:
  `Mathlib.RingTheory.FiniteStability` (`Algebra.FinitePresentation.baseChange`);
  `Algebra.FinitePresentation.trans` is available through the finite-presentation imports.
- `lem-weil-pbc-localization-of-localization`:
  `Mathlib.RingTheory.Localization.LocalizationLocalization`,
  `IsLocalization.localization_localization_isLocalization` and
  `IsLocalization.isLocalization_of_submonoid_le`.
- `def-weil-pbc-essentially-finite-type-algebra`:
  `Mathlib.RingTheory.EssentialFiniteness`, `Algebra.EssFiniteType`.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType`.
- `lem-weil-pbc-criterion-flatness-fibre`:
  `WeilConjectures.RingTheory.FlatOfFlatClosedFiber`, `Module.flat_of_flat_closedFiber`.
- `lem-pc-local-flat-faithful-flat-reflects-surjective` and
  `lem-weil-pbc-faithfully-flat-universally-injective`:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` and `.Basic`, especially
  `Module.FaithfullyFlat.of_flat_of_isLocalHom` and `tensorProduct_mk_injective`.
- `def-weil-pbc-flat-ring-map`: `RingHom.Flat`, already public through the flatness import.
- `lem-sfb-finite-type-local-closed-fibre-approximation` has no recorded Lean declaration
  yet, so there is no module to import for this proof-only dependency. Its invocation is
  preserved in step 5 of the theorem docstring. No missing notion is needed to state the item.

Edge cases checked before writing:

- Empty X: the fixed binder `x : X` makes the implication vacuous, as in the node.
  Empty S or Y likewise cannot occur in a pointed input diagram. No nonemptiness hypothesis
  is added to any scheme.
- Identity structure maps and identity f: the canonical pullback map reduces up to the
  standard identity pullback isomorphisms, and the resulting flatness conclusions hold.
- Nonclosed x and s are included; `asFiber` is defined for every point.
- Non-Noetherian and nonreduced bases are included. q is only locally of finite type;
  it is not required to be finitely presented or flat away from f(x).
- hp and hfs concern one point, not global flatness of p or f_s. Both conclusions are
  pointwise as well. There is no surjectivity, separatedness, openness or compactness clause.
- All schemes have arbitrary common universe `u`, as in Mathlib's category of schemes;
  no test-object quantifier can become vacuous through an independently smaller universe.
- The structure-sheaf stalk is a nonzero local ring at every actual scheme point, so the
  source's nonzero module condition is automatic, including in characteristic zero or p.

Searches performed using the prescribed wrappers and read-only sources:

- `msearch.py ... leansearch "Pointwise fibre criterion flatness morphism of schemes
  finitely presented source finite type target"`: eight hits, including `Scheme.Hom.fiber`,
  `Flat.of_stalkMap`, `Flat.iff_flat_stalkMap`, the finite-presentation class, finite-fibre
  and locality lemmas. None states the fibre criterion.
- `msearch.py ... leanfinder "Pointwise fibre criterion for flatness of a morphism of
  schemes, source locally finitely presented over the base and target locally finite type,
  flat at a point over the base and flat on the fibre imply flatness at that point"`:
  eight hits on `Flat`, `Flat.of_stalkMap`, `Flat.iff_flat_stalkMap`, its instances,
  `UniversallyOpen.of_flat`, and base-change stability; none is the requested statement.
- `msearch.py ... loogle '"Flat", "fiber"'`: zero hits.
- `msearch.py ... grep
  'flat.*[Ff]iber|flat.*[Ff]ibre|[Ff]iber.*flat|[Ff]ibre.*flat|criterion.*flat'
  AlgebraicGeometry`: three hits in `Morphisms/SmoothFiber.lean`, all assuming flatness
  to infer smoothness. No criterion deducing flatness.
- `rg` with the same fibre/flatness patterns in the project's `WeilConjectures` and
  `Sheaf` sources, plus narrower `039C|criterion.*flatness.*fib|flat.*of.*fib` searches:
  polynomial-chart flatness comparisons concern a specific affine polynomial chart with
  already flat source; they do not give this general diagram or target-flatness conclusion.
  The consumer `Sheaf.AlgebraicGeometry.RelativeFlatLocusBaseChange` cites this node in
  its proof docstring, but only states openness/base-change of a global flat locus.
  Other hits concern smoothness, fibre dimension, fibre degree, or generic fibres.
- `grep -rn 'lem-sfb-fibrewise-flatness-criterion' lean/WeilConjectures`: no matches.
- A search for existing fibre-map definitions found only specialized polynomial,
  geometric, and cohomological maps; the statement uses Mathlib `pullback.map` directly.
- `rg` of `dag/lean_names_upstream.json` and both source trees found no declaration with
  the new theorem name. The earlier searches in the node are preserved unchanged.

Validation: `scompile.py Q13 lem-sfb-fibrewise-flatness-criterion` compiled the delivered
file in both sandbox and library module contexts cleanly (10.7 s and 6.5 s). No warnings
or errors were printed. The only postponed proof is the named theorem. The recorded
signature is copied verbatim from the file; the node differs from the shared copy only in
`lean`.

No mathematical node fault or statement dispute was found. No new definition is necessary.

## Second reading by Q13

The dispatcher explicitly prohibits starting another agent and assigns the independent review
to the maintainer. I therefore do not claim an independent second worker reviewed this file.
For this delivery I reread the node, the finished signature, and the source theorem against
the table above. In particular I rechecked the orientation of `hf.symm` in `pullback.map`,
the exact canonical fibre point `p.asFiber x`, the actual stalk map in hfs, and both separate
pointwise flatness conclusions. No mismatch or statement correction was found.
