## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeRelativePerfectBaseChange` states
`AlgebraicGeometry.Scheme.relativePerfect_baseChange`, with exactly one postponed
proof (`sorry`). It introduces no definitions. The existing node is changed only
in `lean`; its statement, dependency lists, and reviewed stage-1 proof are preserved.
The docstring records the five proof steps and their named prerequisites.

Source read: `literature/stacks-project/perfect.tex`, definition-relatively-perfect
(Tag 0DI0, lines 8702 onward), lemma-affine-locally-rel-perfect (0DI2), and
lemma-base-change-relatively-perfect (0DI5, lines 8804 onward). The source writes
S' ×_S X; the node chooses the canonically isomorphic X ×_S S'. The Lean follows
the node's order, with the projections typed accordingly.

The hypothesis and conclusion correspondence is as follows.

| Node clause | Lean rendering |
| --- | --- |
| Schemes X, S, S' and f : X → S | `{X S S' : Scheme.{u}} (f : X ⟶ S)` |
| Flat f | `[Flat f]` |
| Locally finitely presented f | `[LocallyOfFinitePresentation f]` |
| Arbitrary g : S' → S | `(g : S' ⟶ S)`, with no property imposed on g |
| X' = X ×_S S' | `pullback f g` |
| b : X' → X | `pullback.fst f g` |
| f' : X' → S' | `pullback.snd f g` |
| Zariski structure sheaves and unbounded D(O_X) | `moduleRings Z.toRingedSpace`, `schemeDerivedCategory X`, and the imported definitions; no boundedness subcategory |
| E in D(O_X) | `(E : schemeDerivedCategory X)` |
| E pseudo-coherent | `(hE : IsPseudoCoherent X E)` |
| At each x, an open neighbourhood with finite Tor dimension over S | `hTor : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ HasFiniteTorDimensionOver (U.ι ≫ f) ((derivedPullback U.ι).obj E)` |
| Lb*E pseudo-coherent | First conjunct `IsPseudoCoherent (pullback f g) ((derivedPullback (pullback.fst f g)).obj E)` |
| Lb*E locally has finite Tor dimension over S' | Second conjunct quantifies `∀ x', ∃ U', x' ∈ U' ∧ HasFiniteTorDimensionOver (U'.ι ≫ pullback.snd f g) ((derivedPullback U'.ι).obj ((derivedPullback (pullback.fst f g)).obj E))` |
| No global uniform Tor interval | Each occurrence of `HasFiniteTorDimensionOver` is inside the existential neighbourhood for each point |
| No flatness of g, Noetherianity, or properness | None of these hypotheses occurs |

Restriction to an open is the existing derived pullback along its open immersion.
Such an immersion has exact module restriction; therefore this is precisely the
restriction of the complex required in the node. `HasFiniteTorDimensionOver`
restricts scalars along the actual inverse-image structure-ring map and tests a
K-flat resolution against every inverse-image-base module sheaf. It is not
absolute finite Tor dimension on X, nor a test only against pullbacks of modules
from S. It contains its own finite interval, independently at every open.

The two `HasDerivedCategory.{w}` instance families are localization infrastructure
for schemes and their localized open sites, exactly as in the recorded definitions
and the existing relative-dualizing-pair consumer. They impose no geometric
condition, identify no independent universes, and can be supplied using standard
derived localizations in a sufficiently large universe. The module explicitly
binds `u`, `w`, every scheme, morphism, point and open, and disables auto-implicits.

Statement dependencies read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme (via the public flatness/pullback imports) | AlgebraicGeometry.Scheme, Scheme.Hom |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback (via Mathlib.AlgebraicGeometry.Pullbacks) | CategoryTheory.Limits.pullback, pullback.fst, pullback.snd |
| def-pc-derived-category | WeilConjectures.AlgebraicGeometry.DerivedCategory | AlgebraicGeometry.schemeDerivedCategory |
| def-pur-pseudo-coherent-complex | WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex | AlgebraicGeometry.Scheme.IsPseudoCoherent |
| def-pc-finite-tor-dimension-over | Sheaf.AlgebraicGeometry.FiniteTorDimensionOver | AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver |
| def-pc-derived-pullback | WeilConjectures.AlgebraicGeometry.DerivedPullback | AlgebraicGeometry.derivedPullback |

The recorded finite-Tor dependency was read both locally and through
`scompile.py --source Sheaf.AlgebraicGeometry.FiniteTorDimensionOver`; the live
source agrees. It is used as recorded. There is an upstream same-named variant;
this delivery does not import that variant or create a third definition.
The module uses public imports for statement material and ordinary imports for
all available recorded proof prerequisites, including Mathlib matches. These are
listed verbatim in the module. The proof-only affine, stalk, flat-model, tensor
comparison and pullback-composition modules compile together in module mode.
No proof import has been omitted, and no new node or dependency repair is needed.

Edge cases checked before writing:

- Empty X: pseudo-coherence and the neighbourhood quantifier are vacuous;
  its base change is empty. Empty X' likewise makes both conclusions local and
  vacuous. No nonemptiness assumption appears.
- E = 0: use the zero bounded-above finite-free model and Tor interval [0,0];
  derived pullback preserves zero.
- Identity g: the projection is an isomorphism and both properties transport.
- Non-flat base change: take R = Z, A = Z[t], R' = Z/2. For the structure complex
  the same interval [0,0] persists, despite g not being flat. This case is included.
- Nonuniform bounds: on an infinite disjoint union of points over a field, put a
  free rank-one complex in degree n on the nth component. It is locally relatively
  perfect with no global interval; the `∀ point, ∃ open` form includes it.
- General schemes: neither quasi-compactness nor separatedness is assumed, and no
  finite cover, Noetherian condition, fixed dimension, or characteristic occurs.

Searches for an existing assertion (2026-10-24):

1. `msearch.py ... leanfinder`, query: "Derived pullback preserves pseudo coherent
   complexes with locally finite relative Tor dimension under arbitrary base
   change of a flat locally finitely presented scheme morphism". Eight hits,
   led by `AlgebraicGeometry.Flat.isStableUnderBaseChange` and
   `AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange`;
   only ordinary geometric morphism properties, not this derived assertion.
2. `msearch.py ... loogle`, query:
   "AlgebraicGeometry.Scheme.IsPseudoCoherent, AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver".
   Zero hits; the service reports unknown identifier for the project-specific
   pseudo-coherence definition.
3. `msearch.py ... grep`, query:
   "IsPseudoCoherent|HasFiniteTorDimensionOver|[Rr]elatively[Pp]erfect", in
   Mathlib/AlgebraicGeometry. Zero hits.
4. `msearch.py ... leansearch`, query: "Relative perfection of scheme complexes
   is preserved under arbitrary base change for a flat locally finitely presented
   morphism". Eight hits, including `RingHom.Flat.isStableUnderBaseChange` and
   ordinary scheme finite-presentation/flatness results; no derived relative
   perfection theorem.
5. `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf`, patterns
   `lem-sfb-scheme-relative-perfect-base-change`, `IsPseudoCoherent.*base`,
   `[Rr]elativ.*[Pp]erfect.*[Bb]ase`, and `HasFiniteTorDimensionOver`.
   Found the dependency definitions, the matching local-Tor predicate in
   `RelativeDualizingPair.lean`, and references to the item in the base-change
   consumer's proof docstring. Found `SpaceRelativePerfectBaseChange.lean`, which
   concerns algebraic spaces and a different etale-site notion. No theorem for
   this scheme/Zariski assertion. A separate `grep -rn` for this node id in
   `lean/WeilConjectures` returned no match. The new declaration name was also
   checked against both roots and `dag/lean_names_upstream.json`, with no match.

Validation: the prescribed `scompile.py Q133 lem-sfb-scheme-relative-perfect-base-change`
compiled the module cleanly in both its sandbox and library-module modes. The
only proof body is the requested `sorry`. No statement dispute or source defect
was found. The delivery dry run is performed after writing this report.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
