## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleMixedIntersectionPositive` states
`AlgebraicGeometry.Scheme.Modules.intersectionNumber_pos_of_isAmple`, with `sorry`.
Its source is Stacks Varieties Tag 0BEV, `lemma-ample-positive`, specialized to
its closed subscheme being the ambient scheme. I read that statement and proof
in `literature/stacks-project/varieties.tex`, together with Definition 0BEP.
No definition, new node, dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- A field k: `(k : Type u) [Field k]`.
- A k-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Nonempty: `[Nonempty X]`.
- Proper over k: `[IsProper (X ↘ Spec (.of k))]`.
- Dimension d at least one: `(d : ℕ) (_hd : 1 ≤ d)` and
  `(hdim : topologicalKrullDim X = ((d : ℕ∞) : WithBot ℕ∞))`.
- The d invertible modules: `(L : Fin d → X.Modules)` and
  `[∀ j : Fin d, (L j).IsInvertible]`.
- Each module is ample in the absolute affine-nonvanishing-open sense:
  `(_hL : ∀ j : Fin d, IsAmple X (L j))`, where this resolves to
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- The strictly positive intersection with X:
  `0 < intersectionNumber k X X (𝟙 X) d hdim L`.
  The identity is a closed immersion by the existing instance, and the ambient
  and closed schemes are both X, exactly as required. The intersection number is
  the existing rational coefficient of the squarefree degree-d monomial.
- The modules may differ: L is an arbitrary family, with no equality constraints.
  The last sentence permits nonreduced, nonintegral, nonequidimensional, and
  nonsmooth schemes: none of the corresponding structural assumptions occurs.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the public imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper`, on the structure morphism.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (publicly available through Ample).
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.IntersectionNumber`:
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber`.

The recorded statement dependencies are all usable as given. In particular,
absolute `Scheme.Modules.IsAmple X L` is used, rather than the different upstream
`AlgebraicGeometry.IsAmple f L`. The latter can occur in proof dependencies,
without changing the meaning of this statement. The existing intersection
construction chooses its polynomial from its uniquely characterizing evaluations;
this module does not introduce any choice or polynomial data of its own.

The module imports the recorded, already stated proof dependencies without
`public`. The unstated proof-only node `lem-sfb-top-intersection-multilinear` has
no recorded declaration or module, so its import cannot yet be added. It is
explicitly named in the seven-step proof docstring, for the later proof stage.
Mathlib's proper, finite, affine and closed-immersion facts are available through
the imports, including ZariskisMainTheorem. No proof import was omitted for a cycle.

Edge cases checked before writing: d = 0 is excluded by the node itself; d = 1
retains exactly one ample invertible module and asserts positive degree. Empty X
is excluded explicitly. Nonreduced schemes retain nilpotent multiplicities in the
existing Euler-polynomial definition. Reducible and nonequidimensional schemes
are allowed, with no condition on lower-dimensional components. There is no
algebraic-closedness, perfectness, or characteristic assumption on k. Repeated
bundles are allowed as a constant family, and different bundles remain allowed.
The common universe u follows the dependency API and is arbitrary, allowing any
field/scheme pair after a common universe enlargement. There is no independent
small testing universe or quantification over auxiliary schemes.

Searches actually run with the required wrapper:

- LeanFinder: `The mixed intersection number of d ample invertible sheaves on a
  nonempty proper scheme of dimension d over a field is positive`.
  Eight unrelated hits (number-field Minkowski positivity, height positivity,
  Chevalley bounds, and a simplicial-set pairing); no match.
- LeanSearch: `Ample invertible sheaves on a nonempty proper scheme have positive
  mixed intersection number`. Eight hits about proper morphisms, integral schemes,
  and ideal-sheaf intersections; no mixed intersection positivity result.
- Loogle: `"intersection", "ample"`. Zero hits.
- Mathlib grep: `intersectionNumber|mixedIntersection|intersection_number`.
  Zero hits.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `mixed.*intersection|intersection.*(positive|pos)|ample.*intersection|intersectionNumber`
  (case insensitive). Found the existing intersection definition, component
  reduction, Cartier restriction and pullback statements, and unrelated textual
  matches; none states this mixed positivity theorem. Upstream degree positivity
  in `Modules.Ample` concerns a single repeated line bundle, not mixed intersections.
- Upstream grep for the exact node id: zero hits.
- Name collision rg in `dag/lean_names_upstream.json`, upstream and Sheaf for
  `intersectionNumber_pos_of_isAmple|intersectionNumber_pos`: zero hits.

No STATEMENT-DISPUTED issue or own-node fault was found. The example
`CompactObject.lean` is currently withdrawn; the required module-mode header,
public dependency imports, exposed public section, and source/blueprint docstrings
follow the standing brief. All variables are explicit and autoImplicit is disabled.

Validation: scompile.py passed in both sandbox and library module modes. The
required deliver2.py --no-push then reported OK: preflight and per-file compilation
passed, with no compiler errors or unexpected warnings.

## Second reading by Q122

I reread the node and the completed declaration directly, checking the conclusion
against Definition 0BEP with i equal to the identity. `Field k` matches the field;
`Over` supplies the specified structure map; `IsProper` is on that very map;
`Nonempty X` excludes precisely the empty case; d is a natural number with the
stated lower bound and exact Krull dimension equality. The family has exactly d
members, each is invertible and satisfies the recorded absolute ampleness notion.
The conclusion compares the existing mixed intersection coefficient with zero
using strict order on ℚ. The final permission for different bundles and arbitrary
scheme singularities imposes no extra Lean hypotheses. I checked that the proof
imports' separate relative IsAmple name is not selected by the local namespace.
No mismatch or signature change was needed. This is the dispatcher's single
worker rereading; the maintainer supplies the independent delivery review.
