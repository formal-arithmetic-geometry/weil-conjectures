## Worker report

The module states `AlgebraicGeometry.Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected`
with a `sorry` proof. It uses the existing structure map and geometric predicates; it defines
no new notion. The node's five proof steps are included in the theorem docstring.

Hypotheses and clauses:

- The field `k` is `(k : Type u) [Field k]`.
- The scheme `X` over `k`, including its structure morphism, is
  `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; `X ↘ Spec (.of k)` is `f`.
- Properness of `f` is `[IsProper (X ↘ Spec (.of k))]`.
- Geometric reducedness is `[GeometricallyReduced (X ↘ Spec (.of k))]`.
- `A = H^0(X, O_X) = Gamma(X, O_X)` is the codomain of `globalSectionsRingHom k (X := X)`.
  This map is the node's `rho`, induced by the structure morphism through the canonical
  isomorphism between `k` and the sections of `Spec k`.
- `H^0(X, O_X) = k` means `Function.Bijective (globalSectionsRingHom k (X := X))`.
- The two directions are joined by `↔`; geometric connectedness is
  `GeometricallyConnected (X ↘ Spec (.of k))`. Mathlib defines it by connectedness of every
  base change along `Spec K → Spec k` for a field `K`.

Dependencies used: `Field` (Mathlib); `AlgebraicGeometry.Scheme.Over` from
`Mathlib.AlgebraicGeometry.Over`; `AlgebraicGeometry.Spec` from
`Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.IsProper` from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; `AlgebraicGeometry.GeometricallyReduced` from
`Mathlib.AlgebraicGeometry.Geometrically.Reduced`;
`AlgebraicGeometry.GeometricallyConnected` from
`Mathlib.AlgebraicGeometry.Geometrically.Connected`; and
`AlgebraicGeometry.Scheme.globalSectionsRingHom` from
`WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective` (the only direct import).
`AlgebraicGeometry.Scheme` is Mathlib's scheme type.

Edge cases: the empty scheme is geometrically reduced and proper, but its global-sections
ring is the zero ring, so `rho` is not bijective and its geometric base changes are not
connected in Mathlib's sense. The zero ring cannot be `k`, since `[Field k]` requires
`0 ≠ 1`. No nonemptiness hypothesis was added. The theorem quantifies over an arbitrary
field and scheme universe, without excluding characteristic or field extensions.

Searches: `msearch.py leanfinder` for the full equivalence returned only nearby facts,
including `isField_of_universallyClosed`, which assumes integrality and does not identify
global sections with `k`. `msearch.py loogle` for `GeometricallyConnected` and
`GlobalSectionsBijective` returned no match (the source-only latter name is unknown to
Loogle). `msearch.py grep` in Mathlib AlgebraicGeometry for global sections with geometric
connectedness returned zero hits. `rg` in `WeilConjectures` and `lean/Sheaf` found the
source's `GlobalSectionsBijective.of_geometricallyConnected` and `.connectedSpace`, but no
equivalence. `rg` for this node id found no existing source declaration. The source
checkout's definition of `GlobalSectionsBijective` is exactly bijectivity of the map
used here; its forward direction theorem has the same properness and reducedness
hypotheses. The local repository does not contain the downloaded Stacks or blueprint
source files; the node's source and proof text were read from its DAG record.

Server compilation: clean (`scompile.py`, exit code 0).

## Second reading by H1

I read the node and Stacks `varieties.tex`, Lemma 0FD2
(`lemma-geometrically-reduced-stein`). Its standing assumptions are exactly a field and a
proper, geometrically reduced scheme over that field; its conclusions are the equivalence
of `H^0(X,O_X) = k` and geometric connectedness. The node makes the structure map behind
the first equality explicit.

- Field `k`: `(k : Type u) [Field k]`. Mathlib's `Field` includes `0 != 1`; no
  characteristic restriction is added.
- Scheme `X` and structure morphism `f : X -> Spec k`: `(X : Scheme.{u})
  [X.Over (Spec (.of k))]`, with `f` rendered by `X ↘ Spec (.of k)`. This is the
  `Scheme.Over` declaration recorded by `def-weil-scheme-over-base`; `Spec (.of k)` is
  Mathlib's spectrum used by `def-weil-affine-spectrum`.
- Proper `f`: `[IsProper (X ↘ Spec (.of k))]`. The `def-weil-proper-morphism` match
  records that Mathlib's `IsProper` is equivalent to separated, finite type, and
  universally closed: universal closedness supplies quasi-compactness.
- Geometrically reduced `X/k`: `[GeometricallyReduced (X ↘ Spec (.of k))]`.
  The four geometric predicates described by `def-pc-geometrically-irreducible` are
  separate Mathlib classes; this one demands reducedness after every field base change.
- `A = H^0(X,O_X) = Gamma(X,O_X)` and its `k`-algebra map `rho`:
  `globalSectionsRingHom k (X := X)` is the structure morphism's map into the
  structure sheaf's global sections. The source's `GlobalSectionsBijective` class has
  precisely its `Function.Bijective` as a field, confirming the same map and codomain.
- First conclusion `H^0(X,O_X) = k`: `Function.Bijective
  (globalSectionsRingHom k (X := X))`; this identifies the global-sections ring through
  `rho`, as the node specifies, rather than claiming literal type equality.
- Second conclusion, for every field extension the base change is connected:
  `GeometricallyConnected (X ↘ Spec (.of k))`. Its Mathlib definition quantifies over
  all `Spec K -> Spec k` with `K` a field, as described in the geometric dependency node.
  The two conclusions have the node's order and are linked by `↔`.

Edge cases: Mathlib `ConnectedSpace` includes `Nonempty`, so the empty scheme satisfies
neither side: its global-sections ring is zero and a field cannot map bijectively to it.
No nonempty, positive-dimensional, Noetherian, or characteristic hypothesis was added.
The theorem is polymorphic in `u`; `Spec (.of k)` and `X` share the scheme universe,
the Mathlib convention for morphisms. The zero ring is excluded only because the node
requires a field. There is no index set or integer parameter in this statement.

Independent searches: `msearch.py leanfinder` for the proper geometrically reduced
global-sections equivalence found `isField_of_universallyClosed`, which assumes
integrality and only gives a field; `msearch.py loogle` for the equivalence had no hit
(its service reported `GeometricallyConnected` unknown); `msearch.py grep` for the map
with geometric connectedness had no hit. `rg` over Mathlib, the slopmaster2
`WeilConjectures` tree, and repository `lean/Sheaf` found no full equivalence.
The source module has `GlobalSectionsBijective.of_geometricallyConnected` for one
direction and separate results for the other; neither states this node's `↔`.

Mismatch found: none. Changes: replaced the placeholder reading with this review;
the Lean statement, its docstring and proof-only `sorry`, and the node's verbatim
`lean.statement` already matched the source and node. No new definition or dependency
module is needed.
