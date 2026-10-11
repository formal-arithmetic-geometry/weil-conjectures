## Worker report

Recorded the existing declaration
`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`, in
`WeilConjectures.AlgebraicGeometry.Curve.Picard`, lines 214–246 of the read-only
slopmaster2 checkout. Its docstring explicitly names this blueprint node. No module or
second definition is needed. The candidate already recorded by stage 1 is usable for
stage 2 even though its degree homomorphism has sorried dependencies: this delivery does
not claim a completed proof. Only the item's `lean` field changes.

Hypotheses and clauses, checked against the declaration and its enclosing sections:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Curve over that field: `{C : Scheme.{u}} [C.Over (Spec (.of k))]` gives the scheme and
  its structure morphism. The node's separated finite-type condition is covered by
  `IsProper (C ↘ Spec (.of k))`.
- Smooth connected one-dimensional curve: `SmoothOfRelativeDimension 1` expresses
  smoothness with pure dimension one. In the node's connected dimension-one setting
  this is precisely smoothness of the curve. Connectedness is not needed by the
  existing theorem; its `[Nonempty C]` hypothesis follows from
  `AlgebraicGeometry.IsConnectedCurve.nonempty`. Thus the existing result specializes
  to every connected curve in the node, without changing the node's hypotheses.
- Properness: `[IsProper (C ↘ Spec (.of k))]`.
- Picard group: `C.Pic`, the dependency's existing group of invertible sheaf classes,
  with tensor product written multiplicatively.
- Degree and Picard-zero: `picDegreeHom k C` and `(picDegreeHom k C).ker`.
  `picDegreeHom_toPic` says its value on `O(D)` is `Multiplicative.ofAdd (Divisor.degree C D)`;
  `coe_ker_picDegreeHom` identifies the kernel, as a subset of `C.Pic`, with the
  dependency's `(C ↘ Spec (.of k)).picZero`.
- Splitting and decomposition: `∃ e : C.Pic ≃* Multiplicative ℤ × (picDegreeHom k C).ker`.
  For two abelian groups the product realizes their finite direct sum. The type tag
  `Multiplicative` changes notation, not the integer group.
- It splits the degree sequence, rather than merely giving an abstract isomorphism:
  `∀ L, (e L).1 = picDegreeHom k C L`. The inverse applied to `(n, 1)` gives a
  homomorphic section of degree. Consequently degree is surjective, and exactness at
  Pic is the defining kernel condition; the kernel inclusion is injective.
- Rational-point explanation: the existing source's `picDegreeHom_ofClosedPoint`
  gives degree one for `Pic.ofClosedPoint k P`. Its theorem proof first obtains a
  degree-one class with `surjective_picDegreeHom`, then constructs the section by
  `zpowersHom`. This is the node's explanation, not an additional premise requiring
  a chosen point in the theorem signature.

Dependencies read with their full signatures and docstrings:
`def-sc-curves` records `AlgebraicGeometry.IsCurve` in
`WeilConjectures.AlgebraicGeometry.Curve` (lines 68–104 also give
`IsConnectedCurve` and its nonemptiness lemma);
`def-sc-picard-group` records `AlgebraicGeometry.Scheme.Pic` in
`WeilConjectures.AlgebraicGeometry.PicardFunctor` (lines 159–168);
`def-sc-pic0` records `AlgebraicGeometry.Scheme.Hom.picZero` in
`WeilConjectures.AlgebraicGeometry.Curve` (lines 133–169).
The existing Picard module supplies the homomorphism and the two compatibility
lemmas above. The subset record for Pic-zero is usable through its established
identification with the kernel subgroup; no dependency module is necessary.

Edge cases: an empty curve is excluded by the node's connected-curve definition,
and by the existing theorem's nonemptiness premise; degree cannot be surjective on
an empty curve. `Spec k` is excluded by the dimension-one condition. Arbitrary positive
characteristic is allowed (`Field` and `IsAlgClosed`, with no characteristic-zero
hypothesis). Both positive and negative degrees and degree zero are covered by ℤ and
integer powers. No rational point is chosen as extra input. Universe `u` is explicit
and arbitrary; Pic lives in `Type (u + 1)` as in its existing definition. The broader
disconnected pure-dimension-one case allowed by the existing theorem is not asserted
as a correction of this node.

Searches actually run using `/home/ubuntu/weil-launcher/msearch.py`:

- LeanSearch: "Picard group proper smooth curve degree homomorphism splits kernel integers".
  Service returned Internal Server Error, recorded as unavailable, not no match.
- LeanFinder: "Picard group of a smooth proper connected curve over an algebraically closed
  field splits as integers times kernel of degree". Eight hits: elliptic-curve point
  class maps, relative Picard groups of rings, function-field class numbers; none is
  the scheme-theoretic statement.
- Loogle: `Function.Exact.splitSurjectiveEquiv`. One hit, the general linear exact-sequence
  splitting, not the geometric degree-surjectivity statement.
- Mathlib grep: `picDegreeHom|Picard.*degree|picZero|exists_mulEquiv_prod_ker`. Zero hits.
- Source `rg` with `picDegreeHom|exists_mulEquiv_prod_ker|lem-sc-pic-proper-decomposition`
  in `WeilConjectures/AlgebraicGeometry/Curve/Picard.lean` found the existing theorem
  at 223–225, its labelled docstring, degree surjectivity, and compatibility lemmas.
- Project `rg` with `picDegreeHom|picZero|proper.*decomposition` in `lean/Sheaf`: no hits.
- Inspected `dag/lean_names_upstream.json` for `def-sc-curves` and the item identifier;
  the item has no mapped name there, but its own candidate and the source grep give
  the declaration above.

The blueprint source markdown is not materialized in this local clone (`cat` reports
no such file). The node includes its full statement and two proof steps; these were
read alongside the existing theorem's blueprint-labelled docstring and complete proof.
The existing proof obtains a degree-one class, forms its integer-power section, and
maps `L` to `(deg L, L / section(deg L))`, with inverse `section(n) * y`, exactly as
the node's two proof steps describe. No statement correction or disputed statement.

## Second reading by G1

I independently compared the node with the existing declaration
`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom` and its enclosing
section in `WeilConjectures.AlgebraicGeometry.Curve.Picard`.

- Objects: `k` is `{k : Type u} [Field k] [IsAlgClosed k]`; `C` and its structure
  morphism are `{C : Scheme.{u}} [C.Over (Spec (.of k))]`; smoothness and properness
  are `[SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))]` and
  `[IsProper (C ↘ Spec (.of k))]`. Connectedness supplies `[Nonempty C]` via
  `IsConnectedCurve.nonempty`.
- Hypotheses: no characteristic, Noetherian, separated, finiteness, or chosen-point
  hypothesis is added. The theorem's nonemptiness requirement is weaker than the
  node's connected-curve setting and is available for every node instance.
- Conclusion: `∃ e : C.Pic ≃* Multiplicative ℤ × (picDegreeHom k C).ker` and
  `∀ L, (e L).1 = picDegreeHom k C L` render the product decomposition and its
  degree compatibility. `coe_ker_picDegreeHom` identifies the kernel with `Pic⁰(C)`.

Edge cases checked: connectedness excludes the empty curve; dimension one excludes
`Spec k`; arbitrary characteristic is allowed; positive, negative, and zero degrees
are represented by `Multiplicative ℤ`; and universe `u` is unrestricted. No rational
point is selected as an extra parameter. The kernel includes the zero-degree case.

Searches found the same existing source declaration: LeanSearch was unavailable,
LeanFinder and Loogle returned only unrelated or general algebraic results, and grep
of Mathlib, `WeilConjectures/`, and `lean/Sheaf` found no competing declaration. The
source docstring explicitly labels this declaration with `(blueprint:
lem-sc-pic-proper-decomposition)`.

No mismatch was found and no file or statement was changed. The node's `lean` record
is correctly marked `existing: true` with the slopmaster2 declaration.

## Reviewer fix (R-ppd1203)

The existing source theorem `AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom`
is not exactly the node, so the `existing: true` record was replaced by a new module
`lean/Sheaf/AlgebraicGeometry/Curve/PicardDecomposition.lean`,
`AlgebraicGeometry.Scheme.Hom.exists_mulEquiv_prod_picZero`:

- hypotheses: the source theorem assumes `[Nonempty C]` and
  `SmoothOfRelativeDimension 1`, not a proper smooth connected curve (def-sc-curves). The
  new statement takes `f : C ⟶ Spec (.of k)` with `[IsConnectedCurve f] [Smooth f]
  [IsProper f]` and `[IsAlgClosed k]`, as the landed sibling lem-sc-genus-invariant;
- Pic⁰: the recorded declaration of def-sc-pic0 is the set `f.picZero`; the statement gives a
  subgroup `P0` with `(P0 : Set C.Pic) = f.picZero` instead of the source's private
  `(picDegreeHom k C).ker` (which needs `SmoothOfRelativeDimension 1`);
- splitting: besides `(e L).1 = ofAdd (f.picDegree L)` (first component the degree), the
  node's step 2 says the isomorphism restricts to the identity on Pic⁰; the clause
  `∀ y : P0, e y = (1, y)` is added, which the source theorem lacked.
