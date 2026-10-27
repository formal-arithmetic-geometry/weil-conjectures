## Worker report

The module `Sheaf.AlgebraicGeometry.SeparablePointClosureUniversalDensity` states
`AlgebraicGeometry.separable_point_closure_universal_density`, with the sole proof `sorry`.
There are no definitions, extra nodes, dependency repairs, statement corrections, or disputed
statements. Only the item's `lean` field changes. The source is BLR, Néron Models,
3.3 Lemma 4, printed p.67 (primary scan, PDF page 73), and the coefficient/product extension
specified in the node and used in 7.1 Lemma 4. I read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
and its direct-images proof; this is a prerequisite, not that unit's statement.

Hypothesis and conclusion correspondence:

- `k` is `[Field k]`; the specified separable closure `K` is `[Field K] [Algebra k K]
  [IsSepClosure k K]`. Mathlib's class means separably closed and separable over k;
  separability of a field extension includes algebraicity. No perfectness is imposed.
- `Z : Over (Spec (.of k))` is the k-scheme, and `[LocallyOfFiniteType Z.hom]` is exactly
  local finite type. There is no quasi-compactness, separatedness, or nonemptiness assumption.
- `T` is a set of morphisms in `Over (Spec k)` from the object whose structure morphism
  is `Spec.map (algebraMap k K)`. Thus its elements are exactly k-morphisms Spec K → Z,
  rather than arbitrary scheme morphisms. `hstable` says that precomposition by Spec of
  every `σ : K ≃ₐ[k] K` stays in T. The equality defining `t'` is equality of its actual
  underlying scheme morphism. Quantification over every automorphism also includes inverses.
- `Y`, `i`, `[IsClosedImmersion i]`, `[IsReduced Y]`, and `hclosure` specify precisely the
  reduced induced closed subscheme of the closure of the images of T. Here the point of
  Spec K is `IsLocalRing.closedPoint K`, its unique point, and the set of image points is
  `Set.range (fun t : T ↦ t.val.left (IsLocalRing.closedPoint K))`. This uses the uniqueness
  characterization in the recorded dependency
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, not a second construction.
  That theorem says every reduced closed immersion with this image is uniquely isomorphic
  over Z to its vanishing-ideal subscheme. Accordingly these binders introduce the Y that
  the node specifies; they do not add a condition on the input Z or T. No point lift or
  noncanonical map is assumed as extra data.
- The first conjunct quantifies over L/k and an algebraically closed common overfield Ω
  containing both K and L. The three algebra structures and the two `IsScalarTower`
  instances say the embeddings agree on k. Field algebra maps are injective, so these
  encode the node's field extensions inside Ω. The conclusion is
  `IsReduced (pullback (i ≫ Z.hom) (Spec.map (algebraMap k L)))`, exactly reducedness
  of Y_L. Mathlib's `IsReduced` (all section rings reduced) is equivalent to the stated
  local-ring condition: `isReduced_of_isReduced_stalk` and
  `isReduced_stalk_of_isReduced` in `Mathlib.AlgebraicGeometry.Properties`.
- The second conjunct quantifies over every E/K with its compatible k-structure and
  `m : ℕ` with `1 ≤ m`. `∏ᶜ (fun _ : Fin m ↦ Over.mk (pullback.snd ...))` is the
  m-fold product of Y_E in `Over (Spec E)`, hence its underlying scheme is `(Y_E)^m`.
  Preservation of products by base change gives the canonical identification with
  `((Y_K)^m)_E`; thus this renders the node's product and subsequent field-extension
  clauses with exactly the same schemes up to their canonical fibre-product isomorphism.
- `U` ranges over ALL affine opens of that underlying product, and `s` is a section
  of its structure sheaf on `U.1`, using `presheaf.obj (Opposite.op U.1)` explicitly.
- `x` is an E-rational point of that product: an actual morphism in `Over (Spec E)`
  from the identity object. For each coordinate j, the equation through the canonical
  product projection, base-change projection, and i requires that coordinate to be
  the E-extension of some t in T. This characterizes precisely the induced tuples T^m.
  Each t factors uniquely through i: its support lies in the closed image and its
  field source kills the radical vanishing ideal, by the recorded reduced-induced
  dependency. The fibre-product and product universal properties then give the unique
  induced x for every tuple. Conversely each such x has those tuple coordinates.
  Consequently no tuple is lost and no arbitrary family of maps replaces the induced ones.
- For every such x whose image lies in U, `Scheme.evaluation` sends s to zero in the
  residue field at that image; the conclusion is `s = 0`. The residue field embeds into E
  through x (`Scheme.Hom.residueFieldMap`), so zero here is equivalent to vanishing
  under the rational-point evaluation into E specified in the node. The quantifier hx
  is simply the proof that this evaluation is defined on U.
- The original density in Y_K is the specialization E = K, m = 1. The one-factor
  product is canonically Y_K, and isomorphisms carry affine opens and their section
  rings bijectively. The same second conjunct gives every positive power over K
  and its density after every E/K, including the identity field extension. These
  clauses are combined into one universal assertion, without an added independent
  density predicate or an additional claim.

Recorded statement dependencies used, with source signatures and docstrings read:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (also the over-category encoding).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`,
  `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
  I read its full signature, proof docstring, and uniqueness conclusion.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  Scheme limits come from `Mathlib.AlgebraicGeometry.Limits`; finite products in
  the slice and their fibre-product interpretation come from
  `Mathlib.CategoryTheory.Limits.Constructions.Over.Products`.

The module imports the stated proof inputs through the reduced-induced source,
Mathlib scheme limits, `IsSepClosed`, vector-space bases, and tensor-product bases.
In particular these provide the affine-section/residue-field, radical, reducedness,
separable-closure Galois, scalar-extension, affine pullback, open pullback, and
principal-open APIs named by the proof dependencies. The proof dependency
`lem-sfb-galois-stable-subspace-descent` has no recorded Lean module or Mathlib match
in the current node, and is therefore not imported; it is not needed for typing
this statement. Its step remains explicitly named in the theorem's proof docstring.

Edge cases checked before writing:

- T empty: its closure and reduced induced scheme are empty. Every positive product
  and field base change is empty; only the zero section exists on the empty affine.
  The theorem contains no `Nonempty T` or nonempty Y requirement.
- U empty: the vanishing premise is vacuous and the section ring is the zero ring,
  so the conclusion remains correct.
- m = 1 and E = K are included; m = 0 is excluded exactly by the node's m ≥ 1.
- Imperfect fields and positive characteristic remain allowed: K is only separably
  closed, and reducedness is asserted for arbitrary L, including inseparable L.
- Arbitrary affine opens, not only products of charts, are tested; the localization
  and sheaf step of the node's proof is retained in the docstring.
- All fields and schemes use one explicit ambient universe u, and quantified test
  fields are in that same universe, never an independently smaller universe.
  Thus all required field extensions and common algebraically closed overfields in
  the scheme universe occur, including the algebraic closure of any specified extension.
- Galois stability is substantive: for k = R, K = C and a single nonreal point of
  A¹, dropping stability would leave only one of the two points in its reduced
  k-closure after base change; the asserted density over K would then fail.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder` with “Galois stable separable rational points have
  geometrically reduced closure and universally schematically dense finite products”:
  eight results, including `Algebra.IsGeometricallyReduced`, dominance, and rational-map
  domain density. None states this family/closure/product theorem.
- `msearch.py ... loogle 'AlgebraicGeometry.IsReduced,
  AlgebraicGeometry.IsSchemeTheoreticallyDominant'`: three results concerning dominant
  morphisms, reducedness, and quasi-compact scheme-theoretic dominance. They do not
  supply this Galois-stable-point assertion or its product/extension test.
- `msearch.py ... grep 'schematicallyDense|schematically_dense|separable.*closure'
  AlgebraicGeometry`: only two separable-closure import hits in Sites/EtalePoint.lean.
- `msearch.py ... leansearch 'A Galois invariant family of separable rational points
  has geometrically reduced closure'`: eight results on geometrically reduced algebras,
  separable closure, and Galois extensions, with no exact theorem.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`
  for schematic density, separable closure, universal density, and rational-point powers:
  no exact match. The abelian-subvariety separable-definition theorem is a different
  descent result. `SchematicallyDenseOpen` and the generically-dense predicates concern
  other notions; none is duplicated here.
- `rg` of `lean/WeilConjectures` for this blueprint id: no match.
- `rg` of Mathlib AlgebraicGeometry, both project source trees, and
  `dag/lean_names_upstream.json` for the proposed declaration name: no collision.

Validation: scompile.py compiled both its sandbox check and the delivered library module
cleanly (1.8 s and 1.9 s). The initial elaboration errors (ambiguous section notation,
uninferred product family, and affine-open coercion) were repaired by explicit section
objects, product families, and U.1. There are no #check commands, local notation, hidden
definitions, extra axioms, or proofs beyond the requested sorry.

## Second reading by O4

Author's separate pass, with the original node and final Lean file open; the maintainer's
independent review follows delivery. I rechecked all hypotheses and clauses above.
The field/separable-closure, locally-finite-type, k-point, and Galois-action binders match.
The closed/reduced/image characterization is precisely the recorded dependency's unique
reduced induced structure. The common-overfield towers preserve the compatibility over k.
The second conjunct includes E = K and m = 1 and uses fibre products over E, rather than
products of underlying topological spaces. Each tuple is selected by its actual projected
scheme maps; the E-rational-point type enforces the structure map. Every affine open and
section is tested with the residue-field criterion equivalent to rational evaluation.
Empty T, empty U, arbitrary characteristic and the identity extension are all included.
No mathematical mismatch, statement correction, or new notion was found. The only changes
after the first draft were the three elaboration repairs recorded above; the final server
compile passed.
