## Worker report

The delivery states `CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc`
in `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent`. Its sole proof is `sorry`.
There are no definitions, new nodes, dependency replacements, or statement corrections.
I read the item, all five statement dependencies and their declaration sources,
the proof-dependency records, Stacks `more-groupoids.tex`, lemma-ind-quasi-affine
(Tag 0APK), and `more-morphisms.tex`, definition-ind-quasi-affine and
lemma-ind-quasi-affine-alternative-definition (Tags 0AP6 and 0F1U).
The module docstring records the complete seven-step proof of the node.

Clause-by-clause statement correspondence:

- The schemes A and B are `{A B : Scheme.{u}}`; the specified morphism is `(p : A ⟶ B)`.
- The singleton fpqc covering is exactly
  `(hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage B)`.
  This uses the recorded precoverage, without replacing the covering hypothesis
  by an additional quasi-compactness assumption on p.
- A scheme V with a morphism to A is `{V : Over A}`; the scheme is `V.left`
  and its structural morphism is `V.hom`.
- Every affine open U of A is quantified by `∀ (U : A.Opens), IsAffineOpen U →`.
- The actual fibre product V times_A U is `Limits.pullback V.hom U.ι`.
  All its open subschemes K are quantified by
  `∀ (K : (Limits.pullback V.hom U.ι).Opens)`.
- Quasi-compactness of this open is the hypothesis
  `IsCompact (K : Set (Limits.pullback (C := Scheme.{u}) V.hom U.ι))`.
  Here compact means quasi-compact, with no Hausdorff assumption.
- The induced morphism K to U is
  `K.ι ≫ Limits.pullback.snd V.hom U.ι`. Its required property is precisely
  `IsQuasiAffineHom` of that composite, using the recorded relative predicate.
- The datum is `(D : Over.DescentDatum p V)`. This is the recorded transport
  presentation of the isomorphism and cocycle, whose source docstring explains
  its equivalence with the two- and three-fold pullback presentation by Yoneda.
- The conclusion `D.IsEffective` is the recorded existence of `V₀ : Over B`
  and an invariant map `q : V.left ⟶ V₀.left` giving a Cartesian square.
  The square supplies the desired isomorphism `V₀ times_B A ≅ V` over A,
  and transport invariance says it induces this specific datum.
- There is no quasi-compactness or local finite-presentation hypothesis on V.hom.
  No affineness, separatedness, nonemptiness, or finiteness hypothesis on either
  base is added. All objects are in an arbitrary explicit universe u.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`:
  `CategoryTheory.Over.DescentDatum` and `.IsEffective`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (publicly available
  through the imported `Mathlib.AlgebraicGeometry.Pullbacks`):
  `CategoryTheory.Limits.pullback` and `.snd`.

Proof imports include the recorded modules for affine reduction, affine effectivity,
and invariant-open gluing, plus scheme coproducts, flat base change, affine pullbacks,
Gamma-Spec adjunction and precoverage base change from Mathlib. The recorded
`WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent` was read using
`scompile.py --source` because that current upstream module is not in the older
source checkout; it is imported under precisely its published recorded name.
The four new geometric proof prerequisites have no recorded Lean declaration yet
and hence supply no import. They are cited step by step in the proof docstring.
No import closes a cycle.

Edge cases checked before writing: the empty V is allowed, with the empty descended
scheme; K may be the empty open (compact and quasi-affine), so no nonempty condition
is smuggled into hV. If A is empty, an fpqc singleton cover forces B empty and V is
empty too; all binders still make sense. Infinite unions of affine components and
other non-quasi-compact V are not excluded. For the identity cover, all descent
data are effective, as expected. U is allowed to be the empty affine open, and A
and B are not required to be affine. The conclusion includes datum compatibility,
rather than merely an isomorphism of underlying schemes.

Searches performed on 2026-10-18:

- `msearch.py ... leanfinder "An fpqc descent datum on a scheme whose quasi-compact
  opens over each affine open of the base are quasi-affine is effective"`: eight
  hits, including `HasAffineProperty.descendsAlong_of_affineAnd`,
  `Scheme.exists_isQuasiAffine_of_isLimit`, and affine-transition-limit helpers;
  none is this effectivity theorem.
- `msearch.py ... loogle "IsQuasiAffineHom, DescentDatum"`: zero hits;
  Loogle reported unknown identifier `IsQuasiAffineHom` (an upstream definition).
- `msearch.py ... leansearch "Effective fpqc descent for ind quasi affine morphisms
  of schemes"`: eight hits, including `Scheme.IsQuasiAffine.of_isAffineHom`,
  morphism-property descent lemmas and flat descent for isomorphisms;
  none states effectivity for the geometric class here.
- `msearch.py ... grep "IndQuasiAffine|ind.quasi.affine|isEffective.*[Qq]uasi[Aa]ffine"`:
  zero Mathlib hits.
- `rg` of `ind.quasi.affine|IndQuasiAffine|isEffective.*quasiAffine|
  isEffective_of.*[Qq]uasi` over `WeilConjectures/` and `lean/Sheaf/`:
  no upstream match; the side project has only the narrower
  `QuasiAffineFpqcDescent` (the entire morphism quasi-affine) and
  `SeparatedLqfFpqcDescent` (separated locally quasi-finite). Their signatures
  and docstrings were read and do not duplicate this statement.
- `rg` of the item's id in `WeilConjectures/`: no hits.
- `rg` of the proposed declaration name over Mathlib, `WeilConjectures/`,
  `lean/Sheaf/`, and `dag/lean_names_upstream.json`: no collision.

No mathematical node fault or statement dispute was found. The first compile
caught the namespace collision between `Over.pullback` and `Limits.pullback`;
all occurrences of the scheme fibre product are now explicitly qualified.
The underlying-point-set coercion also needs the explicit category parameter
`(C := Scheme.{u})`, preventing inference from selecting the category of types.
Validation uses only the prescribed per-file `scompile.py` and delivery wrappers.

## Second reading by N2

Author's second pass, not an independent review: this dispatcher brief prohibits
starting other agents and assigns independent review to the maintainer. I reopened
the node and the finished file and checked every quantified object and clause.
In particular, K is an open of the actual pullback, its compactness is not
compactness of the whole pullback, and quasi-affineness is asserted for the
canonical morphism K -> U. Both arrows and all universes are bound explicitly.
The datum and its effectivity use the exact recorded definitions; the latter's
invariance clause preserves the given datum. The empty-open and non-quasi-compact
cases remain present. The name-resolution repair changes no mathematical clause.
No mismatch requiring a statement correction was found. The sole deferred proof
is the theorem matching this DAG node, with all seven proof steps in its docstring.
