## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationExtendsCover` states
`AlgebraicGeometry.Scheme.normalizationIn_functionField_extends_cover`, with its sole proof
`sorry`. No definition, helper theorem, dependency repair, or statement correction is added.
The source is the item's full blueprint page in sec-smooth-purity/sk-prop-a1-kummer.
The theorem docstring carries all five expanded DAG proof steps and their dependencies.

Hypothesis and conclusion correspondence:

- The base field is `{k : Type u} [Field k]`.
- The integral scheme is `(X : Scheme.{u}) [IsIntegral X]`.
- Being over that field is `[X.Over (Spec (.of k))]`, following the project convention.
- Finite type over the field is the pair `[LocallyOfFiniteType (X ↘ Spec (.of k))]`
  and `[QuasiCompact (X ↘ Spec (.of k))]`, exactly the recorded finite-type definition.
- The open subset is `(V : X.Opens)` with its actual open subscheme `V.toScheme` and
  inclusion `V.ι`; its nonemptiness is `[Nonempty V]`.
- Normality of this open is `(hV : IsNormalScheme V.toScheme)`. This is the dependency's
  integral-and-normal-local-domains convention, rather than a newly defined normality.
- The cover is `(P : Scheme.{u}) (f : P ⟶ V.toScheme)`.
- Connectedness is `[ConnectedSpace P]`, which includes nonemptiness, as the node's proof
  explicitly requires. It is not merely `PreconnectedSpace`.
- Finiteness and etaleness are `[IsFinite f] [Etale f]`.
- The reference to the function field `k(P)` entails integrality of P, proved in the node's
  step 2. The conclusion therefore first supplies `∃ (_ : IsIntegral P)`, rather than adding
  integrality as a hypothesis. Mathlib's `P.functionField` is then the generic stalk and
  has its existing Field instance.
- The implicit extension map `k(X) → k(P)` is supplied as an existential Algebra structure.
  Its equation `X.fromSpecOfAlgebraFunctionField P.functionField =
  P.fromSpecFunctionField ≫ f ≫ V.ι` requires precisely the structural map induced by
  the cover on generic points. Thus this is not an arbitrary map or an extra hypothesis.
  The generic-point morphism into X is a monomorphism, so this characterization uniquely
  determines the field homomorphism (Spec is fully faithful). No new choice-based
  definition or auxiliary sorry is introduced. Its finite separability is established in
  proof step 3; no finiteness assumption is needed by the recorded normalization definition.
- Normalization uses the recorded `X.normalizationIn P.functionField` and canonical
  `X.fromNormalizationIn P.functionField` without a private copy.
- Restricting it over V is `pullback (X.fromNormalizationIn P.functionField) V.ι`.
- The claimed agreement with the given cover is `∃ e : pullback ... V.ι ≅ P` together
  with `e.hom ≫ f = pullback.snd ... V.ι`. The equation is essential: this is an
  isomorphism over V, not just an isomorphism of the total schemes.

The existential integral and algebra structures only make explicit the data required to
interpret the node's phrase "normalization of X in k(P)". There is no extra geometric
conclusion such as global finiteness or global normality of the normalization. There are
no `let`, `show`, private declarations, local instances, or local notation in the signature.
All universes and variables are explicit; `u` is shared by the field and schemes in the
usual Scheme/Spec convention, with no independent smaller universe of test objects.

Statement dependencies read and used:

- `def-fin-normalization-extension`: upstream
  `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `AlgebraicGeometry.Scheme.normalizationIn` and `fromNormalizationIn`. Read their full
  declarations and the preceding `fromSpecOfAlgebraFunctionField` construction.
- `def-sbc-normal-dominant-galois`: `Sheaf.AlgebraicGeometry.NormalScheme`,
  `AlgebraicGeometry.IsNormalScheme`, whose complete definition is used for hV.
- `def-sc-function-field`: `Sheaf.AlgebraicGeometry.FunctionField` records that its general
  integral-scheme clause uses Mathlib's `Scheme.functionField`. Read this module and
  `Mathlib.AlgebraicGeometry.FunctionField`, including the generic stalk and Field instance.
  The component-product definition is for the nonintegral-curve clause, not this item.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (extends `IsAffineHom`, with finite maps on affine sections).
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (etale maps on affine pairs).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; an actual `Scheme.Opens` and its canonical inclusion
  implement the open subscheme.
- `def-weil-pbc-scheme-conventions` fixes no declaration; its recorded convention is followed.

The stated proof-dependency modules are imported without `public`:
`Sheaf.AlgebraicGeometry.EtaleNormalComponents` (read its full component theorem),
`Mathlib.AlgebraicGeometry.Noetherian`, `Morphisms.Proper`, `Morphisms.UniversallyOpen`,
`FunctionField`, `Restrict`, `Gluing`, `Scheme`,
`Mathlib.RingTheory.Unramified.LocalRing`, `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
and `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`. These provide the exact
recorded Noetherian, properness, openness, fractions, pullback, separability, integrality,
generic-stalk injection, section-gluing, spectrum, and morphism-gluing proof inputs.
Repeated statement-dependency modules are already imported publicly; no import cycle occurs.

Edge cases checked before writing:

- Empty X is excluded by IsIntegral; empty V is explicitly excluded by Nonempty V.
- Empty P would invalidate the intended connected-cover argument. ConnectedSpace includes
  Nonempty, agreeing with the explicit convention in proof step 2.
- A disconnected cover is outside the statement; no product of fields is substituted for k(P).
- V = X is allowed when X is normal; f = identity is allowed and specializes to
  normalization over the normal scheme.
- A proper nonempty open V is allowed, and no affineness or separatedness of X is imposed.
- Imperfect fields, positive characteristic, and zero-dimensional integral schemes are
  allowed. Separability follows from etaleness, not a characteristic restriction.
- Empty affine opens and empty overlaps in the proof do not impose a nonemptiness
  hypothesis on arbitrary opens in the statement. Step 5 explicitly handles overlaps
  by local morphism equality and gluing.
- The isomorphism equation has domain the pullback and codomain V.toScheme on both sides,
  so it compares exactly the restriction structure maps.

Searches for an existing statement, 2026-10-16:

- `msearch.py ... leanfinder "The normalization of an integral scheme in the function field
  of a connected finite etale cover of a normal open restricts to that cover"`: eight
  hits (`normalizationOpenCover`, `normalizationDesc`, comparison identities,
  `instIsIntegralNormalization`); none identifies this field normalization with the cover.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.normalizationPullback"`: seven hits,
  including smooth base change of relative normalization and its comparison identities.
  None states the required comparison with a given cover via its function field.
- `msearch.py ... grep
  "normalization.*[Ff]unctionField|[Ff]unctionField.*normalization|normalizationObjIso"
  AlgebraicGeometry`: five hits, all in Mathlib/AlgebraicGeometry/Normalization.lean,
  lines 220, 232, 236, 261, 270. These are relative-normalization section formulas.
- `rg` of `normalizationIn`, function-field/normalization patterns, and the item id in
  upstream WeilConjectures/Mathlib/AlgebraicGeometry and project lean/Sheaf/AlgebraicGeometry
  found the upstream normalization construction, generic-point lifting results, and curve
  applications, but no exact statement. Full-tree `rg` of the item id and the chosen
  declaration name in both WeilConjectures and lean/Sheaf found only the explanatory
  reference in NormalOpenLisseImage.lean:77, with no existing declaration of this statement.
- Read the upstream normalization file, the full relevant dependency signatures and
  docstrings, and the original blueprint page; the existing relative-normalization API
  is not itself this statement.

Validation: scompile.py compiled the initial module cleanly as both a sandbox file and its
library module. The final module is checked again by the required deliver2.py --no-push dry
run after adding the direct imports required for the dependency proof plan.

## Second reading by NS

Independent reading, 2026-10-16. I opened the sandbox node and module alongside the
original blueprint page (node/order 1907), all eight statement-dependency records and
their relevant source declarations. I also read the cited Stacks passages in
properties.tex (normal Noetherian schemes and normal integral sections), morphisms.tex
(etale openness, etale fibres over fields, and rational functions), and schemes.tex
(open fibre products). The blueprint's hypotheses are stated locally, without an
additional field characteristic, separatedness, affineness, or normality hypothesis on X.
The Stacks facts used in the proof do not impose such hidden hypotheses either.

Here is my object/hypothesis/conclusion list, with its Lean counterpart and verdict:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A base field k | `{k : Type u} [Field k]` | Exact; arbitrary characteristic and imperfect fields are allowed. |
| An integral scheme X | `(X : Scheme.{u}) [IsIntegral X]` | Exact; Mathlib's nonempty integral-scheme class. |
| X is over k | `[X.Over (Spec (.of k))]` | Exact recorded scheme-over-base convention. |
| X is of finite type over k | `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and `[QuasiCompact (X ↘ Spec (.of k))]` | Exact conjunction specified by def-weil-finite-type-morphism. |
| An open V in X | `(V : X.Opens)`, with `V.toScheme` and `V.ι` | Exact open subscheme, with restricted structure sheaf. |
| V is nonempty | `[Nonempty V]` | Exact. |
| V is normal | `(hV : IsNormalScheme V.toScheme)` | Exact dependency notion: integral with every stalk an integrally closed domain. Integrality of V already follows from nonempty openness in integral X. |
| A cover P to V | `(P : Scheme.{u})` and `(f : P ⟶ V.toScheme)` | Exact objects and structure morphism. |
| The cover is connected | `[ConnectedSpace P]` | Exact explicit convention in node proof step 2: connected and nonempty. |
| The cover is finite | `[IsFinite f]` | Exact: affine with finite affine section maps. |
| The cover is etale | `[Etale f]` | Exact affine-local etale-morphism class, not smoothness or a condition at one point. |
| Its function field k(P) | `∃ (_ : IsIntegral P)`, then `P.functionField` | Correctly derives the integral structure needed to interpret the named field; it is not an extra input hypothesis. |
| The field extension induced by f and V into X | `∃ (_ : Algebra X.functionField P.functionField)` and the equality `X.fromSpecOfAlgebraFunctionField P.functionField = P.fromSpecFunctionField ≫ f ≫ V.ι` | Exact implicit structural inclusion; the equality prevents an arbitrary unrelated algebra structure. |
| The normalization of X in this k(P) | `X.normalizationIn P.functionField` with `X.fromNormalizationIn P.functionField` | Exact recorded upstream construction. |
| Restriction over V agrees with the given cover | `∃ e : pullback (X.fromNormalizationIn P.functionField) V.ι ≅ P` and `e.hom ≫ f = pullback.snd (X.fromNormalizationIn P.functionField) V.ι` | Exact isomorphism over V; the commuting equation preserves the given cover map. |

The algebra-existence clause is a faithful way to express the implicit induced field
extension. In the upstream file, fromSpecOfAlgebraFunctionField is exactly Spec of
the algebra map followed by X.fromSpecFunctionField. The latter is fromSpecStalk at
the generic point. Mathlib Stalk.lean:79-90 makes fromSpecStalk a preimmersion, hence
a monomorphism. Cancelling it, and using full faithfulness of Spec, uniquely fixes
the field homomorphism in the displayed equality. The proof's finite separability
is not an extra input, and the existing normalizationIn construction does not require
a separate finiteness binder. The quantifier order first introduces X, V, P and f,
then derives the structures needed to state their normalization and its restriction.
The final source-proof remarks about global finiteness and normality are not clauses
of the node's statement; the Lean correctly states the restriction result.

Dependency interfaces checked directly: NormalScheme.lean defines IsNormalScheme as
the conjunction used above; FunctionField.lean explicitly delegates its arbitrary
integral-scheme clause to Mathlib Scheme.functionField (the generic stalk), rather
than its component-product definition. Upstream Normalization.lean:283-309 defines
the field-extension normalization and its canonical map with real data, as relative
normalization of Spec k(P) to X. Mathlib Finite, Etale, FiniteType, QuasiCompact and
OpenImmersion give the predicates described in the table. The convention node defines
no separate object. EtaleNormalComponents.lean's theorem has Noetherian source and
normal integral target, so the docstring correctly derives Noetherianity before using
it. There are no new definition nodes or dependency modules in this delivery, and no
statement_change to audit.

Edge cases: empty X is excluded by integrality; empty V by the stated nonemptiness;
empty P by the node's connected-and-nonempty convention, exactly as ConnectedSpace
requires. The auxiliary component index n = 0 can occur for the general dependency
but not this P. No other index set or zero object occurs in the statement. V = X,
the identity cover, zero-dimensional integral schemes, proper nonempty opens, and
nonseparated X are all allowed. The theorem imposes no characteristic condition,
perfectness, degree bound, or degree invertibility. All objects use the same ordinary
Scheme/Spec ambient universe u; there is no smaller universe of test schemes or
fields that could make a hypothesis vacuous. No variable or universe is unbound.

Independent searches, using different conceptual wording from the first worker:

- LeanFinder via msearch: "finite dominant morphism from a normal integral scheme is
  the normalization in its rational function field". Eight hits: toNormalization,
  normalizationDesc, integral-source and dominant-map instances, and their identities.
  Read the relevant Mathlib normalization signatures; none compares normalization in
  the function field with a connected finite etale cover of an open.
- LeanSearch via msearch: "A connected finite etale scheme over a nonempty normal
  open of an integral scheme equals the restriction of normalization in its generic
  residue field". Eight hits, including relative-normalization maps, the integral-map
  isomorphism instance, and Opens.stalkIso. No exact statement.
- Loogle via msearch: `AlgebraicGeometry.Scheme.normalizationIn`. The public index
  reports an unknown identifier; this search does not cover the upstream declaration,
  which I read directly instead.
- Grep via msearch: `normalizationIn|normalization.*cover|cover.*normalization` in
  AlgebraicGeometry. Five hits, all for Mathlib's relative-normalization open cover.
- Independent rg over project lean/Sheaf and upstream WeilConjectures used
  `normalizationIn|fromNormalizationIn|normalization.*[Cc]over|[Cc]over.*normalization`,
  as well as the node id and chosen declaration name. I opened the nearby
  FiniteEtaleOpenIntegralClosure and NormalizationDominantLift modules: they respectively
  prove finiteness of an affine relative closure and lifting through absolute
  normalization, rather than the present statement. The curve normalization theorem
  is restricted to smooth affine curves and asserts different properties. The node id
  occurs in NormalOpenLisseImage only as a proof-plan citation. No duplicate was found.

H5/H6/H8/H9: the delivery has one named theorem with its entire proof `sorry`, no
definitions or proved helpers, no local notation/instances/private declarations, and
source/blueprint docstrings. Its five proof-plan steps match the five DAG steps,
including the induced generic-field map, affine integral-closure comparison and
overlap gluing. Imports expose the statement dependencies and include the recorded
proof inputs. All Lean lines are at most 100 characters. I checked mechanically that
lean.statement equals the file's signature verbatim and that no non-lean node field
differs from the repository node.

Mismatches found and repairs: none. I preserved the Lean module and node record, and
added only this independent second-reading report. Validation: the required
`scompile.py NS lem-fin-normalization-extends-cover
lean/Sheaf/AlgebraicGeometry/NormalizationExtendsCover.lean` completed successfully for
both the sandbox and library module (3.3 seconds each), without errors or warnings.
