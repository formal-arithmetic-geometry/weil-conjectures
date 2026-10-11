## Worker report

The module `Sheaf.AlgebraicGeometry.GenusInvariant` states
`AlgebraicGeometry.genus_jacobian_invariant`, with its only proof `sorry`.
No definition is introduced or duplicated. The node's statement is unchanged.
`def-sc-genus`, which already has its recorded upstream declaration, is added to
`stmt_deps` because the displayed equality explicitly uses genus.

Hypothesis and clause correspondence:

- The extension of algebraically closed fields is `{k K : Type u} [Field k]
  [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]`. A field algebra
  map is injective, so this is an arbitrary field extension, not necessarily
  finite or algebraic.
- The curve and its structure map are `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`.
  `[IsConnectedCurve f]` includes the recorded `IsCurve f` (separated, finite
  type, dimension at most one), nonempty connectedness, and dimension exactly one.
  `[Smooth f] [IsProper f]` render the two remaining hypotheses.
- `b := Spec.map (CommRingCat.ofHom (algebraMap k K))` is the induced base map;
  `fK := pullback.snd f b` is the structure map of `C_K`.
- `fK.genus = f.genus` renders the displayed equality. The recorded genus is
  the dimension of global relative differentials. This is precisely the
  equivalent genus explicitly allowed by def-sc-genus; the upstream theorem
  `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus` in
  `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` identifies it with
  `dim H¹(O)` on smooth proper curves.
- The initial existential instance binders supply geometric integrality of
  both curves and connected-curve structure of `C_K`. These are derived from
  the given hypotheses, as in proof step 1, rather than added assumptions.
  They make it possible to use the recorded `IsJacobian` definition without
  requiring geometric integrality as an input hypothesis. Properness and
  smoothness of `fK` are inferred by base change.
- The two existential `J` clauses assert existence of Jacobians over both
  fields, via the recorded `IsJacobian`. This includes abelian variety
  structure and dimension equal to the appropriate genus.
- For arbitrary such Jacobians and arbitrary representing data `e`, `eK`,
  `IsPicardZeroMul f e` and `IsPicardZeroMul fK eK` mean that the chosen
  identifications are group-valued functor identifications. These are the
  explicit chosen data of the pairs in def-sc-jacobian; no arbitrary choice
  of a witness inside the Prop-valued class is silently fixed.
- `∃ i : JK ≅ Over.mk (pullback.snd J.hom b)` renders
  `J_(C_K) ≅ (J_C)_K`, as schemes over `K`.
- Compatibility is the final universally quantified equation. For every
  `K`-test scheme `T`, and every fibrewise degree-zero line bundle class `L`
  on `C ×_k T`, `pullbackLeftPullbackSndIso f b T.hom` is the canonical
  isomorphism `(C ×_k K) ×_K T ≅ C ×_k T`. Its `Pic.map` transports `L`.
  The existential `hLK` asserts that this transported class has degree zero;
  it is not an extra premise limiting the compatibility assertion.
  `toSheafify` sends the line bundle classes to the respective Picard sheaves;
  `e.homEquiv.symm` and `eK.homEquiv.symm` give their classifying morphisms.
  The equation says that the latter, followed by `i` and the original
  Jacobian's base-change projection, is the former. This is the canonical
  base-change square, not just an abstract isomorphism. Testing on all line
  bundle classes over all test schemes tests the entire Picard sheaf:
  every sheafified section is locally represented by such a class, and
  equality of morphisms is local. It therefore expresses compatibility of
  the full representing identifications. Since those identifications respect
  group laws, this isomorphism also respects the Jacobian group structures.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`,
  `AlgebraicGeometry.IsConnectedCurve`, and `AlgebraicGeometry.Scheme.Hom.genus`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`:
  `AlgebraicGeometry.IsJacobian`, including its `dim_eq` and `represents` fields.
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian`:
  `AlgebraicGeometry.exists_jacobian` was read with its full signature and
  docstring; it provides the existence input of proof step 3. Its docstring
  explicitly omits the general base-change clause, so that clause is stated
  here, not assumed to follow from the mere name of that theorem.
  `picardFunctorDegree`, `picardSubfunctorDegree`, `IsPicardZeroMul` and
  `Functor.RepresentableBy.homEquiv` provide the chosen identifications.
  The source's `nonempty_picardFunctorDegree_iso_of_isPullback` only asserts
  an unspecified isomorphism, so it is not substituted for the canonical
  compatibility clause.
- Mathlib's `pullbackLeftPullbackSndIso`, `Scheme.Pic.map` (from the project),
  `toSheafify`, `Over.map`, and `Over.mk` provide the structural maps, with
  no private definition of base change or genus.

Sources: the node's source markdown is not present on this remote machine.
Read the preserved blueprint source in
`dag/units/sk-prop-ext-invariance.json` and
`dag/notes/sec-curve-estimates/sk-prop-ext-invariance.json`, especially the
proper-case paragraph and its requirement that every map be canonical.
The node's complete three-step proof is included in the declaration docstring.

Edge cases checked: empty and zero-dimensional schemes are excluded exactly
by “connected curve” (dimension one and nonempty), not by an added hypothesis.
The identity extension and arbitrary transcendental extensions are permitted.
There is no characteristic restriction, genus-zero exclusion, or positive-genus
assumption; for genus zero the Jacobian may be the zero-dimensional trivial
abelian variety. Empty test schemes are included. All test schemes, not just
fields or reduced schemes, are quantified, so infinitesimal Picard data are
not lost. A common arbitrary universe `u` is used, as required by the
recorded Scheme/Picard definitions; any fields and schemes can be placed in a
common universe. Every variable and universe is bound explicitly.

Searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: “genus invariant under field extension smooth proper connected
  curve Jacobian base change”; eight elliptic Weierstrass base-change hits,
  none the required statement for arbitrary curves.
- Loogle: “Scheme.Hom.genus, IsJacobian”; no hits, unknown identifier genus.
- Mathlib grep: “genus|IsJacobian” in AlgebraicGeometry; no hits.
- LeanSearch: “genus base change Jacobian smooth proper curve”; service
  unavailable (Internal Server Error), not a negative search result.
- rg of WeilConjectures and lean/Sheaf for genus/baseChange/invariant,
  IsJacobian, and Jacobian/baseChange found the genus-only theorem
  `Scheme.arithmeticGenus_pullback` and the declarations listed above, but
  no theorem containing both genus equality and canonical Jacobian
  identification compatibility. Searching the item id in upstream found none.
- rg for the proposed full declaration name in Mathlib, WeilConjectures,
  `dag/lean_names_upstream.json` and lean/Sheaf found no collision.

No new nodes or dependency modules are needed. There is no disputed statement
or source correction. Server single-file compilation passed with no warnings
or errors; nothing was compiled locally. The second reader will independently
review and deliver this statement.

## Second reading by K1

Independent second reading: opened the delivered node and module together,
then the four statement-dependency nodes and their upstream declarations.
The following is my object/hypothesis/conclusion inventory and its Lean match.

1. Ground field and extension: the unit explicitly assumes an extension of
   algebraically closed fields. `{k K : Type u}` with `[Field k] [Field K]`,
   `[IsAlgClosed k] [IsAlgClosed K]` and `[Algebra k K]` gives precisely this.
   The algebra map between fields is injective; neither algebraicity nor
   finiteness nor a chosen embedding into a third field is required. Verdict:
   exact, including the unit's ambient hypothesis on the original field.
2. Curve and structure morphism: `{C : Scheme.{u}}` and
   `(f : C ⟶ Spec (.of k))` introduce the curve over the original field.
   `IsConnectedCurve f` extends the recorded `IsCurve f`, whose fields are
   separatedness, locally finite type, quasi-compactness and dimension at most
   one; its own fields impose connectedness/nonemptiness and dimension one.
   This is exactly def-sc-curves, not a zero-dimensional special case. Verdict:
   exact. `[Smooth f] [IsProper f]` give precisely smoothness and properness.
   Projectivity, Noetherianity and geometric integrality are consequences,
   not extra input hypotheses.
3. Extended curve: `b := Spec.map (CommRingCat.ofHom (algebraMap k K))`
   and `fK := pullback.snd f b` are the standard fibre product and its
   structure morphism. Smoothness and properness are inherited by base change.
   The existential `GeometricallyIntegral f`, `IsConnectedCurve fK` and
   `GeometricallyIntegral fK` are output witnesses establishing the scope of
   the recorded Jacobian definition. They are properties already forced by
   the input assumptions, not restrictions on the field extension or curve.
   Verdict: exact representation of the objects needed by the conclusion.
4. Genus equality: `fK.genus = f.genus` is the stated equality in the stated
   direction. Opened `Scheme.Hom.genus` in Curve.lean: its data are finrank of
   global relative differentials, with no sorry inside the definition.
   def-sc-genus explicitly permits this equivalent genus. Also opened
   `Scheme.genus_eq_arithmeticGenus` in Curve/RiemannRoch.lean: for smooth
   relative-dimension-one proper curves it agrees with `dim H¹(O)`. The
   smooth relative dimension is derived here, not assumed separately. The
   agreement theorem still depends on postponed proofs upstream; that is a
   stage-3 obligation, not a replacement definition in this delivery. Verdict:
   exact under the explicit equivalent definition allowed by the node.
5. Jacobians over both fields: the existential `J`, `GrpObj J` and
   `IsJacobian f J` clauses give both representing abelian varieties. Opened
   the recorded `IsJacobian`: it extends `IsAbelianVariety`, imposes
   `dim_eq = f.genus`, and asserts existence of a group-compatible representing
   isomorphism. Verdict: matches the referenced existence conclusion.
6. Chosen identifications: universal `J`, `JK` with `GrpObj`/`IsJacobian`
   instances, followed by `e`, `eK : ...RepresentableBy ...` and
   `IsPicardZeroMul f e`, `IsPicardZeroMul fK eK`, range over the Jacobian
   pairs of def-sc-jacobian. Opened `IsPicardZeroMul` and both degree-zero
   Picard definitions in Picard/Jacobian.lean. These conditions specify the
   chosen group-valued identifications themselves; they are not additional
   hypotheses on C. Verdict: exact, without fixing an arbitrary choice hidden
   inside the Prop-valued IsJacobian class.
7. Base-change isomorphism: `∃ i : JK ≅ Over.mk (pullback.snd J.hom b)`
   is `J_(C_K) ≅ (J_C)_K` over K. The quantifier follows both chosen
   identifications, so it can carry those very identifications to each other.
   Verdict: exact; an unspecified abstract isomorphism would not suffice.
8. Compatibility: for every `T : Over (Spec (.of K))`, every `L` on
   `C ×_k T` and every degree-zero witness `hL`, the assertion supplies a
   degree-zero witness `hLK` for its canonical pullback and equates its
   classifying map, followed by `i.hom.left` and the original Jacobian
   projection, with its original classifying map. Opened
   `pullbackLeftPullbackSndIso` and its projection lemmas in Mathlib's
   Pullback/Pasting.lean: its hom goes from `(C ×_k K) ×_K T` to `C ×_k T`,
   so `Pic.map` has exactly the required contravariant direction.
   `toSheafify` and `homEquiv.symm` then have the intended meanings.
   Verdict: exact canonical square, not an arbitrary Picard isomorphism.
   Degree-zero line bundles locally generate their fppf sheafification; all
   K-test schemes and their fppf covers are quantified here. Equality on those
   local representatives therefore gives equality on all Picard sections.
   With IsPicardZeroMul this also implies compatibility with group laws.

Source check: the primary source is the blueprint, not a Stacks lemma. Its
markdown is absent on this machine, so read the preserved unit
`dag/units/sk-prop-ext-invariance.json` and its complete section text in
`dag/notes/sec-curve-estimates/sk-prop-ext-invariance.json`. The proper-case
paragraph requires the same genus and the canonical Jacobian base change;
no characteristic restriction applies to this lemma (the unit's prime-to-
characteristic n concerns its cohomology conclusion). Independently read
Stacks `curves.tex` from the Stacks source repository: `definition-genus`
(Tag 0BY7) assumes properness, dimension one and H⁰(O)=k; the last follows
here from proper geometric integrality over k. `lemma-duality-dim-1`
(Tag 0BS2), parts (5) and (6), gives the equivalent differentials genus under
smooth relative dimension one. Also read Tag 01JF on uniqueness of
representing pairs by Yoneda. Sources consulted:
https://raw.githubusercontent.com/stacks/stacks-project/master/curves.tex,
https://stacks.math.columbia.edu/tag/0BY7,
https://stacks.math.columbia.edu/tag/0BS2,
https://stacks.math.columbia.edu/tag/01JF.

Dependency/existing-declaration check: opened the recorded `exists_jacobian`
for thm-sc-jacobian-representability, including its full signature and
explicit documentation that base change is omitted there. It supplies the
existence proof input, not the compatibility conclusion of this delivery.
Opened `nonempty_picardFunctorDegree_iso_of_isPullback`: its arbitrary
isomorphism is explicitly weaker than the canonical statement, so it cannot
replace this module. No new definition nodes or dependency modules are
present or needed to type the statement; all notions used are the recorded
upstream ones. There is no statement_change and no corrected statement to
check against citers.

Edge cases: empty schemes and points are excluded by the node's definition
of connected curve itself. Genus zero is allowed, including its trivial
Jacobian; no nontriviality assumption appears. Empty test schemes and
nonreduced test schemes are included. Identity extensions and arbitrary
transcendental extensions are included. All characteristics are included;
there is no n binder, hence no n=0 case to exclude. The common arbitrary
universe follows the recorded Scheme/Picard APIs; objects of different
sizes can be placed in a common universe. Every variable and universe is
explicitly bound; no accidental typeclass premise was found.

Independent searches, with different wording from the first worker:

- LeanFinder through msearch.py: “Jacobian Picard degree zero functor canonical
  change of algebraically closed base field”; eight Weierstrass elliptic
  curve hits, none for arbitrary proper smooth connected curves.
- Loogle through msearch.py: `"genus"`; zero hits.
- LeanSearch through msearch.py: “For a smooth proper curve its Jacobian and
  genus commute with extension of algebraically closed fields”; service
  returned Internal Server Error, recorded as unavailable, not negative.
- rg in Mathlib AlgebraicGeometry for `Picard|Jacobian|genus` found elliptic
  Jacobian coordinates, not the required general-curve Picard theorem.
- rg in WeilConjectures and lean/Sheaf for genus with pullback/invariant/
  baseChange and Jacobian with base change found the existing
  `Scheme.arithmeticGenus_pullback` in Cohomology/EulerChar.lean and the
  Picard base-change statements above. Opened arithmeticGenus_pullback:
  it only gives genus invariance, not the Jacobian compatibility clause.
- rg for the proposed full name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no collision.

Mismatches/changes: none in the Lean signature, node statement, definitions
or compatibility equation. Left those files unchanged. Appended this
independent report. The module introduces no definitions and proves nothing:
its only theorem body is `sorry`. The module and declaration docstrings cite
this node's source and blueprint id, and the declaration docstring follows
all three proof steps. Imports, namespace and line widths match conventions.
Verified the node's lean.statement is verbatim the delivered signature.
Independent server single-file compilation passed in 2.4 seconds with no
errors or warnings.
