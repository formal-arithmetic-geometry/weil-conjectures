## Worker report

Existing declaration: `CategoryTheory.Over.DescentDatum.transport_self`, a structure
projection in `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`, source line 86.
No module is delivered: the identity is already part of the recorded dependency's
transport encoding. The field's full source signature is
`transport_self {T : C} (f : T ⟶ X) (a : Over.mk f ⟶ V) : transport f f rfl a = a`.
Its generated projection also takes the ambient category, `p : X ⟶ Y`, `V : Over X`,
and `D : DescentDatum p V`. Specialize the ambient category to
`AlgebraicGeometry.Scheme.{u}`; the generic existing declaration includes every
scheme universe and requires no property of `p` or `V`.

Hypotheses and clauses, matched individually:

- Schemes X and Y and the morphism X → Y: the projection's implicit objects
  `{X Y : C}` and `{p : X ⟶ Y}`, specialized to `C = Scheme`.
- A scheme V over X: `{V : Over X}`, whose underlying scheme is `V.left` and
  whose structure morphism is `V.hom`.
- A descent datum φ on V relative to X/Y: the argument `D : DescentDatum p V`.
  The dependency's full docstring explicitly identifies this transport encoding
  with the pullback isomorphism and its cocycle. `D.transport f₁ f₂ h` is the
  action of φ on points lying over the two maps f₁ and f₂.
- The fibre product and its projections: `pullback p p`, `pullback.fst p p`
  and `pullback.snd p p` from the recorded fibre-product dependency. Their
  universal pair yields the original φ in the transport description.
- The diagonal with both projection composites equal to id_X: it is
  `pullback.lift (𝟙 X) (𝟙 X) rfl`. For any test map `f : T ⟶ X`, its
  composition with the diagonal corresponds to the pair `(f,f)`.
- Both iterated pullbacks canonically identified with V: a T-point of either
  pullback along the diagonal, over f, is exactly `a : Over.mk f ⟶ V`.
  This uses the projection composites id_X, so no arbitrary identification or
  extra chosen isomorphism enters the field statement.
- Under these identifications Δ*φ equals id_V: `D.transport f f rfl a = a`
  for every T, f and a. This is equality on all scheme-valued points, not merely
  on the underlying topological points. Yoneda in `Over X` identifies it with
  equality of the endomorphism of V and the identity. Conversely identity of
  that endomorphism fixes every such point. Thus the two statements are
  equivalent, with the same objects and no extra geometric assumptions.

Dependency declarations read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`
  in `Mathlib.AlgebraicGeometry.Scheme`; full signatures and docstrings read.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, `pullback.lift`, `pullback.map` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, and the
  `HasPullbacks Scheme` instance in `Mathlib.AlgebraicGeometry.Pullbacks`;
  full source declarations read.
- `def-pd-descent-datum`: `CategoryTheory.Over.DescentDatum` and
  `CategoryTheory.Over.DescentDatum.IsEffective` in
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`; full structure,
  fields and docstrings read. Its `transport_self` field is the existing item.
  Effectivity is defined in the dependency but is not assumed here.

Source verified at https://stacks.math.columbia.edu/tag/023U, paragraph
immediately after Definition 35.34.1 (023V), together with Remark 35.34.2.
The local `literature/stacks-project/descent.tex` was absent, so the official
Stacks page was opened instead. This is exactly the paragraph named by the node.
The node's proof specializes the cocycle to the triple diagonal, giving an
invertible idempotent e; cancellation gives e = id. The transport definition
already includes this consequence as its `transport_self` field.

Edge cases checked: X → Y an identity (equal-pair transport still fixes every
point); X or V empty (Yoneda includes empty test schemes and empty objects,
without any nonemptiness assumption); arbitrary characteristics and arbitrary
scheme universes; non-affine schemes and morphisms not fpqc. No condition of
flatness, surjectivity, finiteness, effectivity or affineness is introduced.
No statement correction, disputed statement, new node or dependency module.

Searches for existing declarations:

- `msearch.py ... leanfinder` query: "The pullback of a scheme descent datum
  along the diagonal is the identity; transport along equal points is the
  identity". Eight Mathlib hits, including pullback-diagonal isomorphisms and
  a pseudofunctor descent identity; no exact scheme-datum match.
- `msearch.py ... loogle` query:
  `CategoryTheory.Over.DescentDatum.transport_self`. Zero hits, unknown
  identifier (the public search index does not contain this source declaration).
- `msearch.py ... grep` query:
  `transport_self|descent.*diagonal|diagonal.*descent`, subdirectory
  `CategoryTheory`. Zero Mathlib hits.
- `rg -n` with that pattern in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  and repository `lean/Sheaf`: found the exact field at DescentDatum.lean:86,
  its assignment at line 219, and a reference to the identity in
  `Sheaf/AlgebraicGeometry/FpqcSingletonFullyFaithful.lean:92`.
- The same pattern in `dag/lean_names_upstream.json`: no entry for the field.
- `grep -rn` for `lem-galois-descent-datum-diagonal-identity` in the upstream
  source: no blueprint-tag match. The signature/docstring search found the
  existing declaration despite its absent item tag.

A sandbox-only scratch check imports the existing module and Scheme, checks
both the full projection and its Scheme specialization, and prints its axioms
on the server. The scratch file is not a delivered module.
Server validation passed with exit code 0, no warnings, in 1.5 seconds:
`transport_self` specializes to schemes with exactly the binders listed above;
`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

## Second reading by J1

I independently opened the item JSON, its sandbox JSON, all three statement-dependency
nodes, the complete upstream DescentDatum structure, and the Mathlib declarations
for Scheme, Scheme.Hom, pullback, its projections and lift, and HasPullbacks Scheme.
The item has no corrected statement, new node, or dependency module.

Source reading: the local Stacks checkout is absent. I fetched the official
[descent.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex)
into the sandbox scratchpad and read lines 8091–8169, including the section's
introductory assumptions, Definition 023V, the paragraph at 8136–8144, and Remark
35.34.2. I also checked the official [section 023U](https://stacks.math.columbia.edu/tag/023U).
The section introduces arbitrary schemes and an arbitrary morphism, and the
paragraph states the asserted diagonal identity. No covering assumption occurs.

My object/hypothesis/conclusion checklist, in the node's order:

1. X and Y are schemes and p maps X to Y. The projection has implicit X, Y, p
   in an arbitrary category; instantiate C with Scheme.{u} and its existing
   category instance. Verdict: the scheme specialization has exactly these objects.
2. V is a scheme equipped with V -> X. The binder V : Over X packages V.left
   and V.hom without restricting either. Verdict: exact.
3. The given phi is an isomorphism between the two pullbacks and satisfies the
   cocycle. Its recorded dependency is DescentDatum p V. I read its transport,
   naturality, self, and composition fields, not just its name. Verdict: the
   dependency's transport model expresses the same datum. The inverse transport
   is obtained by reversing f₁,f₂; transport_transport and transport_self give
   the two inverse laws. Conversely an invertible geometric cocycle yields
   transport_self by cancelling the invertible idempotent on the equal triple.
   Thus the self field imposes no extra condition on a geometric descent datum.
4. X ×_Y X and pr₀,pr₁ are the chosen fibre product and projections. These are
   pullback p p and pullback.fst/snd p p. Scheme.Pullback.instHasPullbacks gives
   their existence for all morphisms. Verdict: the transport description does
   not choose a different fibre product; the universal pair recovers phi.
5. Delta is the unique morphism whose projection composites are identities.
   It is pullback.lift (𝟙 X) (𝟙 X) rfl; lift_fst/lift_snd give the composites.
   The pair associated to f ≫ Delta is (f,f). Verdict: the self transport is
   exactly restriction to this diagonal, with no free choice of a diagonal.
6. Both iterated pullbacks are canonically V over X. Their points over an
   arbitrary f : T -> X are both Over.mk f -> V, because both composites
   of the diagonal with a projection are identity maps. Verdict: the identical
   source/target type of transport f f renders both canonical identifications.
7. The resulting morphism V -> V equals its identity. The actual field is
   transport_self {T : C} (f : T ⟶ X) (a : Over.mk f ⟶ V) :
   transport f f rfl a = a, and its generated projection takes the datum first.
   Verdict: equality for every T,f,a means equality of the induced natural
   endomorphism of the representable functor on Over X. Yoneda gives equality
   of morphisms of V over X. In particular T = V.left, f = V.hom and a = id_V
   already detect the endomorphism. Conversely the identity fixes every point.
   These auxiliary test objects are universally quantified, not added hypotheses.

Edge cases: there is no index family, integer n, or zero-object assumption in
this item. Empty X, Y or V are admitted wherever their structure maps exist;
empty test schemes remain available. Identity p, arbitrary characteristics,
non-affine schemes and non-fpqc p are included. The generic projection allows
independent object/hom universes and specializes to Scheme at every universe;
all variables and universes are bound in the generated signature.

Independent searches (2026-10-11), with different terms from the worker:
- LeanFinder via msearch: "A cocycle isomorphism of objects over a base restricts
  to the identity on the unit section". Eight hits, led by OneCocycle.ev_refl.
  I opened that declaration: it concerns group-valued cochains, not this datum.
- Loogle via msearch: '"DescentData", "id"'. Six hits concerning identity
  morphisms or identity pullback functors; none replaces this projection.
- Mathlib grep via msearch: hom_id|self|diagonal in CategoryTheory/Sites/Descent.
  Seventeen hits. I read DescentData.hom_self and its surrounding structure;
  it needs a pseudofunctor and uses different objects from the recorded datum.
- rg in upstream WeilConjectures/CategoryTheory/Comma/Over and project lean/Sheaf
  for unit section|equal points|transport_self|DescentDatum found the upstream
  self field and the project's uses of that same descent-datum definition.
  This confirms reuse of the exact recorded dependency instead of a private copy.

No mathematical mismatch was found, and no node or Lean signature was changed.
The sandbox lean.statement is verbatim the field's source signature at line 86.
Existing upstream declarations are reused, so the delivery introduces neither
proofs nor definitions nor new docstrings. The source structure documents 023V;
its short self-field docstring identifies the identity. The node's two proof
steps remain applicable: form the diagonal and its canonical identifications,
then restrict the cocycle to the triple diagonal and cancel the isomorphism.
Those steps explain why the transport model already contains this consequence.

I reran scompile on scratchpad/Check.lean: exit 0, no warning, 1.5 seconds. It
printed the full projection type and its Scheme specialization; #print axioms
reported only propext, Classical.choice and Quot.sound. The scratch file and
fetched source are not delivered. Second reading changed only this report.
