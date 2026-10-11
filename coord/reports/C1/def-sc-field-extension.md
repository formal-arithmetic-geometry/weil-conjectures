## Worker report

Existing declarations realize the entire bundle of field-extension notation. No module is
needed: the node introduces names for the dependency constructions, not a new kind of
field extension or a new cohomology map. The primary declaration is
`AlgebraicGeometry.Etale.cohomologyMap`, in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` (line 182).
Its signature and docstring were read: it takes an arbitrary scheme morphism, an abelian
étale sheaf on its target, and a natural degree, and returns the additive cohomology map
into the cohomology of the inverse image. Specializing its morphism to the canonical
base-change projection gives exactly rho; no additional hypotheses enter that construction.

Hypothesis and clause correspondence (names below describe terms, not new Lean aliases):

- k and k' are algebraically closed fields: `[Field k] [IsAlgClosed k]`,
  `[Field k'] [IsAlgClosed k']`.
- The field extension k'/k is `[Algebra k k']`, with map `algebraMap k k'`.
  This is the recorded `Algebra` of `Mathlib.Algebra.Algebra.Defs`.
- C is a curve over k: `C : Scheme`, `f : C ⟶ Spec (.of k)`, `[IsCurve f]`.
  `AlgebraicGeometry.IsCurve` is in `WeilConjectures.AlgebraicGeometry.Curve`;
  its full docstring and signature include separation, finite type and dimension ≤ 1.
- Write i for `Spec.map (CommRingCat.ofHom (algebraMap k k'))`.
  C_k' is `CategoryTheory.Limits.pullback f i` and pi_k' is
  `CategoryTheory.Limits.pullback.fst f i`. These are the base-change dependency's
  recorded scheme-level conventions, as explained in its lean.note and in
  `Sheaf.AlgebraicGeometry.BaseChangeConventions` (read in full for those conventions).
  The Mathlib declarations and docstrings are in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- F is `Sheaf C.smallEtaleTopology AddCommGrpCat.{u+1}`, using the abelian-sheaf
  dependency's `CategoryTheory.Sheaf` (`Mathlib.CategoryTheory.Sites.Sheaf`).
- F_k' is `(AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u+1}
  (pullback.fst f i)).obj F`. The inverse-image declaration and its docstring in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` identify it as the sheafified
  presheaf inverse image left adjoint to direct image.
- For every q ≥ 0 use `q : ℕ`. The map rho is
  `AlgebraicGeometry.Etale.cohomologyMap (pullback.fst f i) F q`, of type
  `Sheaf.H F q →+ Sheaf.H ((Etale.upperStar AddCommGrpCat.{u+1}
  (pullback.fst f i)).obj F) q`.
  This is precisely the recorded cohomology-pullback dependency. The cohomology
  dependency records `Etale.cohomology` and `Etale.rightDerivedGlobalSections` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, with their sheaf-level
  comparison to `Sheaf.H` left to stage 3; this delivery follows the existing dependency
  convention, rather than defining a second cohomology theory.

Edge cases: q = 0 is included; neither torsion nor constructibility is imposed on F;
no properness, smoothness, connectedness or nonemptiness is required of C. Empty curves
and zero-dimensional curves are included by IsCurve, and by the generic pullback and
cohomology-map declarations. The trivial extension k' = k and every characteristic are
included. Universes can be placed in one common universe, with schemes in that universe
and coefficient groups in its successor, as in the dependency declarations; no test-object
quantification is restricted.

Searches made:

- msearch leanfinder: "base change of a curve along a field extension and pullback map on
  etale sheaf cohomology" returned eight Weierstrass-curve base-change hits, none the
  complete bundle.
- msearch loogle: "CategoryTheory.Limits.pullback, CategoryTheory.Limits.pullback.fst"
  returned twelve hits including pullback.fst and pullbackIsPullback; their signatures
  confirm the canonical fibre-product projection.
- msearch grep: "cohomologyMap|fieldExtension" in AlgebraicGeometry returned zero hits
  in Mathlib.
- msearch leansearch: "pullback map on etale cohomology of a sheaf along a scheme
  morphism" was unavailable (service Internal Server Error); no verdict is drawn from it.
- rg in the source repository for def-sc-field-extension, fieldExtension definitions,
  and cohomologyMap definitions found the canonical Etale.cohomologyMap at line 182.
  Curve/FieldExtension.lean also uses exactly this map along a cartesian base-change
  projection (lines 88–95); its signature was read, but that theorem is not recorded here.
- rg in lean/Sheaf for fieldExtension, FieldExtension and def-sc-field-extension found
  field-theory and descent material, no competing definition of this bundle.

The node's source is the blueprint definition itself; its text in the DAG was read.
The literal source Markdown file is absent from the local literature checkout. No
statement correction, new node, dependency replacement, or disputed statement is needed.

## Second reading by C1

I independently opened the node copy, each of its seven dependency records, and the
recorded declarations. The node's source is a blueprint definition, not a Stacks lemma:
`sec-curve-estimates/sk-prop-ext-invariance/def-sc-field-extension.md`, order 1028.
The literal Markdown is absent from this machine's literature checkout. I read the
complete imported source text in the node; there is no ambient hypothesis stated there.
I also read the upstream Curve/FieldExtension and Curve/Assertions usages. In particular,
the properness and torsion assumptions of the invariance theorem are not assumptions
of this definition of the pullback map.

The independent object/hypothesis/clause checklist is:

1. Algebraically closed fields k and k': `[Field k] [IsAlgClosed k] [Field k']
   [IsAlgClosed k']`. Verdict: exact. These specialize the generic construction; the
   generic declaration is not an assertion about arbitrary fields being algebraically closed.
2. An extension k'/k: `[Algebra k k']` and `algebraMap k k'`. I read `Algebra`
   in Mathlib.Algebra.Algebra.Defs: its unital ring map supplies precisely the extension
   map, automatically injective for fields. Verdict: exact; no finite-extension hypothesis.
3. A curve C over k: `C : Scheme.{u}`, `f : C ⟶ Spec (.of k)`, `[IsCurve f]`.
   I read the class in WeilConjectures.AlgebraicGeometry.Curve: separation, local finite
   type plus quasi-compactness (finite type), and `topologicalKrullDim C ≤ 1`.
   Verdict: exact; no smoothness, properness, connectedness, or dimension-equals-one assumption.
4. Base change C_k': `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))`,
   using the scheme conventions recorded by def-pc-base-change. I read
   Sheaf.AlgebraicGeometry.BaseChangeConventions and Mathlib's pullback signatures.
   Verdict: exact fibre product over Spec k; all schemes have these pullbacks.
5. Projection pi_k' to C: `pullback.fst f i`, for the above spectrum map i.
   The Mathlib signature is `pullback f i ⟶ C`. Verdict: correct projection, not `snd`.
6. An abelian etale sheaf F on C: `Sheaf C.smallEtaleTopology AddCommGrpCat.{u+1}`.
   Verdict: the recorded abelian-etale-sheaf dependency; arbitrary F, without constructibility
   or torsion restrictions.
7. F_k' = pi_k' inverse image of F: `(Etale.upperStar AddCommGrpCat.{u+1}
   (pullback.fst f i)).obj F`. I read upperStar's signature, construction and docstring
   in WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: sheafified presheaf inverse
   image, left adjoint to lowerStar. Verdict: the dependency's notion, not module pullback.
8. Every nonnegative degree q and its pullback homomorphism: `q : ℕ` and
   `Etale.cohomologyMap (pullback.fst f i) F q`. Its source is `Sheaf.H F q` and
   target is `Sheaf.H ((Etale.upperStar _ (pullback.fst f i)).obj F) q`.
   I read its complete section binders and body at TopologicalInvariance.lean:182.
   The preceding universal-homeomorphism section has ended; this definition requires no
   universal-homeomorphism instance. Verdict: exact map in the existing cohomology-pullback
   encoding. I also read Etale.cohomology and rightDerivedGlobalSections in
   Derived/LowerShriek.lean:227–236. Their comparison with Sheaf.H is the stage-3 bridge
   explicitly documented by both recorded cohomology dependencies, not a new notion here.

Edge cases: q = 0, F = 0, the empty scheme, curves of dimension zero, the identity
extension, and arbitrary characteristic all remain allowed. Empty schemes have Krull
 dimension bottom in IsCurve. No index set or test-object quantification occurs.
The common arbitrary universe u for fields and schemes, successor universe for groups,
is the existing site's convention; it does not fix a finite universe or bound cardinality.

Independent H4 searches used different wording from the first reader's report:

- LeanFinder via msearch: "inverse image of abelian sheaves along a morphism of schemes
  induces a homomorphism on cohomology". Eight Mathlib scheme-module/sheaf map hits;
  none is the etale cohomology map.
- Loogle via msearch: `AlgebraicGeometry.Etale.cohomologyMap` is unknown to its Mathlib
  index (zero hits); this is not evidence against the upstream declaration I opened.
- Loogle via msearch: `CategoryTheory.Limits.pullback.fst` returned its exact general
  signature and eleven related pullback declarations.
- msearch grep: `cohomologyMap` returned zero Mathlib hits. Direct rg with
  `cohomologyMap|extension.*pullback|field.*base.change` in Mathlib/AlgebraicGeometry,
  WeilConjectures/AlgebraicGeometry/Curve, and lean/Sheaf/AlgebraicGeometry found the
  upstream curve applications (FieldExtension:93 and Assertions:126,137), not a new
  independent field-extension notion. The upstream cohomologyMap is the existing map.

No mathematical mismatch was found, and no Lean or node field was changed. In particular,
there is no missing definition or unusable dependency requiring a new node or module.
The node's lean.statement is verbatim the upstream signature from `noncomputable def`
through the result type before `:=`. No new definition data, theorem, proof, or file-local
notation is delivered. The only change is this independent second-reading section.
A sandbox-only Check.lean explicitly applies the existing map to the canonical projection,
with all fields, algebraic closure instances, curve instance, F, q, and universe bound;
its compile result is recorded below. It is not a module of the delivery.

Validation: `python3 /home/ubuntu/weil-launcher/scompile.py C1 def-sc-field-extension
scratchpad/Check.lean` exited 0, compiled in 3.1 seconds, with no warning or error.
The printed fully explicit cohomologyMap type has only X, Y, f, F and n as parameters,
confirming that no hidden properness, torsion or universal-homeomorphism hypothesis enters.
