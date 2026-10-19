## Worker report

The module `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula` states
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion`
with proof `sorry`. It introduces no definitions or helper theorems. The DAG statement is unchanged.

Sources read: the blueprint lemma lem-kun-0f0g in sec-smooth-purity/sk-prop-sf-kunneth-ordinary;
Stacks etale-cohomology.tex, Tag 0F0G, lemma-projection-formula-proper-mod-n, statement and proof.
The node's corrected geometric-fibre proof, rather than the invalid global generation argument
in the imported blueprint proof, is reproduced step by step in the declaration docstring.

Hypothesis and clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with universe u explicitly declared.
- The morphism f: `(f : X ⟶ Y)`.
- Properness: `[IsProper f]`, the Mathlib convention collected by
  def-weil-pbc-scheme-conventions. Read Mathlib.AlgebraicGeometry.Morphisms.Proper,
  `AlgebraicGeometry.IsProper`: separated, universally closed and locally finite type;
  universally closed also implies quasi-compact, so this is the paper's properness.
- The commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]`, with the inherited
  small-etale size convention of def-kun-projection-formula-map.
- Torsion: `(hΛ : IsAddTorsion Λ)`. Read Mathlib.GroupTheory.Torsion: all elements have
  finite additive order. For a unital ring this is equivalent to some positive integer
  killing 1, hence the ring; it imposes neither finiteness of the ring nor invertibility
  of its characteristic on the schemes.
- Arbitrary E in D(X_et,Λ): `(E : DerivedCategoryModule Λ X)`.
- Arbitrary K in D(Y_et,Λ): `(K : DerivedCategoryModule Λ Y)`. The abbreviation in
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients is exactly
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`, with X replaced
  by Y for K. There is no boundedness, constructibility or Tor amplitude binder.
- The specified canonical arrow: the two evaluations
  `((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K`.
  Read the complete declaration and docstring in
  WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection. Its source bifunctor is
  `derivedTensorRightDerivedLowerStar`, and its target is
  `rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar`, giving exactly
  Rf_*E tensor K -> Rf_*(E tensor f^{-1}K). The declaration
  `rightDerivedLowerStarProjectionMap_app_app` identifies it as the adjunction mate
  of the canonical tensor comparison followed by counit tensor identity, exactly the
  map of def-kun-projection-formula-map. Exact inverse image agrees with its left
  derived functor by `leftDerivedUpperStarIsoMapDerivedCategory`.
- The sole conclusion that this arrow is an isomorphism: `IsIso` of that component.

Statement dependencies used:

- def-kun-projection-formula-map: upstream module
  WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection, declaration
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, and the accompanying
  component and transpose equations. Its recorded specialization is used directly.
- def-weil-pbc-scheme-conventions: a convention record, not a new declaration or module;
  its properness pointer uses Mathlib.AlgebraicGeometry.Morphisms.Proper,
  `AlgebraicGeometry.IsProper`.
- Supporting standard coefficient instances come from
  WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat, in particular
  `AlgebraicGeometry.Etale.upperStarPreservesFlat_moduleCat`. They impose no additional
  flatness hypothesis on E or K.

Imports include the recorded available proof modules for lem-kun-0f10,
lem-kun-stalk-as-pullback, lem-exc-abelian-sheaves-gmodules,
lem-kun-proper-base-change-torsion-ring, lem-kun-inverse-image-monoidal, and
lemma-weil-pbc-geometric-stalk-conservative. The source for ProperUnboundedBaseChange
was read using `scompile.py --source` because the local clone lacked it.
The unstated proof prerequisites lem-kun-proj-formula-natural and lem-kun-0f12 do not
prevent stating this theorem and have no module to import. The other proof dependencies
are convention or Mathlib records, rather than modules to import as new statements.

Edge cases checked: empty source and target schemes are allowed; f may be the identity;
either complex may be zero or unbounded in both directions; the zero coefficient ring is
allowed (no Nontrivial binder); infinite torsion rings such as F_p[t] are allowed;
characteristic may equal a residue characteristic. Neither schemes being Noetherian nor
finite dimensional nor any global bound on the fibres is assumed. The universe u+1
coefficient convention is exactly that of the recorded map, with u arbitrary.

Searches performed:

- msearch.py leanfinder: "The canonical derived projection formula map for a proper
  morphism of schemes with torsion ring coefficients is an isomorphism for unbounded
  complexes". Eight results about unrelated quasi-isomorphisms and derived-category
  resolutions; no projection formula.
- msearch.py loogle: "rightDerivedLowerStarProjectionMap, IsIso". Zero hits; unknown
  identifier rightDerivedLowerStarProjectionMap in the Mathlib search index.
- msearch.py grep: "projectionFormula|projection_formula|rightDerivedLowerStarProjectionMap".
  Zero Mathlib hits.
- rg in upstream WeilConjectures for the node id, projection/isomorphism variants,
  and rightDerivedLowerStarProjectionMap. Read
  WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula. Its
  `isIso_rightDerivedLowerStarProjectionMap_of_finite` assumes `[Finite Λ]` and therefore
  does not state this node (e.g. F_p[t] is excluded). Its dualizable-object theorem adds
  dualizability of K. Neither is reused as an exact match.
- rg in lean/Sheaf for rightDerivedLowerStarProjectionMap, projection_formula and
  projectionFormula found scheme O-module projection-formula modules, which concern
  different coefficients and sites. The precise torsion/proper name and node id were
  also searched in lean/Sheaf, upstream sources and dag/lean_names_upstream.json, with
  no exact match.

No statement correction, disputed statement, new node or dependency repair was needed.

## Second reading by NB

Independent second reader, 2026-10-15. I read the repository node and its sandbox copy,
the complete Lean module, both statement-dependency nodes and their recorded interfaces,
the blueprint source, and Stacks etale-cohomology.tex at
lemma-projection-formula-proper-mod-n (Tag 0F0G), including its proof and the adjacent
constant-complex formula. The source introduces arbitrary schemes and unbounded module
complexes: it does not assume Noetherian schemes, invertibility of the coefficient
characteristic, finite coefficients, constructibility, or finite Tor amplitude.

Here is my object/hypothesis/conclusion checklist, made against the node:

1. Objects X and Y are arbitrary schemes. Lean has `{X Y : Scheme.{u}}` with explicit
   `universe u`. Verdict: exact; neither scheme is restricted to an affine, nonempty,
   Noetherian or finite-dimensional case.
2. The specified morphism is f : X -> Y. Lean has `(f : X ⟶ Y)`. Verdict: exact.
3. The sole geometric hypothesis is properness of f. Lean has `[IsProper f]`.
   I opened Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper extends IsSeparated,
   UniversallyClosed and LocallyOfFiniteType; universal closedness gives quasi-compactness.
   This is the properness collected by def-weil-pbc-scheme-conventions, whose own record
   explicitly fixes no additional notion. Verdict: exact, with no extra geometric instance.
4. The coefficient object is the commutative torsion ring used by the recorded projection
   morphism. Lean has `(Λ : Type (u + 1)) [CommRing Λ] (hΛ : IsAddTorsion Λ)`.
   I opened the definition of additive torsion in Mathlib.GroupTheory.Torsion: it means
   finite additive order for each element. For a unital ring, applying this to 1 gives
   a positive integer annihilating the entire ring. Conversely such an integer gives
   additive torsion. Verdict: exact; this is not a finite-ring assumption.
5. E is any object of D(X_et,Λ). Lean has `(E : DerivedCategoryModule Λ X)`.
   I opened Coefficients.lean: this abbreviation is literally
   `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   Verdict: exact, including complexes unbounded in both directions.
6. K is any object of D(Y_et,Λ). Lean has `(K : DerivedCategoryModule Λ Y)`.
   Verdict: exact by the same abbreviation; no dualizability, flatness or boundedness
   hypothesis is present. The binders quantify independently over every E and every K.
7. The arrow is the canonical PF_f(E,K) of def-kun-projection-formula-map, from
   Rf_*E tensor^L K to Rf_*(E tensor^L f^{-1}K). Lean uses
   `((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K`.
   I opened LowerStarProjection.lean in full. Its source and target bifunctors have
   precisely these objects, with left-derived upper star on the target. The component
   formula and transpose equation define this arrow as the mate of the canonical
   pullback tensor comparison followed by counit tensor identity. I also read
   UpperStarMonoidal.Comparison: its tensor comparison is the hom of the canonical
   derived natural isomorphism. The recorded exact-pullback comparison identifies
   left-derived upper star with the termwise inverse image. Verdict: the dependency's
   actual canonical arrow is reused, rather than an arbitrary map or endpoint isomorphism.
8. The conclusion is that this particular arrow is an isomorphism. Lean asserts
   `IsIso` of precisely that component. Verdict: exact, with no additional conjunct
   and no weakened existential isomorphism conclusion.

Universe and instance check: the coefficient and module-object universes u+1 are exactly
those in the landed def-kun-projection-formula-map record and DerivedCategoryModule.
The scheme universe u is arbitrary. This is the common large-universe convention for
small-etale module sheaves; no independent universe equality or additional size instance
was added. FlatModuleCat.lean supplies upperStarPreservesFlat_moduleCat for every
commutative Λ, not an assumption on E or K. The clean wrapper compilation confirms all
coefficient structure instances synthesize. Every variable and universe is explicitly bound.

Edge cases: either complex may be zero; identity and empty-source proper maps are covered;
an empty target imposes only the existence of f, not a new nonemptiness hypothesis.
The zero ring is included (characteristic one, without Nontrivial). Infinite positive
characteristic rings, including F_p[t], are included. Positive characteristic may coincide
with a scheme residue characteristic. There is no degree parameter or truncation bound,
so degree zero and all positive/negative cohomology degrees remain covered. There is no
index type, hence no empty-index exclusion. No global cohomological-dimension bound on Y
is assumed: the proof plan correctly uses finite dimension only on each proper geometric
fibre, exactly as Stacks 0F0G does.

Independent searches, using different wording from the worker:

- msearch.py leanfinder: "For torsion commutative coefficients, the derived tensor
  projection morphism of any proper map on the etale site is invertible". Eight hits,
  concerning formally etale algebra tensor products, Kaehler differentials and etale
  morphism composition. Their returned signatures do not state this theorem.
- msearch.py loogle: `"projection", "IsIso"`. Zero hits.
- msearch.py grep: `tensor.*pushforward|pushforward.*tensor|[Pp]rojection.*[Ff]ormula`.
  Three unrelated Witt-vector/manifold text hits, no etale derived projection formula.
- msearch.py leansearch: "Proper direct image on the small etale site satisfies the
  projection formula for arbitrary unbounded complexes over a commutative ring of
  positive characteristic". Service returned Internal Server Error; recorded as
  unavailable, not as a negative mathematical search result.
- Independent rg over upstream WeilConjectures and project lean/Sheaf used
  `projection.?formula`, `projection.?map`, `rightDerivedLowerStarProjectionMap`, and
  tensor/pushforward variants. I opened upstream ProjectionFormula.lean, including
  `isIso_rightDerivedLowerStarProjectionMap_of_finite` and
  `isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable`.
  The former assumes `[Finite Λ]`, excluding F_p[t]; the latter restricts K to
  dualizable objects. Neither is an exact existing declaration of this node.
  The project's ringed/scheme module projection-formula arrows and finite-free/totalization
  statements concern different module sites or hypotheses. Neither the chosen theorem
  name nor the node id has an exact upstream declaration in dag/lean_names_upstream.json.

No new definition nodes or dependency modules belong to this delivery, so H12/H13 introduce
no additional items to audit. The two genuine statement dependencies are usable as recorded.
The file introduces no definition, private notion, local notation or local instance.
Its only theorem has the whole proof `sorry`, as stage 2 requires. Its module/declaration
docstrings identify Tag 0F0G and `(blueprint: lem-kun-0f0g)`; the five proof-plan steps
match all five DAG proof steps, including coefficient actions, canonical-map compatibility,
constant-complex reduction and conservativity. Existing proof modules are imported for
that plan; the two still-unstated proof prerequisites are not hypotheses of this statement.

Mismatches and changes: none found in the Lean statement, node, or docstrings. I preserved
them verbatim and added this independent reading to the worker report. The only changed
node field relative to the repository is `lean`; no statement correction or citer audit
is needed. I checked programmatically that `lean.statement` equals the theorem signature
verbatim and that every Lean line has at most 100 characters.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NB lem-kun-0f0g
lean/Sheaf/AlgebraicGeometry/ProperTorsionProjectionFormula.lean` succeeded for both the
sandbox and library module checks, without errors or warnings. No global build or direct
compiler invocation was run. The initial delivery dry run correctly requested this missing
second-reading section; it reported no other preflight defect.
