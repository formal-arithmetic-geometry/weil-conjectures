## Worker report

The module lean/Sheaf/AlgebraicGeometry/GeometricFiberFinite.lean states both clauses of
cor-weil-pbc-geometric-fiber-finite, with sorry proofs only. No definitions are introduced.
The source blueprint was read in full, including its proof. The six proof steps of the
reviewed DAG node are recorded in the two theorem docstrings. There is no statement correction.

Hypotheses and clauses:

- Schemes X,Y and their map f: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Properness: `[IsProper f]`, Mathlib's separated, universally closed, locally finite type
  predicate. Universal closedness supplies quasi-compactness, so this is finite type as required.
- A geometric point: `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)`.
  This allows every algebraically closed extension, not only algebraic closures of residue fields.
- The geometric fibre and its two projections are `pullback f y`, `pullback.fst f y`,
  `pullback.snd f y`. The canonical cartesian square is `IsPullback.of_hasPullback f y`.
- Finite coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Commutativity is the convention of the dependency def-weil-pbc-derived-categories and its
  module-sheaf category, not a new restriction relative to that vocabulary.
- K in D+: `_root_.DerivedCategory.Plus
  (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- First displayed formula: `IsIso ((derivedBaseChangeMapPlus (ModuleCat Λ)
  (IsPullback.of_hasPullback f y).toCommSq).app K)` is exactly the recorded exchange map
  y^{-1} Rf_* K → Ra_* i^{-1} K. The square comparison, inverse images and derived direct
  images are the existing dependency functors, not replacements.
- F is a finite module sheaf: `F : Sheaf X.smallEtaleTopology (ModuleCat Λ)` and
  `[Scheme.IsFiniteSheaf F]`. The existing node def-constructible-finite was added to stmt_deps
  to name this notion. For module coefficients this is finite generation of each geometric
  stalk; over the finite ring Λ it is equivalent to finiteness of the underlying stalk set.
  No constructibility or local constancy is imposed.
- Every q≥0: `(q : ℕ)`, coerced to the integer cohomological degree by Lean.
- Left endpoint of the second formula: `(Scheme.pointSmallEtale y).sheafFiber.obj
  (higherDirectImage Λ f q F)` is precisely `(R^q f_* F)_y` in ModuleCat Λ.
- Right endpoint: `(cohomology (ModuleCat Λ) (pullback f y) q).obj
  ((DerivedCategory.singleFunctor _ 0).obj ((upperStar (ModuleCat Λ)
  (pullback.fst f y)).obj F))` is precisely `H^q(X_y,F|X_y)`.
- The second formula is not a bare existence of an isomorphism between those endpoints:
  it asserts IsIso of `sourceIso.inv ≫ Γ.map (baseChangeHomologyMap ... F) ≫ targetIso.hom`.
  Here sourceIso and targetIso explicitly identify global sections of the degree-q source
  and target sheaves with the displayed endpoints. The sheaf map is the fixed degree-q
  cohomology of the exchange evaluated at F[0]. Existence of these endpoint comparisons
  unpacks the identifications implicit in the displayed paper formula; they are conclusions,
  not additional hypotheses. The public API does not yet select canonical named versions
  of these two endpoint comparisons. The theorem records their existence together with
  invertibility of the transported specified exchange, avoiding invented comparison data.

Dependency declarations read and used (including their docstrings and signatures):

- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed; the geometric-point encoding also agrees
  with AlgebraicGeometry.Scheme.SpecToEquivOfField (Mathlib.AlgebraicGeometry.ResidueField).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, pullback.fst,
  pullback.snd. The chosen pullback square uses IsPullback.of_hasPullback.
- def-weil-pbc-etale-sheaves: CategoryTheory.Sheaf, with ModuleCat Λ coefficients in the
  six-functor encoding specified by the dependency record. Its additional set-sheaf
  predicates and torsion predicate are not needed in the signature.
- Sheaf.AlgebraicGeometry.DerivedCategories and its imported
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients: DerivedCategory.Plus,
  AlgebraicGeometry.Etale.DerivedCategoryModule, DerivedCategory.homologyFunctor.
- WeilConjectures.SixFunctors.BaseChange.Square: squareUpperStarIso, imported publicly
  through BaseChange.Derived; it gives the square comparison of inverse images.
- WeilConjectures.SixFunctors.BaseChange.Derived: derivedBaseChangeMapPlus.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: upperStar, lowerStar,
  upperStarLowerStarAdjunction, imported by the exchange and cohomology modules.
- Mathlib.CategoryTheory.Sites.Point.Basic: Point.sheafFiber; and
  Mathlib.AlgebraicGeometry.Sites.EtalePoint: Scheme.pointSmallEtale.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek: cohomology and
  rightDerivedGlobalSections, imported publicly by SmoothBaseChange.Defs.
- WeilConjectures.ConstructibleSheaf.Defs: Scheme.IsFiniteSheaf, existing finite-sheaf notion.
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs: higherDirectImage,
  baseChangeSourceFunctor, baseChangeTargetFunctor, baseChangeHomologyMap.
- Proof-only import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper supplies
  thm-weil-pbc-bounded-below's recorded isIso_baseChange_of_isProper. The other three
  proof-only nodes (forget-coefficients, geometric-point pullback/stalk, bounded Leray)
  have no Lean records, so there are no such modules to import yet.

Edge cases checked: empty X and empty geometric fibre give zero stalk/cohomology; an empty
Y admits no geometric point, so there is no illicit nonempty-base hypothesis. Zero Λ and
zero F or K are included; no Nontrivial hypothesis occurs. Degree zero is included, and no
positive-degree/invertibility-on-the-base or characteristic restriction is imposed.
No boundedness above, quasi-projectivity, noetherianity, constructibility, or finite local
constancy is assumed. Universes follow the existing small-etale six-functor encoding;
Ω and schemes use u and module sheaves/coefficient rings use u+1, all explicitly bound.

## Second reading by ND

I reread the node statement, its Stacks source (Tag 0DDF, corresponding to the two
proper-base-change-stalk clauses), and the complete Lean signature. The objects and
hypotheses match item by item: `f : X ⟶ Y` with `[IsProper f]`; an algebraically closed
field `Ω : Type u` and geometric point `y : Spec (.of Ω) ⟶ Y`; the fibre and its
projections are Mathlib's `pullback f y`, `pullback.fst f y`, and `pullback.snd f y`; and
the finite commutative coefficient ring is `Λ : Type (u + 1)` with `[Finite Λ]`. The
first conclusion is rendered by `isIso_geometricFiber_finite`: `K` is exactly an object
of `_root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat Λ))`, and the
`IsIso` concerns `derivedBaseChangeMapPlus` for the canonical `IsPullback.of_hasPullback`
square. This is the derived exchange map in the node, with no extra boundedness,
Noetherian, characteristic, or nonempty assumptions.

For the second clause, `F` is a module sheaf with the node's finite-sheaf hypothesis,
using the existing `Scheme.IsFiniteSheaf` definition (now cited by `def-constructible-finite`),
and `q : ℕ` supplies every `q ≥ 0`. The left displayed endpoint is the fibre of
`higherDirectImage Λ f q F`; the right endpoint is `cohomology` of the pullback fibre
with `upperStar (pullback.fst f y) F`. The existential `sourceIso` and `targetIso`
explicitly identify the global-sections presentations with these endpoints, and the
conclusion says the transported, specified `baseChangeHomologyMap` is an isomorphism.
Thus the formula's map is fixed rather than a bare unrelated existence of an endpoint
isomorphism. The Lean conclusion includes both endpoint comparisons that the paper
leaves implicit; these are witnesses, not added hypotheses. All quantifiers have the
same order and no clause is omitted.

Edge cases remain covered: degree zero, zero coefficient ring and zero sheaf/complex,
empty fibres, and arbitrary allowed universes. An empty base has no geometric point, so
the statement does not accidentally assume a nonempty base. No positive-degree,
constructibility, local-constancy, quasi-projective, or Noetherian condition appears.

I searched Mathlib and the slopmaster2 source with `msearch.py` (leanfinder, loogle,
grep and leansearch queries for proper base change, geometric fibres, stalk cohomology),
and used `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` for the node and its
notions. No existing theorem states this corollary. The only relevant existing notion
is `Scheme.IsFiniteSheaf` in `WeilConjectures.ConstructibleSheaf.Defs`; I used it and
added the already-landed `def-constructible-finite` to `stmt_deps`, rather than defining
a duplicate. Dependency declarations were opened and checked, including
`IsProper`, `pullback`, `pointSmallEtale`, `derivedBaseChangeMapPlus`, `higherDirectImage`,
`cohomology`, and `baseChangeHomologyMap`.

No mismatch requiring a repair was found. The worker's prior repair from
`pullbackIsPullback` (an `IsLimit`) to `IsPullback.of_hasPullback` is retained, since the
base-change API requires the latter. The module compiled cleanly with `scompile.py` on
the server; only the permitted `sorry` proofs remain.

Searches (all read-only):

- msearch.py leanfinder, query "proper base change geometric fiber finite coefficient ring
  bounded below derived etale cohomology": eight unrelated etale base-change / finite-fibre
  results; no geometric-stalk cohomology formula.
- msearch.py loogle, query "IsProper, IsIso": zero hits; identifier IsProper not known to
  the service. The declaration was instead read directly in pinned Mathlib.
- msearch.py grep, query "proper.*base.*change|[Gg]eometric[Ff]iber", AlgebraicGeometry:
  25 hits, including geometricFiber (a point of the big etale site) and morphism-property
  stability; no proper-base-change cohomology formula.
- msearch.py leansearch, query "proper base change geometric stalk cohomology finite
  coefficients": UNAVAILABLE, Internal Server Error; no mathematical verdict inferred.
- rg of source SixFunctors, using geometricFiber / geometric_fiber and
  stalk.*[Cc]ohomology|[Cc]ohomology.*[Ss]talk|fiber.*[Cc]ohomology|[Cc]ohomology.*[Ff]iber:
  only unrelated Frobenius/finite-stalk and torsion-family occurrences, no full statement.
- rg of source WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json for
  cor-weil-pbc-geometric-fiber-finite, geometricFiberFinite, geometric_fiber_finite and
  "Finite-coefficient geometric": no existing declaration of this corollary.
- rg for IsFiniteSheaf found the existing definition in ConstructibleSheaf/Defs.lean and
  the existing DAG node def-constructible-finite; used it rather than creating a new notion.

Server validation: scompile.py ND cor-weil-pbc-geometric-fiber-finite compiled this single
module cleanly, 3.8 seconds, nice 19, two threads, 60 second limit. The initial attempt
used pullbackIsPullback (an IsLimit, not IsPullback); changed to IsPullback.of_hasPullback.
No warning remains. No local compiler or global build was run.
