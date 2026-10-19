## Worker report

The module `Sheaf.AlgebraicGeometry.SeparableClosureConservative` states
`AlgebraicGeometry.separableClosure_baseChange_conservative`, with one `sorry` and no
definitions. Its conclusion has exactly the three clauses of
`lem-kun-sep-closure-conservative`. The node copy changes only `lean`.

I read the node, every statement dependency and its recorded interface, and the original
blueprint file `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-sep-closure-conservative.md` on the project server (the literature files are not
present in the shared checkout). The source statement agrees verbatim with the node.
The proof docstring follows the node's six proof steps, including its explicit compatible
field embedding and its unbounded localization argument.

Hypotheses and clauses, in their order:

- A field `K` is `(K : Type u) [Field K]`. A chosen separable closure is
  `(L : Type u) [Field L] [Algebra K L] [IsSepClosure K L]`. Mathlib's
  `IsSepClosure` supplies separability and separable closedness; its separability implies
  algebraicity. This permits any chosen separable closure, including `SeparableClosure K`.
- A scheme over `K` is `(X : Scheme.{u}) (s : X ⟶ Spec (.of K))`.
  The structure morphism is explicit because the node concerns its base change and the
  proof names it. No properness, nonemptiness, finite type or characteristic condition
  is imposed.
- The base change is `pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L)))`.
  Its projection to `X` is `pullback.fst s (Spec.map ...)`, exactly the convention
  recorded in `def-pc-base-change`.
- Every geometric point is quantified as
  `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X), ...`.
  The first conjunct asserts the existence of `y` into that pullback with
  `y ≫ pullback.fst ... = x`. It keeps the same algebraically closed field, adds no
  preselected embedding of `L` in `Ω`, and asserts no uniqueness of the lift.
- For every `F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}` and every
  `α : F ⟶ G`, the second conjunct says
  `IsIso α ↔ IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} p).map α)`, with `p`
  expanded as the actual projection. Thus both directions of the sheaf criterion occur.
- For every `A B : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`
  and every `α : A ⟶ B`, the third conjunct gives the same equivalence for
  `(Etale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.map α`.
  This is the entire unbounded derived category; there is no boundedness assumption.

Dependency interfaces used (the declarations and their source docstrings/signatures were
read, rather than inferred from their names):

| Node | Module and interface |
| --- | --- |
| `def-pc-scheme` | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, morphisms and `Spec` |
| `def-kun-separably-closed` | `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`, `IsSepClosure`, `IsSepClosure.isSeparable` |
| `def-weil-geometric-point` | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded inline field-and-morphism encoding; also read `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField` |
| `def-pc-base-change` | `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its documented `pullback`/`pullback.fst` convention; `Scheme.Modules.moduleBaseChange` concerns modules and is not used in place of the scheme projection |
| `def-weil-pbc-etale-site` | `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology` |
| `def-weil-pbc-abelian-etale-sheaves` | `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, with the recorded coefficient category `AddCommGrpCat.{u + 1}` |
| `def-weil-pbc-derived-categories` | `Sheaf.AlgebraicGeometry.DerivedCategories`: its documented `DerivedCategory (Sheaf ... AddCommGrpCat.{u + 1})` encoding of `D(X_et)` |
| `def-weil-pbc-inverse-image` | `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `AlgebraicGeometry.Etale.upperStar` |
| `def-weil-pbc-derived-inverse-image` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: its recorded `mapDerivedCategoryPlus` is the restriction of `Functor.mapDerivedCategory`; the latter (defined in Mathlib's `DerivedCategory.ExactFunctor`, also the interface of proof dependency `lem-weil-pbc-exact-functor-derived-factorization`) is the canonical unbounded construction used here |

The stated proof dependencies are imported too: the composition interface is in the
already public `UpperLowerStar.Defs`; `GeometricStalkAsPullback` (read through
`scompile.py --source`) supplies `Scheme.geometricStalk_as_pullback`;
`EtaleInverseImageExact` supplies `Etale.upperStar_abelian_exact`; the upstream
`EtalePoint` supplies `Scheme.isIso_of_isIso_sheafFiber_map`; the Mathlib pullback,
algebraically closed field and exact-derived-functor modules supply the other recorded
proof interfaces. `lem-kun-stalk-faithful-derived` has no recorded Lean module in the
read DAG, so it has no import yet; its statement is not needed to type this statement.

Edge cases checked: the empty scheme makes the point-lifting clause vacuous and has the
expected trivial sheaf/derived categories; zero sheaves, zero derived objects and arbitrary
morphisms remain quantified; already separably closed `K` allows `L = K`; imperfect fields
of positive characteristic are included because `L` need only be separably closed, while
`Ω` is algebraically closed. No assumption on the structure map being surjective is added.
All schemes and geometric-point fields use the project's common scheme universe `u`;
the abelian coefficient groups use its established universe `u + 1`. All variables and
the universe are explicitly bound. The factorization and conservativity are valid for
nonreduced and non-Noetherian schemes as well.

Searches made before drafting, through `msearch.py` with its log in this sandbox:

- LeanFinder: `Every geometric point lifts after base change to a separable closure of a
  field and pullback of abelian etale sheaves and unbounded derived objects reflects
  isomorphisms`. Eight hits on étale base-change stability, module-sheaf pullback units,
  étale composition and formally étale algebras; no exact match to this node.
- Loogle: `"ReflectsIsomorphisms", "Etale"`. Zero hits.
- Mathlib grep in `AlgebraicGeometry`:
  `separab.*conserv|conserv.*separab|reflectsIsomorphisms.*upperStar|exists_comp_eq_of_surjective`.
  Zero hits.
- LeanSearch: `Base change of a scheme over a field to its separable closure is
  conservative on abelian etale sheaves and on the unbounded derived category`.
  Unavailable: Internal Server Error, recorded as unavailable.
- `rg` of the upstream `WeilConjectures` tree and `lean/Sheaf`, both for the node id
  and for separable-closure/conservativity/isomorphism phrases, found no exact existing
  statement. It found `Etale.reflectsIsomorphisms_upperStar_of_surjective` in upstream
  `SixFunctors.Etale.UpperLowerStar.Surjective`; I read the full theorem and docstring.
  It concerns module sheaves along an arbitrary surjection and states neither the
  geometric lifting clause nor the unbounded derived clause, so it is not this item.
- A check of `dag/lean_names_upstream.json` for the item and a check of both source trees
  for the proposed full declaration name found no duplicate.

No statement correction, new node, unusable dependency or disputed mathematical clause
was found. The first compile diagnosed a field-notation line break; after fixing that
syntax, `scompile.py Q34 lem-kun-sep-closure-conservative` compiled both sandbox and
library forms cleanly (4.3 s and 5.3 s). The proof remains exactly `by sorry`.

## Second reading by Q34

I independently compared the node JSON, the complete Lean module and the original
blueprint source at `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
lem-kun-sep-closure-conservative.md`. The source statement is verbatim the node's
statement. I also read the unit's `_section.md`: its finite-type, separably closed
base and invertible-integer hypotheses belong to the Kunneth proposition, whereas
this helper explicitly introduces an arbitrary scheme over an arbitrary field.
They must not be added to this lemma. I checked the cited Stacks TeX in the
launcher's literature mirror: fields.tex, `lemma-map-into-algebraic-closure` (09GU);
etale-cohomology.tex, `lemma-stalk-pullback` (03Q1) and
`theorem-exactness-stalks` (03PU); derived.tex,
`lemma-right-derived-exact-functor` (015F). These require respectively an algebraic
extension and algebraically closed target, arbitrary scheme morphisms, and exact
functors of abelian categories. There is no omitted Noetherian, properness,
finite-type, characteristic or boundedness hypothesis. The Zorn proof of 09GU
uses only algebraic closedness of the target, as the node explains.

Here is my object/hypothesis/conclusion checklist, in source order.

| Source item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary field K | `(K : Type u) [Field K]` | Exact; no perfectness or characteristic assumption. |
| A separable closure of K | `(L : Type u) [Field L] [Algebra K L] [IsSepClosure K L]` | Exact; the class has separably closed top field and separable extension, and separability implies algebraicity. No chosen embedding into a geometric-point field is assumed. |
| Scheme X over K | `(X : Scheme.{u}) (s : X ⟶ Spec (.of K))` | Exact; `s` is its structure morphism, with no additional property. Explicit structure maps are the project's base-change convention. |
| Base change and projection p | `pullback s (Spec.map (CommRingCat.ofHom (algebraMap K L)))`, with `pullback.fst` | Exact; the algebra map has the contravariant Spec direction `Spec L ⟶ Spec K`. The first projection goes to X. |
| Every geometric point of X | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)` | Exact recorded geometric-point interface; all such points, no K-algebra structure or lift chosen in advance. |
| Factors through X_L | `∃ y : Spec (.of Ω) ⟶ pullback ..., y ≫ pullback.fst ... = x` | Exact; the field remains Ω, and the lift is existential without uniqueness. |
| Every morphism of abelian etale sheaves | `∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (α : F ⟶ G)` | Exact category and quantifiers; no torsion, constructibility or finiteness condition. |
| Isomorphism iff its pullback is one | `IsIso α ↔ IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} p).map α)` with p expanded | Both implications, on the actual projection and canonical inverse image. |
| Every morphism of derived objects | `∀ (A B : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (α : A ⟶ B)` | Entire unbounded derived category, not its Plus subcategory. |
| Derived isomorphism criterion | `IsIso α ↔ IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategory.map α)` with p expanded | Both implications for the canonical exact termwise derived inverse image. |

I opened every statement dependency's node record and its actual declaration or
bundle interface. In Mathlib these are `Scheme`, `IsSepClosed` and `IsSepClosure`,
`IsAlgClosed` and `Scheme.SpecToEquivOfField`, `Scheme.smallEtaleTopology`, and
`Sheaf` (the full subcategory of sheaf presheaves). The
`BaseChangeConventions` header explicitly identifies scheme base change with the
chosen pullback and the projection to X with `pullback.fst`; its module-pullback
function is not substituted for this scheme construction. The `DerivedCategories`
header explicitly identifies the coefficient-free category with the exact
`DerivedCategory (Sheaf ... AddCommGrpCat.{u + 1})` used here.

I read the upstream `Etale.upperStar` construction and its surrounding coefficient
and scheme binders, also checking the current source using `scompile.py --source`.
It applies to arbitrary scheme morphisms and is the canonical left adjoint, not
an arbitrary functor. For the derived-inverse-image node I read both the recorded
`Functor.mapDerivedCategoryPlus` and its underlying Mathlib
`Functor.mapDerivedCategory`: the former is explicitly the restriction of the
latter. Mathlib's `mapDerivedCategoryFactors` identifies the latter with termwise
application followed by localization. Hence the unbounded interface is already
present through the dependency's imported module; no replacement or private
construction is needed. I checked the proof-dependency records: all recorded
modules are imported (or already publicly imported). The still-unstated
`lem-kun-stalk-faithful-derived` has no module to import and is needed only in the
future proof, not to type the statement.

Edge cases: empty X is allowed, with the lifting clause vacuous and the remaining
criteria in the trivial sheaf and derived categories. Zero sheaves, zero derived
objects and their morphisms are included. There are no index types or degree n
parameters to restrict; derived objects have arbitrary integer degrees and no
boundedness assumptions. All characteristics, including imperfect fields in
positive characteristic, are included: only L is separably closed, while Ω is
algebraically closed. If K is already separably closed then L = K is allowed by
`IsSepClosure.self_of_isSepClosed`. The quantified `u` is the established common
universe for schemes, fields and geometric points, as in the dependency's exact
inline interface; coefficients are in `u + 1` as required by the upstream site
and inverse-image construction. No independent test universe makes a hypothesis
vacuous, and no extra universe equality or category-size assumption is added.
All variables and the sole universe `u` are explicitly bound.

I repeated independent searches using different phrasing:

- LeanFinder via `msearch.py`: "Base field extension by a separable algebraic
  closure lifts all algebraically closed points and detects invertible arrows on
  the derived etale category". Eight hits, all on formally etale algebras and
  standard-etale maps; none states this result.
- Loogle via `msearch.py`: `"IsSepClosure", "IsIso"`. No hits.
- Mathlib grep via `msearch.py` in AlgebraicGeometry:
  `IsSepClosure|separableClosure|ReflectsIsomorphisms`. Eight hits on forgetful
  module functors, limits, affine etale coefficients and the geometric-point
  construction; none supplies this conjunction.
- Direct `rg` on both the upstream WeilConjectures tree and project `lean/Sheaf`
  for separability with conservativity, reflection or lifting, the node id, and
  the proposed full declaration name found no duplicate. I opened
  `Etale.reflectsIsomorphisms_upperStar_of_surjective`: its coefficient category
  is ModuleCat and it assumes a surjective scheme map; it supplies neither the
  geometric-point lift nor the derived clause, so it cannot replace this item.

No mismatch was found. I left the Lean module, signature and node unchanged and
appended this independent reading only. There are no new definition nodes or
dependency modules to review. The module has no definitions, auxiliary proofs,
local notation or private constructions, and its only proof is `by sorry`.
Both source/blueprint docstrings are present; the theorem docstring follows all
six node proof steps, including the compatible embedding and unbounded
localization argument. I checked that `lean.statement` is verbatim the module's
signature and that Lean lines stay within 100 characters. Compilation and final
preflight are recorded below after running the prescribed wrappers.

Second-reader validation: the required direct `scompile.py Q34
lem-kun-sep-closure-conservative lean/Sheaf/AlgebraicGeometry/
SeparableClosureConservative.lean` run passed cleanly in sandbox and library forms
(8.3 s and 5.0 s), with no error or warning. Signature equality and line-width
checks passed. The final delivery dry run is required to pass before pushing.

I also repeated LeanSearch with "Extending a base field to its separable closure
gives a conservative inverse image on etale sheaves and their unbounded derived
category". The service returned Internal Server Error; the required search log
records it as unavailable. The successful independent LeanFinder, Loogle and
grep searches above supply the remaining search evidence.

Final second-reader dry run: `deliver2.py Q34
lem-kun-sep-closure-conservative --no-push` printed OK for commit `2cdda2337c`:
preflight and compilation passed. The delivery contains the same unchanged Lean
statement and this second-reading report.
