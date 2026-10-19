## Worker report

The module states exactness and canonical arbitrary base change for extension by zero
of abelian sheaves on small etale sites, and the degreewise comparison for complexes.
Nothing is proved: the single theorem has proof `sorry`. No definitions or new nodes.

Hypothesis and clause correspondence:
- Schemes U, Z, Z′ are `{U Z Z' : Scheme.{u}}`; `j : U ⟶ Z` with
  `[IsOpenImmersion j]` is the open immersion. `a : Z' ⟶ Z` is arbitrary.
- The Cartesian square is the chosen `pullback a j`, with projection to U equal to
  `pullback.snd a j` and the base-changed immersion `pullback.fst a j`.
  `(IsPullback.of_hasPullback a j).flip.toCommSq` supplies exactly this orientation.
  Any Cartesian square is canonically isomorphic to the chosen one.
- Sheaves mean abelian sheaves, as the node's stage-1 split report explicitly specifies:
  the coefficient category is `AddCommGrpCat.{u + 1}`. No coefficient datum is added.
- Exactness is the conjunction `.Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits` for `openImmersionLowerShriek AddCommGrpCat j`.
  In abelian categories this says that every short exact sequence stays short exact.
- The sheaf comparison is `IsIso (openImmersionLowerShriekBaseChangeMap ... sq)`.
  This is a natural transformation, so the statement covers every sheaf F at once.
  Its source is `upperStar a_U ⋙ openImmersionLowerShriek j′` and its target is
  `openImmersionLowerShriek j ⋙ upperStar a`. Its inverse is exactly the displayed
  `a⁻¹ j_! F → j′_! a_U⁻¹ F`. Invertibility of the canonical mate expresses that
  direction without choosing an arbitrary isomorphism or a noncanonical map.
- For complexes the last conjunct applies `.mapHomologicalComplex (ComplexShape.up ℤ)`
  to that very transformation. Its components are the same sheaf comparison in each
  degree, so its inverse gives the displayed complex comparison. All unbounded
  integer-indexed cochain complexes are covered. The exactness clause already ensures
  degreewise extension preserves complexes, acyclic complexes and quasi-isomorphisms;
  these are consequences, not extra hypotheses.

Dependencies read and used:
- `def-weil-pbc-extension-by-zero`: module
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, declaration
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`. Real Kan-extension/sheafification
  construction, additive and exact in the upstream interface.
- `def-weil-pbc-inverse-image`: module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declaration
  `AlgebraicGeometry.Etale.upperStar`, with its sheaf pullback adjunction.
- `def-pc-fibre-product`: Mathlib module
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback` and projections.
- `def-weil-pbc-scheme-conventions` is a convention record, with no declaration to import;
  its `Scheme` and `IsOpenImmersion` are the actual Mathlib notions used.
- Canonical map: upstream
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`,
  `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`. Its full docstring
  defines it as the conjugate of the underived exchange under the composite adjunctions.
  This gives the required mate, not an abstract comparison.
- Proof dependency `lem-weil-pbc-extension-by-zero-exact` is upstream
  `Etale.preservesFiniteLimits_openImmersionLowerShriek` in the already imported Defs.
- Proof dependency `lem-weil-pbc-etale-shriek-base-change-modules` is imported privately
  from `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`, declaration
  `Etale.isIso_etaleLowerShriekBaseChangeMap`. The upstream open-immersion specialization
  is also available as `Etale.isIso_openImmersionLowerShriekBaseChangeMap`.
- Mathlib `NatTrans.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`
  provides the genuine degreewise chain map.

Source checked: local `literature/stacks-project/etale-cohomology.tex`,
`proposition-describe-jshriek` (03S5), `lemma-shriek-base-change` (03S6).
The latter explicitly states the abelian and module-sheaf comparison for arbitrary f.

Edge cases checked: empty U gives the zero extension; j the identity gives the identity
comparison; a the identity gives the identity-square comparison; empty Z′ gives the
zero target category. None is excluded by the binders. No finite-type, quasi-compact,
separatedness or boundedness assumption occurs. Zero sheaves and zero complexes are
included. The universe u is arbitrary and coefficients have the standard u+1 site size.

Searches (msearch.py NH with this item; logs in searches.jsonl):
- LeanFinder: “extension by zero exact arbitrary base change etale sheaves complexes”:
  8 unrelated Kaehler/cotangent exactness hits; no match.
- Loogle: `openImmersionLowerShriekBaseChangeMap,
  preservesFiniteLimits_openImmersionLowerShriek`: unknown identifier, no hits.
- Mathlib grep: `openImmersionLowerShriek|lowerShriek|extension.by.zero`:
  one multiplicative-character extension hit, unrelated.
- LeanSearch: “exact extension by zero base change sheaves etale complexes”:
  unavailable (Internal Server Error).
- rg in upstream `WeilConjectures/SixFunctors/Etale/LowerShriek/OpenImmersion`:
  exactness in Defs and canonical base-change IsIso in BaseChangeSquare, read in full.
  No combined statement including complexes found; these existing constructions are reused.
- rg for the item id across upstream WeilConjectures: no hits.
- rg in project `lean/Sheaf/AlgebraicGeometry` for extension by zero and
  openImmersionLowerShriek: related curve applications and module comparison, no
  exactness-plus-complex-base-change declaration.

Validation: scompile.py compiled the delivery file cleanly, without warnings or errors.
No statement correction, dependency repair, disputed statement, or missing prerequisite.

## Second reading by NH

I independently read the item JSON, its Lean module, all four statement-dependency
records and their actual interfaces, both proof-dependency interfaces, and Stacks
etale-cohomology.tex at definition-extension-zero, proposition-describe-jshriek
(03S5), and lemma-shriek-base-change (03S6). The source assumes schemes and an
etale j; the item's open immersion is the specified specialization. There are no
ambient Noetherian, finiteness, separatedness, characteristic or boundedness
hypotheses. No new definition node or dependency module is in this delivery.

Object/hypothesis/conclusion inventory and individual verdicts:

- Schemes U, Z, Z': `{U Z Z' : Scheme.{u}}`. These are Mathlib schemes, not schemes
  over an extra base or field. Matches.
- Open immersion j: `(j : U ⟶ Z) [IsOpenImmersion j]`. This is exactly the
  convention dependency's open immersion, with no quasi-compactness assumption.
  Matches.
- Arbitrary base change a: `(a : Z' ⟶ Z)`, with no property assumed. Matches.
- Cartesian square, U', a_U, j': `pullback a j`, `pullback.snd a j`, and
  `pullback.fst a j`. Reading the pullback projection signatures confirms their
  codomains U and Z', respectively. `(IsPullback.of_hasPullback a j).flip.toCommSq`
  therefore has exactly the orientation required by the comparison. The fibre
  product dependency explicitly chooses one once and for all; the chosen square
  excludes no base change or sheaf. The base-changed open immersion is inferred,
  not an additional hypothesis. Matches.
- Abelian sheaves F on the small etale site: `AddCommGrpCat.{u + 1}` in the
  recorded `Etale.openImmersionLowerShriek` and `Etale.upperStar` interfaces.
  The extension-by-zero dependency explicitly identifies its integer-coefficient
  case with abelian sheaves, and the item's split report specifies this case.
  The upstream construction is Kan extension followed by sheafification, not
  direct image or the set-valued extension. Matches.
- Exactness: `.Additive`, `PreservesFiniteLimits`, and `PreservesFiniteColimits`
  of that same extension-by-zero functor. For these abelian sheaf categories this
  is equivalent to preserving short exact sequences. It is neither an assumed
  property nor an added conclusion beyond exactness. Matches.
- Every F and the canonical comparison: `IsIso
  (openImmersionLowerShriekBaseChangeMap ... sq)` asserts invertibility of the
  natural transformation, equivalently invertibility at every sheaf. I read its
  definition: it is the conjugate of the flipped underived exchange under the
  composite adjunctions, with source `upperStar a_U ⋙ openImmersionLowerShriek j'`
  and target `openImmersionLowerShriek j ⋙ upperStar a`. Its inverse is precisely
  the node's displayed direction, not an arbitrary isomorphism. Matches.
- Complex clause: the final `IsIso` uses `.mapHomologicalComplex
  (ComplexShape.up ℤ)` of the very same transformation. Mathlib defines its
  component in degree n as the sheaf transformation at K.X n. Thus the map and
  inverse commute with differentials by naturality, for every integer-indexed
  cochain complex. Exactness on complexes follows degreewise from the preceding
  exactness clause, including preservation of acyclics and quasi-isomorphisms.
  No derived, pro-etale or bounded-below replacement is made. Matches.

Dependency audit: the actual upstream lower-shriek and upper-star definitions
have the required arbitrary-scheme and small-etale interfaces and use real
constructions. The exactness instance in OpenImmersion.Defs is accompanied by
additivity and finite-colimit preservation. I opened the project's
EtaleLowerShriekBaseChangeModules theorem (general etale j, constant module
coefficients) and the upstream open-immersion specialization (general
Grothendieck abelian coefficients). The latter directly supplies the abelian
case without making an implicit module-category identification part of the
statement. The former is correctly retained as the node's proof-plan import.
The scheme-convention node introduces no declaration of its own.

Edge cases: empty U, Z or Z', identity j or a, zero sheaves, zero complexes and
complexes concentrated in degree zero are admitted. There is no index-set or
positive-degree parameter, hence no hidden nonempty-index or n > 0 hypothesis.
The schemes have arbitrary universe u; the coefficient group universe u+1 is
exactly the recorded small-etale convention. All binders and the universe are
explicit. No characteristic or coefficient-field restriction is present.

Independent searches (different queries from the first reader):

- LeanFinder via msearch: "exact functor extension zero commutes base change
  cochain complexes abelian etale" returned eight Ext/exact-functor results,
  none a statement of this node.
- Loogle via msearch: "NatTrans.mapHomologicalComplex" returned unknown
  identifier; the declaration was nevertheless found and read in local Mathlib.
- LeanSearch via msearch: "extension zero base change abelian sheaves" was
  unavailable with Internal Server Error; no negative mathematical conclusion
  is drawn from that failure.
- rg across Mathlib, upstream WeilConjectures and project lean/Sheaf for
  `extensionZero.*baseChange|exact_baseChange|lowerShriek.*[Cc]omplex|
  [Cc]omplex.*lowerShriek|extension.by.zero.*exact` found component exactness and
  base-change results, applications, and the bounded-below derived comparison.
  I opened Etale/DerivedExtensionZeroBaseChange.lean: its main theorem assumes
  finite module coefficients and concerns D-plus and coherence, so is not this
  unbounded abelian-sheaf complex statement. No existing declaration states the
  complete node. All existing functors, the mate and the complex construction
  are reused; no duplicate definition is introduced.

No mathematical or Lean mismatch found; no signature or node correction made.
The single postponed theorem has the source/blueprint docstring and all three
proof steps (exactness, inverse canonical mate, degreewise naturality). The file
contains no definitions or proofs besides its required theorem `sorry`.
The node's lean.statement was checked verbatim against the file signature.
