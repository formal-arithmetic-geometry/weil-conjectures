## Worker report

The module `Sheaf.Paper.VanishingDescendsRetract` states the categorical form of the
node.  `C` and `D` are the source and target categories, and `R q : C ⥤ D` is the
functor denoting `R^q h_*`.  The objects `I M : C` render the two sheaves, while
`ι : I ⟶ M`, `ρ : M ⟶ I`, and `hρ : ι ≫ ρ = 𝟙 I` render the retraction
hypothesis.  The hypothesis `hM` renders `R^q h_* M = 0` for every `q > 0` as
`IsZero ((R q).obj M)`, and the conclusion renders vanishing for `I` with the same
quantifiers and positivity clause.  The proof is `sorry`, as required at stage 2.

The statement uses `CategoryTheory.Retract` (the structure with section, retraction,
and `i ≫ r = 𝟙`) and `CategoryTheory.Limits.IsZero`.  In the intended application,
`C` is `Mod(Xₑₜ, Λ)`, `D` is `Ab(Yₑₜ)`, and each `R q` is the functor supplied by
`def-weil-pbc-direct-image`; the dependency `def-weil-pbc-derived-categories`
provides the bounded-below derived setting.  The other statement dependencies fix
scheme conventions, the module-sheaf category, the constant sheaf, the small étale
site, and abelian étale sheaves.  Their recorded declarations are used as the
intended interpretations; no private replacement definitions are introduced.

Edge cases checked: `q = 0` is excluded exactly by the node's `0 < q`; the theorem
allows an empty class of positive degrees only through the explicit universal
quantifier, and permits zero objects and arbitrary (including empty) categories.
No finiteness, nonzero coefficient, or characteristic assumption is added.

Searches made:

- `msearch.py ... leanfinder "higher direct image of a direct summand vanishes if it vanishes on the sheaf"` returned only generic derived-category vanishing declarations, with no exact statement.
- `msearch.py ... loogle "CategoryTheory.Retract, IsZero, Functor.map"` returned no hits (the service reported unknown `IsZero`).
- `msearch.py ... grep "Retract|IsZero" CategoryTheory` found `Mathlib.CategoryTheory.Retract`, `CategoryTheory.Limits.IsZero`, and generic object-property retract files, but no higher étale direct-image statement.
- Repository searches with `rg` found no existing declaration for this node or its theorem name.

No statement correction, source error, or new/dependency module was needed.

## Earlier second reading (a previous round; superseded)

I reread the item statement and all seven statement dependencies. The Lean binders match the categorical source and target, functor family, retract maps and identity equation, positive-degree vanishing hypothesis, and identical positive-degree conclusion clause by clause. The recorded Mathlib/project declarations were checked before writing; the theorem is generic exactly because the item’s `R^q h_*` is only supplied by the direct-image dependency. No hypotheses or edge cases were changed.

## Second reading by J1

I independently read the node, its seven statement dependencies, the delivered
Lean, and the source proof at Stacks Tag 0A4C, `lemma-sandwich`, first paragraph
(`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`, lines 18430–18462).
The source assumes proper maps and a surjection in its surrounding sandwich
lemma, and injectivity to obtain its direct summand. Those assumptions produce
the retraction; the isolated descent-of-vanishing step needs only the retraction
that this node explicitly assumes. They must not be added to this node.

The earlier categorical delivery and earlier second reading above are
superseded by this reading. I found H3: arbitrary categories `C`, `D` and an
arbitrary family `R` replaced the node's actual schemes, coefficient ring,
module sheaves and higher direct images. A specialization in a docstring does
not state that specialization in Lean. I replaced those binders and expressions
with the recorded geometric constructions; the natural-language node did not
need correction. I also found H8: the old docstring compressed the proof and
omitted the first (forgetful) step. It now gives all three steps and their node
references. Added the standard copyright header and removed unused generic
retract imports. The main declaration is now
`AlgebraicGeometry.Etale.vanishing_descends_retract`.

Object/hypothesis/conclusion checklist, written from the node before repair:

| Node item | Final Lean rendering | Verdict |
| --- | --- | --- |
| Schemes X and Y, arbitrary morphism h | `{X Y : Scheme.{u}} (h : X ⟶ Y)` | Exact; no properness, étaleness or finiteness assumption. |
| Commutative coefficient ring Λ, including Z and F_r | `(Λ : Type (u + 1)) [CommRing Λ]` | Exact in the source six-functor universe convention; no field or torsion assumption. |
| Small étale site of X and Y | `X.smallEtaleTopology`, `Y.smallEtaleTopology` | Recorded Mathlib sites, not Zariski sites. |
| Sheaves of modules over constant Λ | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` | Standard module-valued encoding used by the recorded derived-category dependency. |
| I and M in that category | `{I M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}` | Both use the same scheme and coefficients. |
| Module morphisms iota and rho | `(ι : I ⟶ M) (ρ : M ⟶ I)` | Natural transformations with Λ-linear components. |
| rho after iota is id_I | `(hρ : ι ≫ ρ = 𝟙 I)` | Same order and identity object. |
| Underlying abelian sheaf of F | `(sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F` | Forgets coefficients before deriving direct image, as required. |
| F placed in degree zero in D+ | `(DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj ...` | Recorded bounded-below construction, not an unspecified complex. |
| Rh_* on abelian sheaves | `(rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj ...` | Recorded total right derived functor on D+; computed by injective/K-injective representatives. |
| R^q h_* F = H^q(Rh_*F) | `(DerivedCategory.Plus.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj ...` | The target is abelian sheaves on Y, not module cohomology or global cohomology. |
| Vanishing for M in every positive degree | `hM : ∀ q : ℕ, 0 < q → IsZero (...)` with terminal input M | Exactly the hypothesis; no vanishing in degree zero. |
| Vanishing for I in every positive degree | `∀ q : ℕ, 0 < q → IsZero (...)` with terminal input I | Exactly the conclusion with the same quantifier order. |

Dependency signatures opened and checked:

- `def-weil-pbc-scheme-conventions` is a convention record; the node assumes only
  a scheme morphism, rendered by Mathlib's `Scheme` and categorical Hom.
- `def-weil-sheaf-of-modules-category` records `Scheme.Modules` only for
  structure sheaves, and explicitly points to general `SheafOfModules` in its
  note/mathlib match. I opened `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`:
  its `SheafOfModules` is sheaves over a sheaf of rings. Our coefficient sheaves
  use the module-valued encoding prescribed by the recorded
  `def-weil-pbc-derived-categories`, not `Scheme.Modules` (which would be wrong).
- `def-weil-pbc-constant-sheaf`: `constantSheaf` in
  `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean` is sheafification of the
  constant presheaf. A sheaf of Λ-modules with Λ-linear restrictions is the
  usual encoding of modules over this constant sheaf: the constant action
  extends uniquely to locally constant coefficient sections by sheaf gluing.
  No new constant-ring definition is introduced.
- `def-weil-pbc-etale-site`: `smallEtaleTopology` in
  `Mathlib/AlgebraicGeometry/Sites/Etale.lean` is the topology on `X.Etale`;
  source lowerStar uses its base-change functor.
- `def-weil-pbc-abelian-etale-sheaves`: `Sheaf J AddCommGrpCat` is exactly the
  full category of abelian sheaves in the dependency's note.
- `def-weil-pbc-derived-categories`: opened the source
  `SixFunctors/Etale/Derived/Coefficients.lean`, where
  `DerivedCategoryModule Λ X` is literally
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  Opened Mathlib `DerivedCategory/Plus.lean`: `singleFunctor` inserts a sheaf
  in the specified degree, and `homologyFunctor` composes inclusion of D+
  with the derived cohomology functor. We use these existing constructions.
- `def-weil-pbc-direct-image`: opened `UpperLowerStar/Defs.lean`:
  `lowerStar` is precomposition with étale base change, for arbitrary h.
  The recorded derived declaration actually lives in the imported
  `Derived/UpperLowerStarCoherence.lean`; opened its signature and body:
  `rightDerivedLowerStarPlus` is `lowerStar.rightDerivedFunctorPlus`.
  Both categories in its signature are D+ of the required abelian sheaves.

Edge cases: q=0 is excluded by `0 < q`, and every positive natural degree is
included and cast to the same integer cohomology degree. Zero sheaves and
empty schemes are allowed. There is no index family to constrain. Any
characteristic, the zero ring, Z, and prime-field coefficients are allowed.
The scheme universe u is arbitrary; coefficients and abelian sheaf values are
in u+1, the established six-functor encoding (smaller rings may be lifted).
No independent test universe or extra smallness/Noetherian instance is added.
All variables and universes are bound. No local notation, local instance,
private definition, let binder, or hollow definition occurs. The sole theorem
has proof `by sorry`; nothing is proved.

Independent searches, with different phrasing from the first worker:

- LeanFinder via msearch: "functor sends a split subobject of an acyclic sheaf
  to a zero object" returned generic injective derived-vanishing and complex
  acyclicity lemmas, no statement of higher direct-image vanishing on retracts.
- Loogle via msearch: `CategoryTheory.Limits.IsZero.retract` returned the
  opposite-direction construction: a zero object is a retract of every object.
  Opened the reported signature; it is not this item.
- Grep via msearch: `acyclic|Retract|IsZero`, scoped to `SixFunctors/Etale`,
  returned no exact statement.
- Direct rg over Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json for `vanishing_descends_retract`,
  `vanishing.*summand`, `acyclic.*retract`, `retract.*acyclic` found only generic
  acyclic-complex retract material and perfect-summand material, not this
  geometric statement or a colliding declaration name. Generic retract facts
  remain proof leaves, not an existing record for this node.

There are no new definition nodes, dependency modules or statement correction.
The JSON lean.statement is verbatim the final signature. The repaired module
compiled cleanly with scompile.py on the server (2.8 seconds, exit code 0).
