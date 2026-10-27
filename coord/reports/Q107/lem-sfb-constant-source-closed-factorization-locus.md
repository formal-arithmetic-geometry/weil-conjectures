## Worker report

The module `Sheaf.AlgebraicGeometry.ConstantSourceClosedFactorizationLocus` states
`AlgebraicGeometry.existsUnique_constantSource_closedFactorizationLocus` with a single
`sorry` proof. There are no new definitions, additional nodes, dependency repairs, or
statement corrections. The source was read directly with pdftotext: Milne, Algebraic
Groups (2017), printed pp.35–38, particularly 1.100–1.105. The docstring contains all
eight steps of the node's proof, including the coordinate ideal, arbitrary algebra
tests, principal-open compatibility, two gluings, uniqueness, and base change.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`, with no characteristic restriction.
- The three k-schemes are `Y X S : Over (Spec (.of k))`; their structure maps are
  `Y.hom`, `X.hom`, and `S.hom`.
- Separatedness is the three `IsSeparated` instances. Finite type is, for each
  structure map, `LocallyOfFiniteType` and `QuasiCompact`, exactly the conjunction
  specified by the recorded dependency. Properness is not assumed: that dependency
  supplies the definition of separatedness.
- The closed immersion is `(W : Scheme.{u}) (i : W ⟶ X.left) [IsClosedImmersion i]`.
  W has the induced k-structure `i ≫ X.hom`. No independent choice of structure is
  required, and every closed k-subscheme is covered by this encoding.
- The family is `f : pullback Y.hom S.hom ⟶ X.left`; its k-linearity is exactly
  `hf : f ≫ X.hom = pullback.snd Y.hom S.hom ≫ S.hom`.
- A closed subscheme of S is encoded by `I : S.left.IdealSheafData`, with
  `L = I.subscheme` and inclusion `I.subschemeι`. These are Mathlib's existing
  constructions; the closed-immersion instance is supplied by ClosedImmersion.
  `IsClosedImmersion.overEquivIdealSheafData` identifies this encoding with closed
  immersions over S. `∃! I` therefore gives uniqueness as a closed subscheme,
  rather than the incorrect literal uniqueness of a presentation by a scheme.
- For every test scheme and parameter map, the first quantified clause uses
  `(T : Scheme.{u}) (s : T ⟶ S.left)`. The induced structure is `s ≫ S.hom`.
  Every k-scheme with a k-map to S has exactly this structure; conversely every
  displayed s is such a k-map for the induced structure. There is no finite-type,
  separatedness, affineness, nonemptiness, or reducedness condition on T.
- The left side of the first equivalence is the unique factorization
  `∃! l : T ⟶ I.subscheme, l ≫ I.subschemeι = s`. The right side is existence of
  `w : pullback Y.hom (s ≫ S.hom) ⟶ W` with composite i equal to
  `pullback.map ... (𝟙 Y.left) s (𝟙 (Spec (.of k))) ... ≫ f`.
  This is precisely `f ∘ (id_Y × s)`. Uniqueness on the left is equivalent to
  existence, since the inclusion is a closed immersion and hence a monomorphism.
  The equation for w also forces w to respect the induced k-structures.
- The subfunctor/representability assertion is expressed by these unique lifts:
  composing with `I.subschemeι` identifies Hom_k(T,L) bijectively with the subset
  of Hom_k(T,S) given by the right side. Precomposition of a lift is its restriction
  to a new test scheme, and precomposition on the right uses the product map.
  Consequently this is the full natural represented subfunctor, and not merely
  a statement about geometric or field-valued points. No additional construction
  or arbitrary comparison map is used.
- The second clause quantifies over `(S' : Scheme.{u}) (b : S' ⟶ S.left)` without
  further hypotheses. It asserts closedness of the actual pullback projection
  `pullback.snd I.subschemeι b`, and the identical unique-lift criterion for every
  `(T : Scheme.{u}) (t : T ⟶ S')`. Its family is the original family pulled back
  along `t ≫ b`, written using `pullback.map`. Functoriality of product maps
  identifies this with first pulling the family along b and then along t.
  The uniqueness quantifier includes both the original and base-change clauses;
  the latter follows formally from the original by the pullback property, so this
  is also uniqueness among closed subschemes satisfying the original property.

Recorded statement dependencies used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`, supplied by
  Mathlib.AlgebraicGeometry.Morphisms.Proper through Morphisms.Separated.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.snd`, and
  `pullback.map`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback;
  scheme pullbacks are supplied by Mathlib.AlgebraicGeometry.Pullbacks.

All six dependency nodes and their records were read, along with the source signatures
and docstrings. The example Sheaf compact-object file is now withdrawn, so its recorded
upstream file `WeilConjectures.CategoryTheory.CompactObject` was read for the conventions.
Proof imports supply the recorded Mathlib inputs: closed-immersion base change and
affine criterion, proper monomorphisms, spectra of tensor products, bases and base
change, morphism gluing, open products, ideal-sheaf closed subschemes, and affine opens.

Edge cases checked before writing: empty Y gives L = S, and the two universal
conditions are always satisfied; W = X likewise gives L = S. Empty S gives its
unique empty closed subscheme. With W empty and Y nonempty, L is empty (with Y
empty it is S). For the nonreduced parameter example Y = Spec k, S = Spec k[ε]/ε²,
X = affine line and f defined by ε, with W the origin, L is Spec k, not its ambient
parameter scheme. The formulation retains that ideal and accepts nonreduced tests.
All universes and variables are explicit; the common Scheme.{u} universe is arbitrary
and is also the universe of the field and test schemes, as in the project convention.

Searches performed:

- msearch leanfinder, query: "A family Y times S to X over a field factors through
  a closed subscheme on a unique closed parameter subscheme of S". Eight hits:
  IsClosedImmersion.lift/lift_fac, valuative criteria, scheme image factorization,
  immersion liftCoborder, and separatedness/dominance lemmas. None constructs the
  locus for an entire family with constant source.
- msearch loogle, query: `"IsClosedImmersion"`. Twelve hits, including the class,
  stability under base change, locality, affine morphisms, and subscheme inclusion;
  none gives the factorization locus.
- msearch grep, query: `factor.*[Cc]losed|[Cc]losed.*factor|factorizationLocus|closedSubfunctor`,
  directory AlgebraicGeometry. Five hits in Morphisms/Immersion, all descriptions
  of an immersion's open/closed factorization, not this theorem.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures, and Sheaf for closed subfunctors,
  factorization loci, constant-source closed conditions and the proposed declaration
  name; also searched dag/lean_names_upstream.json. Existing hits are the Hilbert
  closed-subfunctor theorem and downstream group-scheme consumers, not this statement.
  The explicit node-id grep in WeilConjectures gave no declaration. No duplicate
  definition or theorem was found. Raw msearch records are in sandbox searches.jsonl.

Validation: scompile.py compiled the statement cleanly in sandbox and library module
modes (4.8 s and 5.5 s). The final exact file is compiled again by the required dry
run and delivery. No `#check`, local notation, private declaration, local instance,
or automatic implicit variable remains.

## Second reading by Q107

A separate in-thread rereading checked the complete node against the delivered
signature and the eight-step docstring. No sub-agent was started, as the dispatcher
requires; the maintainer's independent review is still the delivery review.
The check matched the nine separated/finite-type hypotheses, the closed immersion,
the k-morphism equation, the actual fibre products and product maps, both directions
of the factorization condition for arbitrary test schemes, uniqueness as a closed
subscheme, the represented subfunctor, and arbitrary base change. In particular,
no properness assumption was substituted for separatedness, and no reduced or
finite-type restriction was imposed on test schemes or new bases. W and each test
scheme use the forced induced k-structure, not an extra assumption. The unique-lift
wording is justified by the existing closed-immersion monomorphism property.
No mathematical mismatch or statement dispute was found. Two explicit public
imports for the recorded scheme and pullback modules were added after this check;
the final dry run compiles that exact file.
