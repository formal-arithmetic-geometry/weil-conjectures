## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction` states
`AlgebraicGeometry.Scheme.exists_perfect_generator_of_open_union_affine`, with proof `sorry`.
No definition is duplicated, no dependency module or new node is needed, and the node's
statement is unchanged. Read Stacks Tag 09IS at https://stacks.math.columbia.edu/tag/09IS,
particularly its induction step beginning with the cover X = U union V. The local literature
copy perfect.tex is unavailable here; the official page supplies the source. The theorem's
docstring includes all four proof steps and the helper nodes used by each.

Hypotheses and clauses, individually:
- Scheme X: `X : Scheme.{u}` (arbitrary universe u).
- Quasi-compact X: `[CompactSpace X]`.
- Quasi-separated X: `[QuasiSeparatedSpace X]`.
- Open subschemes U and V: `U V : X.Opens`, with U's scheme `U.toScheme`.
- Quasi-compact U: `hU : IsCompact (U : Set X)`.
- Affine V: `hV : IsAffineOpen V`.
- Cover: `hcover : U ⊔ V = ⊤`.
- P in D_QCoh(O_U): `P : schemeDerivedQCohCategory U.toScheme`.
- P perfect: `hP : IsPerfect U.toScheme P.obj`.
- P generator: `hgen : IsWeakTriangulatedGenerator P` on the full subcategory.
- Q and K' in D(O_X): `∃ Q K' : schemeDerivedCategory X`.
- Q perfect and K' perfect: `IsPerfect X Q ∧ IsPerfect X K'`.
- P a summand of Q restricted to U: maps `ι` and `π` with `ι ≫ π = 𝟙 P.obj`.
  The restriction is `overFunctor` composed with the canonical `Modules.overEquiv U`
  and then `mapDerivedCategory`. Thus both maps live in the actual D(O_U), with the
  same shared SheafOfModules category instance as the dependency definitions.
- Support of K' on V minus U: for every integer n and point x outside the set difference,
  `Subsingleton ↑(TopCat.Presheaf.stalk (H^n(K')).val.presheaf x)`.
  The stalk is an additive group, whose underlying type is explicitly coerced; subsingleton
  says it is the zero group. This is exactly cohomology-sheaf vanishing on the complement.
- The direct sum generates D_QCoh(O_X): `Q ⊞ K'` has witness `hqc` of
  `schemeDerivedQCohProperty X`, and the bundled object is an `IsWeakTriangulatedGenerator`.

The HasDerivedCategory binders fix the shared derived localizations (global, localized opens,
and U). The IsTriangulated binders specify the inherited triangulated structures of D_QCoh;
they express the category structure presupposed by the generator definition, without imposing
an additional geometric hypothesis. The locally enabled generic functor instances allow the
canonical open equivalence to be used as an exact additive functor.

Dependency declarations read and used:
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  read Scheme.lean's structure and docstring.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`; read the entire definitions.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`; read its full signature,
  local covering definition, and `IsStrictlyPerfect` definition.
- `Sheaf.CategoryTheory.WeakTriangulatedGenerator`: `IsWeakTriangulatedGenerator`;
  read its hypotheses and nonzero-map-into-shift definition.
- Mathlib Modules.Sheaf: `Scheme.Modules.overEquiv` (line 558) and
  `overFunctorEquiv` (line 605), read docstrings and signatures. The latter explains the
  agreement with restriction to the open subscheme; no new restriction definition is made.

Edge cases checked: U = X allows K' = 0 since the support set is empty; V contained in U
has the same behavior. U empty reduces to the affine generator case, with P necessarily zero
in the empty category. X empty permits Q = K' = 0 and weak generation is vacuous. Integer
shifts include zero and negative shifts. No nonemptiness or nonzero hypothesis was added.
The retract formulation equals a direct summand in this additive triangulated category.
Under the cover, V minus U equals X minus U and is therefore closed in X.

Searches actually run via /home/ubuntu/weil-launcher/msearch.py for this item:
- leanfinder: `perfect generators extend across an affine open cover of a quasi compact
  quasi separated scheme`: eight generic affine-cover results, none the theorem.
- loogle: `DerivedCategory, IsWeakTriangulatedGenerator`: zero hits, unknown identifier
  IsWeakTriangulatedGenerator (it is our project definition, not a Mathlib declaration).
- leansearch: `perfect generator derived quasi coherent category affine open induction`:
  unavailable, Internal Server Error; not interpreted as a negative search.
- grep: `perfect.*generat|generat.*perfect`, Mathlib AlgebraicGeometry: zero hits.
- rg in source WeilConjectures for the item id and perfect/generator patterns: no item
  declaration; only unrelated finite generation of modules over perfect rings/fields.
- rg in lean/Sheaf for perfect generators, IsWeakTriangulatedGenerator, derived QCoh,
  IsCompact and IsAffineOpen: located the shared definitions and QcOpenDerivedLift,
  AffinePseudoCoherentLift, and DerivedQCohCompactGeneration. These are different claims.
- tools/lean_names_upstream.py show for the item: no named exact declaration returned.

Server compilation completed cleanly, exit code 0, in 4.1 seconds. All variables and
universes are explicit (`set_option autoImplicit false`). There are no node faults or
statement disputes.

## Second reading by G1

I reread the node statement, its Tag 09IS induction-step source, and the theorem signature.
The introduced objects and hypotheses match as follows: `X : Scheme.{u}` with
`[CompactSpace X]` and `[QuasiSeparatedSpace X]` renders the quasi-compact,
quasi-separated scheme; `U V : X.Opens` renders the two opens; `hU : IsCompact
(U : Set X)` renders quasi-compactness of U; `hV : IsAffineOpen V` renders
affineness of V; and `hcover : U ⊔ V = ⊤` renders X = U union V. The derived-category
`HasDerivedCategory` and triangulated-property binders provide the shared categories
presupposed by the dependency definitions. `P : schemeDerivedQCohCategory U.toScheme`
with `hP : IsPerfect U.toScheme P.obj` and `hgen : IsWeakTriangulatedGenerator P`
renders a perfect generator on U.

The conclusion is rendered clause by clause: `∃ Q K' : schemeDerivedCategory X`
introduces the two objects; `IsPerfect X Q ∧ IsPerfect X K'` gives their perfectness;
the existential maps `ι` and `π` have source and target in the canonical restriction
of Q to `D(O_U)` and satisfy `ι ≫ π = 𝟙 P.obj`, exactly the direct-summand clause;
the quantified integer and point support condition says every stalk of every
cohomology object of K' is subsingleton outside `(V : Set X) \ (U : Set X)`;
and `∃ hqc, IsWeakTriangulatedGenerator (⟨Q ⊞ K', hqc⟩ ...)` gives the direct-sum
generator of `D_QCoh(O_X)`. Quantifier order is unchanged. No mismatch was found and
no code change was required.

Edge cases checked: empty U, V contained in U, U = X (with K' = 0), empty X,
zero objects, and all integer shifts including zero and negative integers are admitted;
there is no nonemptiness or characteristic hypothesis and the universe parameters are
explicit.

Searches found no existing declaration: LeanFinder returned only generic affine-cover
lemmas; Loogle returned zero hits for `DerivedCategory, IsWeakTriangulatedGenerator`;
LeanSearch was unavailable (recorded as such); grep found no perfect-generator theorem
in Mathlib AlgebraicGeometry; repository and upstream-name searches found no exact
notion or statement. The existing dependency declarations are used directly and no new
node or dependency module is needed.

## Reviewer fix (R-poi1508)

Generation is restated in the landed sibling form of lem-pc-perfect-generation-affine-base
(C1 773f742f5): the hypothesis on P is
`∀ E : schemeDerivedQCohCategory U.toScheme, IsZero E.obj ↔ ∀ n : ℤ, Subsingleton (P.obj⟦n⟧ ⟶ E.obj)`
and the conclusion is `schemeDerivedQCohProperty X (Q ⊞ K') ∧ ∀ E : schemeDerivedQCohCategory X,
IsZero E.obj ↔ ∀ n : ℤ, Subsingleton ((Q ⊞ K')⟦n⟧ ⟶ E.obj)`. This drops the two added hypotheses
`[(schemeDerivedQCohProperty X).IsTriangulated]` and `[(schemeDerivedQCohProperty U.toScheme).IsTriangulated]`
(not part of the node; the induction's citers would have had to supply them) and the
`IsWeakTriangulatedGenerator`-on-the-subcategory form, so base case and induction step chain
in one form. The Triangulated.Subcategory and WeakTriangulatedGenerator imports are replaced by
Sheaf.AlgebraicGeometry.DerivedCategory. Everything else (restriction via overFunctor ⋙ overEquiv U
as G1 ce180b4c0, retract ι ≫ π = 𝟙, stalkwise support of every H^n(K') off V \ U) is unchanged.
