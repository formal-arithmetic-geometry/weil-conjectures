## Worker report

The module `Sheaf.Paper.ConstructibleCompactness` states
`AlgebraicGeometry.ProEtale.constructible_compactness`, with exactly one postponed
proof, `by sorry`. It also supplies two real-data helpers belonging to this assertion:
`constructibleCompactnessComparison`, the displayed canonical additive map, and
`HasConstructibleCompactness`, which expands the two conclusions without introducing
another construction of any coefficient ring, constructibility predicate or category.
No node statement or dependency list is changed, and no new DAG node is needed.
One dependency module receives the compile-interface repair described below.
There is no repair note for this item.

Hypothesis and clause correspondence:

- The fixed global tuple `(p,a,q,k₀,k)` is `D : WeilConjectures.FiniteFieldDatum.{u}`.
  Its fields require `p.Prime`, `1 ≤ a`, `q = p ^ a`, a finite field `k₀` with
  `Nat.card k₀ = q`, and `[IsAlgClosure k₀ k]`. Thus the base is the specified
  algebraic closure of a finite field, not an arbitrary field.
- The prime different from the characteristic is `(ℓ : ℕ) [Fact ℓ.Prime]`
  and `(hℓ : ℓ ≠ D.p)`.
- The fixed coefficient algebraic closure is the dependency's `PadicAlgCl ℓ`.
  The finite subextension is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`;
  this is a subtype of intermediate fields of `ℚ_[ℓ]` in `PadicAlgCl ℓ`
  with `FiniteDimensional ℚ_[ℓ] E`. Using the fixed algebraic closure of the
  coefficient-ring dependency gives its actual canonical coefficient objects.
- The alternatives `Λ = E` and `Λ = Q̄_ℓ` are the two conjuncts of the theorem:
  `HasConstructibleCompactness (Profinite.continuousMapRingObj E) X` and
  `HasConstructibleCompactness (Profinite.padicAlgClRingObj ℓ) X`.
  The latter is the finite-subextension-valued subsheaf, not all continuous maps
  into the valuation-topological algebraic closure. Both use their canonical
  ring-object instances; no arbitrary multiplication is quantified.
- `X` separated and of finite type over `k` is `(X : Scheme.{u})`,
  `[X.Over (Spec (.of D.k))]`, `[IsSeparated (X ↘ Spec (.of D.k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
  `[QuasiCompact (X ↘ Spec (.of D.k))]`. The last two together are finite type.
- The pulled-back ring is `condensedRingObj Λ X`, the underlying object of
  the recorded `coefficientRing X (Mon.mk Λ)` construction along `p_X^*`.
- The ambient category in both clauses is exactly
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X))`. This is the ordinary unbounded module-object
  derived category, namely the layer-(B) row of sk-def-sfb-derived-categories.
- `Cons` uses the recorded `IsConstantModelConstructible Λ X` throughout.
  `Dbc` is the recorded `constantModelBoundedConstructible Λ X`: bounded
  for the standard t-structure with every cohomology sheaf satisfying that
  same finite constant local-model predicate. There is no finite Tor or
  derived-completion condition, and no use of arbitrary local presentation
  matrices to redefine constructibility.
- `IndCons` is `ObjectProperty.ind.{u + 1}
  (IsConstantModelConstructible Λ X)`, Mathlib's actual filtered-colimit
  presentation in the ambient module category. `Dic` is imposed inline as
  `∀ (i : I) (n : ℤ), ... ((DerivedCategory.homologyFunctor _ n).obj (K i))`.
  In particular the family is not required to have a common cohomological bound.
- The closure is `(localizingClosure (constantModelBoundedConstructible Λ X))`.
  Its recorded definition is the intersection of full replete triangulated
  subcategories containing exactly the chosen class and closed under ambient
  coproducts. The specialized `localizingClosureProEtale` is deliberately not
  used, since it generates from Dctf whereas this node generates from Dbc.
- The first assertion explicitly supplies coproducts in that full subcategory
  and, for every bounded constructible `C`, membership `hC` in the closure and
  `IsCompactObject (ObjectProperty.FullSubcategory.mk C hC)`. This uses
  def-pc-compact-object literally. Existence of membership and coproducts records
  the structures required to read compactness and follows from the closure
  construction and det-def-localizing-closure-existence, not an added assumption.
- The stronger assertion quantifies over every bounded constructible ambient
  `C`, every `I : Type (u + 1)`, and every `K : I → DerivedCategory ...` with
  the stated `Dic` membership. It supplies `(c : Cofan K) (_ : IsColimit c)`
  and bijectivity of `constructibleCompactnessComparison C K c`.
  The latter is exactly `DirectSum.toAddMonoid fun i ↦
  Preadditive.rightComp C (c.inj i)`. Thus its domain is
  `⨁ i : I, (C ⟶ K i)` and its target is `C ⟶ c.pt`; every Hom and coproduct
  is ambient. Bijectivity of this additive group homomorphism is precisely
  being an isomorphism. Using a colimit cofan states existence as well as the
  comparison, without assuming a chosen coproduct; the unique compatible
  isomorphism transports the assertion to any other coproduct.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, including
  its field and algebraic-closure instances; its `CoefficientDatum` convention
  was also read.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, reexporting
  the continuous-function coefficient constructors.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `Profinite.padicAlgClRingObj`, and its
  commutative ring-object instance. This node has a closed upstream audit rather
  than a `lean` record; the audited declarations are used directly.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`:
  `PadicAlgCl.FiniteIntermediateField` and its finite-dimensional and normed-field
  instances, and `Profinite.continuousMapRingObj` from the public import closure.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`, and the preservation
  of commutativity. Read in the specified shared 51-module framework.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  sk-def-sf-setting's recorded convention module is imported. The geometry and
  rational module coefficients required here use the finite-field datum and the
  ordinary pro-etale module-object interfaces, rather than its finite-stage
  etale coefficient category.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `IsConstantModelConstructible`, `constantModelBoundedConstructible`, and their
  full-subcategory encodings; the full definition and finite-constant-model
  construction were read.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded ambient derived-category convention module is imported. The
  relevant ambient category is Mathlib `DerivedCategory`, not its distinct
  bounded-constructible row.
- `Sheaf.Paper.LocalizingClosureExistence`: `localizingClosure_exists` and
  `CategoryTheory.localizingClosure` from `Sheaf.Paper.LocalizingClosure`.
- `Sheaf.CategoryTheory.CompactObject`: `CategoryTheory.IsCompactObject`.
- Mathlib `CategoryTheory.ObjectProperty.ind`, `DerivedCategory`,
  `DerivedCategory.homologyFunctor`, `DirectSum.toAddMonoid`,
  `Preadditive.rightComp`, `Cofan`, `IsColimit`, `HasCoproducts`, and
  `ObjectProperty.FullSubcategory` are reused directly.

The currently recorded proof modules are imported without `public`:
`Sheaf.Paper.AmbientIndDerivedTriangulated`,
`Sheaf.Paper.ConstructibleCompactnessBounded`,
`Sheaf.CategoryTheory.CompactObjectsThick`,
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, and
`WeilConjectures.CategoryTheory.TruncationTriangle`.
At initial inspection, det-ambient-ind-derived-sums,
sk-lem-uniform-constructible-ext, and sk-lem-finite-window have no recorded
module; the docstring retains all their proof uses. All five DAG proof steps
are transcribed, including the natural finite-window square, finite Postnikov
induction and the final restriction from Dic to Loc(Dbc).

Edge cases checked before writing:

- The empty index type is allowed: no `Nonempty I` assumption occurs; the cofan
  is the zero coproduct and both Hom groups are zero.
- Zero source and the empty scheme are allowed; no nonzero or nonempty condition
  on `C` or `X` is introduced.
- A source with one nonzero cohomology sheaf and a width-zero truncation window
  are included, as are arbitrary positive and negative shifts of the source.
- Unbounded families, and families whose individual bounds have no uniform
  interval, remain admissible because `hK` imposes only ind-constructibility in
  each degree. Only the source is bounded.
- `E = ℚ_ℓ` is included as the bottom finite intermediate field. The full
  algebraic closure uses its finite-subextension-valued condensed sheaf.
- The excluded case `ℓ = p` remains excluded by the exact explicit hypothesis;
  no additional primality or characteristic restriction is imposed.
- Sums and filtered diagrams use the fixed `u + 1` coefficient/site universe.
  The small pro-etale site retains its existing object and morphism universes.

Searches made through `msearch.py Q51 sk-thm-constructible-compactness`:

- `leanfinder`, query "Bounded constructible complexes of rational pro-etale
  sheaves are compact in the ind constructible derived category": eight hits,
  about condensed Grothendieck categories, solidity and derived t-structures;
  none states this assertion.
- `loogle`, query `CategoryTheory.IsCompactObject, DirectSum.toAddMonoid`:
  zero hits, unknown Mathlib identifier `CategoryTheory.IsCompactObject`.
- `grep`, query `constructible.*[Cc]ompact|[Cc]ompact.*constructible`:
  thirteen Mathlib hits, all about constructible subsets and topology,
  not rational pro-etale derived compactness.
- `leansearch`, query "Hom from bounded constructible rational complexes commutes
  with direct sums of ind constructible complexes": eight hits, on generic
  HomologicalComplex and DirectSum operations; no exact match.
- `rg` on the prescribed upstream `WeilConjectures` and shared `lean/Sheaf`
  sources found finite-coefficient compactness and the bounded-family lemma,
  but neither gives compactness for arbitrary unbounded ind-constructible
  families and a general bounded constructible source with rational coefficients.
  Searching `sk-thm-constructible-compactness` found only source citations in
  the bounded-family module. Searches of the proposed declaration names in
  Mathlib, upstream, shared sources and `dag/lean_names_upstream.json` found no
  collision. The generic cofan comparison has an arbitrary derived source;
  `constructibleBoundedComparison` instead requires a sheaf source in degree zero.

No `STATEMENT-DISPUTED` issue or node correction was found. The proof remains
entirely postponed, as required for stage 2.


## Dependency modules

`det-constructible-compactness-bounded`, module
`Sheaf.Paper.ConstructibleCompactnessBounded`: its recorded declaration was
mathematically exact, but the module was unusable for this consumer because the
prescribed compiler repeatedly timed out at 60 seconds in that dependency, both
in the local overlay and on server confirmation, before reaching the item.
Reading its current server source with `scompile.py --source` confirmed that it
matched the shared checkout. A sandbox profiler copy showed all three signatures
elaborating, but the full file still exceeded the limit. Removing this proof
import only in a diagnostic copy of the consumer allowed the consumer to compile
cleanly (28.5 seconds sandbox, 20.3 seconds library), isolating the problem.

The repaired interface explicitly binds `[HasDerivedCategory.{u + 1} A]`
for the actual module category `A` in each of the two bounded theorems. This is
only the choice of a small-Hom localization that the coefficient/site universe
convention already requires. It exists by the imported Grothendieck abelian
instance, which callers can still synthesize automatically; the binder does not
assume an extra geometric fact, impose an equality of universes, or restrict
objects. Making the chosen localization a parameter avoids repeated normalization
of its full construction. The original comparison definition, theorem names,
geometric and coefficient hypotheses, interval and family conditions, and
conclusions are retained. The helper still takes the original sheaf source in
degree zero; its definition and proof docstrings are verbatim from the published
module. The theorem signatures are refreshed in the node's `lean` record.

The unrelated public import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
is removed. `CondensedConstantConstructibility` already supplies the ordinary
derived module categories and their canonical instances. The currently recorded
proof dependencies `Sheaf.Paper.LocalizingClosureExistence` and
`Sheaf.Paper.DetIndHeartIISums` are added as non-public imports. There are no
existing direct importers of the bounded module in the shared sources. The
consumer imports the same module under its recorded name, so there is no second
copy or alternate statement of the bounded theorem. The dependency node changes
only in `lean`, with its signature refreshed and a note explaining the interface
repair.

The dependency's statement is unchanged, clause by clause: arbitrary field `k`
of positive characteristic `p ≠ ℓ`; separated finite-type `X` over `k`; a finite
coefficient subextension `E` or the finite-subextension-valued algebraic closure;
constructible sheaf `C` in degree zero using finite constant scalar models;
integers `a ≤ b`; every small family with ind-constructible cohomology vanishing
outside `[a,b]`; a coproduct cofan and bijectivity of its shifted-coprojection Hom
comparison for every integer shift `s`. The original real-data comparison and full proof docstrings are retained. Empty families, `a=b`, negative shifts,
the zero source and the empty scheme remain allowed. Only the dependency node's `lean` record is refreshed; its module and declaration
names are retained, and its signature is copied verbatim from the repaired file.


Validation: both final delivered Lean files compiled cleanly through the prescribed
`scompile.py` machinery used by `deliver2.py --no-push`, individually and in
module-dependency order, with the unchanged 60-second limit, two threads and
nice 19. There were no errors or unexpected warnings. Both node signatures were
also checked against the exact theorem signatures in the delivered files.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
