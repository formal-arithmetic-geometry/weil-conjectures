## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.compactification_localizing`
in `Sheaf.Paper.CompactificationLocalizing`. There is one theorem with proof `sorry`,
no definitions, no extra hypotheses on the derived categories, and no statement correction.
The node copy changes only `lean`. The original statement and all dependency lists remain.

Read the current node, every statement-dependency statement and declaration record,
their source declarations and docstrings, both proof-dependency statements, the current
blueprint statement and its three-paragraph proof, and the framework manifest. No repair
note exists for this item. The existing stage-1 finite-type-over-a-field clarification
is retained.

Hypotheses, clause by clause:

- Prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- The field is `(k : Type u) [Field k]`; positive characteristic different from ell
  is `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`. A field's nonzero
  characteristic is prime, so this does not impose an extra characteristic restriction.
- `X Y : Scheme.{u}` have `[X.Over (Spec (.of k))]` and its Y counterpart.
  Separated finite type over k is the explicit triple `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` on each structure map. No algebraic closedness,
  finite-field, properness of X or Y, or smoothness is assumed.
- The specified morphism is `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`, with
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` for separated finite type.
- Y qcqs is `[CompactSpace Y] [QuasiSeparatedSpace Y]`. These explicit hypotheses
  repeat consequences of the standing assumptions, as does the node's own qcqs clause.
- `(c : Compactification.BoundaryCompactification f)` is the exact recorded compactification
  notion. Its object `c.obj.obj : Compactification f` supplies the proper map g, open
  immersion i, and `f = i ≫ g`; the full-subcategory property supplies quasi-compactness
  of i. The wide-subcategory restriction changes morphisms between compactifications,
  not objects. There is no density or chosen-compactification condition on this c.
- Λ is a commutative internal ring of condensed abelian groups, the same object used
  throughout the recorded module-object framework. `_hΛ` lists all admissible coefficients,
  up to isomorphism of ring objects. The finite clause quantifies a finite commutative
  discrete topological ring A in `Type u`, killed by an ell power. The next clauses give
  Z_ell and Q_ell with continuous-function condensed realizations. The finite intermediate
  field clause gives both O_E and E for a finite subextension of the fixed PadicAlgCl ell.
  The last clause is the published finite-subextension condensed algebraic closure,
  following the coefficient convention in the source framework, also used by the existing
  proper/open interchange statement. All topologies are specified by those constructions;
  no arbitrary ring object is admitted merely because its scalar ring looks admissible.

Conclusions, clause by clause:

- The functor is exactly `rightDerivedLowerShriekOfCompactification Λ c.obj.obj`,
  definitionally `(openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor`. Thus it is the levelwise exact extension
  by zero followed by total derived proper pushforward, with the same Λ on both sides.
- The first conjunct says `localizingClosureProEtale Λ X K →
  localizingClosureProEtale Λ Y (F.obj K)` for every ambient object K. Since these are
  full subcategories, this is precisely existence of the canonical restriction: its
  objects are `⟨F.obj K.obj, preservation K.obj K.property⟩` and its maps are `F.map`.
  No arbitrary substitute functor or mere nonempty choice is introduced.
- The second conjunct says every distinguished ambient triangle with its three vertices
  in the source closure maps to a distinguished ambient triangle. `F.mapTriangle` uses
  the actual composite shift comparison: exact levelwise derivation for i and the
  K-injective right-derived comparison for g. The full closure inherits its triangles
  and shifts from the ambient category, so this is exactly triangulated exactness of
  the restriction, without asserting an additional theorem about other ambient objects.
- The third conjunct uses `PreservesColimit K F` for every discrete diagram whose
  objects are in the source closure. This is preservation of the actual ambient
  coproduct cocones, hence of their canonical comparisons. No arbitrary isomorphism
  between unrelated objects substitutes for coproduct preservation. `I : Type (u + 2)`
  agrees with the indexing universe of the recorded `CategoryTheory.IsLocalizingSubcategory`
  applied to this ambient category; the source category has object universe u+2 and hom
  universe u+1, verified with an scompile diagnostic. Smaller index types are included
  by universe lifting. `PreservesColimit` quantifies every existing colimit cocone, just
  as the recorded closure definition quantifies ambient coproducts when they exist.
- The final conjunct is preservation of `constantModelBoundedConstructible Λ X K ∧
  DerivedCategory.finiteTorAmplitude _ K`, exactly the object predicate of the recorded
  `ConstantModelConstructibleFiniteTor Λ X`. Both bounded constructibility and finite
  Tor amplitude remain explicit in the target. No Dctf=Dbc simplification is made.

Dependency declarations used:

- `sk-def-sfb-dc-setting`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` and its documented
  standing scheme binders. The present theorem quantifies the given c rather than
  selecting that chosen compactification. This module is imported as recorded.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and
  `ConstantModelConstructibleFiniteTor`, reached through LocalizingClosure. Its full
  finite-constant-model and affine-local construction is used without a private copy.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingClosure`,
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` and its generic
  `CategoryTheory.localizingClosure` / `IsLocalizingSubcategory` definitions.
- `sk-def-sfb-module-derived-pushpull`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`,
  `CategoryTheory.Functor.rightDerivedFunctor` applied to the recorded lowerStar;
  this is used inside the recorded compactification functor, not copied.
- `sk-def-sfb-module-derived-lower-shriek`: published
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`,
  `AlgebraicGeometry.ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification`.
- `sk-def-nagata-sketch-data`: `Sheaf.Compactification.BoundaryRefinement`,
  `AlgebraicGeometry.Compactification.BoundaryCompactification` and `QuasiCompactObjects`.
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`.
- `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` / `IsSeparated`, through the compactification structure.
- `def-weil-pbc-quasi-compact-scheme`: Mathlib `Topology.Defs.Filter`, `CompactSpace`.
- `def-weil-quasi-separated-morphism`: Mathlib `AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `AlgebraicGeometry.QuasiSeparated` and the corresponding `QuasiSeparatedSpace` scheme
  convention. The latter is the scheme condition written by this node's qcqs phrase.
- Coefficient realizations are the published `Profinite.continuousCoefficientRingObj`
  (`Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`), `continuousMapRingObj`,
  `padicIntegersRingObj`, `padicSubfieldCondensedRing`, `padicAlgClRingObj`
  (`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`).
- The public `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
  import supplies the canonical `CommShift` instance needed to state `mapTriangle`.
  This was missing from the initial import list and repaired after the first compiler error.

Both proof dependencies, `det-proper-image-localizing-open` and
`det-proper-image-localizing-proper`, currently have no Lean record. They are not notions
needed to state this theorem: its docstring records their complete intended use. There
is therefore no proof-only module to import yet. The maintainer can add the imports
when those theorem modules are stated, under stages/2-statements.md rule 7.

Edge cases checked: X and Y may be empty. The compactification need not be dense and
may contain an extra proper component disjoint from X; extension by zero is zero there.
Identity/proper compactifications and open-immersion compactifications specialize to the
corresponding factor. The zero complex and empty coproduct are included. No nonempty
index type, positive cohomological degree, nonzero coefficient ring, or fixed Tor interval
is required. A zero finite coefficient ring is allowed (including exponent n=0), while
nonzero finite rings are included at every permitted exponent. E=Q_ell is allowed and
Z_ell/Q_ell are also explicitly included. All universes and variables are explicitly bound.

Searches performed using msearch.py with group N3 and this item:

- LeanFinder: "Derived proper pushforward after extension by zero preserves constructible
  finite Tor complexes and restricts to a triangulated functor preserving coproducts on
  their localizing closure". Eight generic derived-functor, exact-functor and homological
  descent hits; none states the geometric preservation result.
- Loogle: `CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Limits.PreservesColimitsOfShape`. Zero hits for the conjunction query.
- Mathlib grep: `localizingClosure|Localizing|rightDerivedLowerShriek` in CategoryTheory.
  Six hits, concerning Verdier right/left-localizing subcategories and site localization;
  these are different notions.
- LeanSearch: "Compactification proper pushforward extension by zero exact coproduct
  preserving localizing constructible finite Tor derived category". Eight generic hits,
  including `Functor.mapDerivedCategoryFactors`, `DerivedCategory.instHasZeroObject`,
  and exact functor facts; no match.
- rg over the slopmaster2 WeilConjectures tree: node id and
  `localizing|Localizing`; no node-tag or localizing-closure theorem match. The prescribed
  node-id grep is also covered by this literal-id search. Searches of the chosen theorem
  name and node id in upstream names found no duplicate.
- rg over `lean/Sheaf`: `localizingClosureProEtale|ConstantModelConstructibleFiniteTor`
  finds the two definition modules and `ProEtaleProperOpenInterchange`, which only asserts
  invertibility of its interchange arrow on the closure. That theorem's full signature
  and docstring were read; it does not state this node. Further coefficient searches found
  `UniqueAdjointCoefficients` and `TrfDevissageGeneration`, which use different coefficient
  category packages. No duplicate definition or theorem is introduced.

Validation: scompile.py compiled this file cleanly as both sandbox and library module,
3.3 s and 3.5 s respectively, with no warnings. The preliminary diagnostic file and
pp.universes option were replaced; the final module has no #check or debug options.
All lines are at most 100 characters. The only postponed proof is this node's theorem.

## Second reading by N3

Author self-check, not an independent review: reread the node and final module together.
The characteristic, scheme finiteness and separation, k-morphism, Y qcqs, compactification
and admissible coefficient clauses are all present as detailed above. Restriction,
triangle preservation, coproduct preservation, and both components of Dctf preservation
are four separate conjuncts about the exact recorded ambient functor. No density, chosen
factorization, bounded-below restriction, derived-completeness condition, or ambient
coproduct-preservation conclusion has slipped into the statement. The full-subcategory
criterion is used directly rather than supplying unproved alternate category instances.
The canonical shift import was the only compilation repair. There are no new or dependency
nodes and no statement corrections. The maintainer's independent review remains outstanding.
