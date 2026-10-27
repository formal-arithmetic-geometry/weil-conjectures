## Worker report

`Sheaf.WeilSheaf.NativeDerivedHomComparison` states the native resolution-independent
Hom transposition in `AlgebraicGeometry.ProEtaleWeilSheaf.derivedHomComparison`.
The public real-data Prop definition `CategoryTheory.Adjunction.IsResolutionHomComparison`
packages its six groups of equations. It is a helper for this very statement, not
an independent new notion requiring a new definition node. There is one theorem,
with proof `sorry`, and no postponed data. No dependency record or node statement
was changed.

The packaged formulation avoids kernel expansion of the actual native sheaf
adjunction. Directly constructing a function using its unit caused expensive
proof-irrelevance/type comparisons. The final formulation describes exactly the
same function using an equation after composition with the invertible resolution
map. This is an equivalent formula, without a new hypothesis or a weaker claim.
All quantities supplied to the public predicate are the actual native functors
and maps, not arbitrary input structures in the theorem.

Hypothesis and object matching:

| Node | Lean |
|---|---|
| finite field k₀ | `(k₀ : Type u) [Field k₀] [Finite k₀]` |
| prime ℓ, different from characteristic | `(l : ℕ) [Fact l.Prime] [hchar : Fact (ringChar k₀ ≠ l)]`, explicitly retained by `include hchar` |
| algebraic closure and Ω | framework constructions use `AlgebraicClosure k₀` and `PadicAlgCl l`, with their specified coefficient sheaves and topology; no new model is chosen |
| separated finite-type X₀,Y₀ | `X Y : Scheme.{u}`, their `Over` instances, and `hXs,hYs,hXt,hYt,hXq,hYq`; locally finite type plus quasi-compact is finite type |
| separated finite-type f₀ over k₀ | `f : X ⟶ Y`, `f.IsOver`, `hfs,hft,hfq` |
| all geometric assumptions retained | `include hXs hYs hXt hYt hXq hYq hfs hft hfq` |
| W_X,W_Y | exactly `ProEtaleWeilSheaf k₀ l X` and `ProEtaleWeilSheaf k₀ l Y`, the abelian fixed-pair categories of actual coefficient-module sheaves |
| small-site and larger coefficient universes | inherited unchanged from the recorded native categories; the public predicate permits independent category object and morphism universes |
| arbitrary complexes M,J | arbitrary objects of `HomotopyCategory ... (ComplexShape.up ℤ)`, each the homotopy quotient of an unbounded complex |
| F₀,G₀ | `upperStar k₀ l f`, `lowerStar k₀ l f`; their `mapHomotopyCategory` functors are Fh,Gh in the predicate |
| specified η,ε | `(upperStarLowerStarAdjunction k₀ l f).mapHomotopyCategory ...`, supplied as adjh, including its original unit and counit |
| Q_T | `DerivedCategory.Qh` supplied as QX,QY |
| f*,Rf_* | the actual `mapDerivedCategory` and `rightDerivedFunctor`, supplied as Fd,Rd |
| localization comparison | `mapDerivedCategoryFactorsh`, supplied as α; α_M identifies f*(QM) with Q(F₀M) |
| β_I | `rightDerivedFunctorUnit`, supplied as β |
| K-injective objects | KI is the predicate that an object equals the quotient of a `CochainComplex ... ℤ` with `IsKInjective` |
| resolution r | arbitrary homotopy arrow r with `HomotopyCategory.quasiIso ... r`, supplied as W r; for every chain resolution the quotient has this property, and every such homotopy arrow has a chain representative with that same property |

Clause matching and equivalence of the displayed formulas (Lean uses left-to-right
`≫` for composition):

1. The theorem supplies `adj : Fd ⊣ Rd` on the actual ambient derived categories.
   Its `adj.homEquiv T N` is the required bijection for every derived T,N, with
   no assumption on their cohomology. Precomposing by the isomorphism α_M gives
   a bijection from `Hom(QF₀M,QJ)` for each complex representative M,J.
2. The second conjunct of `IsResolutionHomComparison` identifies this bijection
   with the specified four-arrow composite for EVERY K-injective resolution r.
   Given h and the unique t with `QX.map t = h ≫ QX.map r`, it states
   `adj.homEquiv (α_M ≫ h) ≫ Rd.map(QX.map r)
     = QY.map(adjh.unit.app M ≫ Gh.map t) ≫ β_I`.
   Existence and uniqueness of t are exactly the already recorded Mathlib theorem
   `CochainComplex.IsKInjective.Qh_map_bijective` into I. Inverting Rd(Qr) on the
   right recovers the node's four arrows: Qr postcomposition, inverse localization
   on Hom, the SPECIFIED unit transpose, then β_I followed by Rd(Qr) inverse.
   The last two arrows are c_r inverse because the dependency fixes
   `c_r = Rd(Qr) ≫ inv β_I`. This asserts the entire composite is bijective,
   since it equals an actual `homEquiv` after an isomorphism of its source.
   There is no vacuity: every h has the required unique t by the Mathlib input.
3. The same formula holds for all r, while `adj.homEquiv (α_M ≫ -)` has no r in
   it. Thus every resolution composite is equal, including different target
   complexes I,I'. This is exactly resolution independence, not a choice of an
   unconstrained bijection for each resolution.
4. The third and fourth conjuncts explicitly give both equations of naturality
   for arbitrary ambient derived arrows a and b. No condition requires those
   arrows to be chain maps or to have degree zero before localization, so extension
   morphisms are included. Applying these equations to specified source and target
   isomorphisms gives independence of BOTH complex representatives, with the
   localization isomorphism α included explicitly. The identity/composition
   compatibilities are the same equations applied to identities/composites.
5. The first conjunct gives the unique homotopy class t representing every
   derived v between K-injectives, with
   `β_I ≫ Rd.map v = QY.map(Gh.map t) ≫ β_I'`.
   The dependency supplies `IsIso β_I`, so multiplying on the left by its inverse
   gives precisely the node's `Rd(v) = inv β_I ≫ QY(G₀t) ≫ β_I'`.
   The final implication `IsIso v → IsIso t` says that the lift of any specified
   isomorphism between representatives of one object is an isomorphism in the
   homotopy category, equivalently a homotopy equivalence. Naturality from clauses
   3 and 4 identifies their Hom transpositions.
6. The fifth conjunct is the unit/first identity-transpose normalization, written
   after multiplication by β_I:
   `adj.unit_QM ≫ Rd(α_M) ≫ Rd(Qs) = QY(η_M ≫ G₀s) ≫ β_I`.
   Multiplying on the right by β_I inverse yields
   `adj.unit_QM ≫ Rd(α_M) ≫ Rd(Qs) ≫ inv β_I = QY(η_M ≫ G₀s)`.
   Since `adj.unit` is `adj.homEquiv(id)` and `Rd(Qs) ≫ inv β_I = c_s`, this
   is exactly the stated normalization, with the explicit localization source
   identification Rd(α_M). It covers every resolution of F₀M.
7. The sixth conjunct is the counit/second identity-transpose normalization:
   `Fd(β_I) ≫ adj.counit_QI = α_(G₀I) ≫ QX(ε_I)`.
   `adj.counit` is the inverse transpose of the identity. The α factor simply
   identifies `Fd(QG₀I)` with `QF₀G₀I`, so this is precisely the node's equation.
8. The unit and counit are those of the same specified ambient adjunction adj,
   whose Hom equivalence was identified by clause 2. Its triangle identities
   are fields of `Adjunction`. No preservation of bounded constructibles is asserted.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework` records
  `WeilConjectures.WeilSheaf.LowerShriek` and its family of native declarations.
  The full definitions/signatures/docstrings of `ProEtaleWeilSheaf`, its Frobenius
  functor and `upperStar` were read in Category.lean; `lowerStar` and
  `WeilComplex.derivedLowerStar` in LowerStar.lean. This delivery uses the actual
  ambient categories and functors, not the restricted full subcategories.
- `lem-sf-native-weil-injective-adjunction-model`:
  `Sheaf.WeilSheaf.NativeInjectiveAdjunctionModel`,
  `AlgebraicGeometry.nativeWeilInjectiveAdjunctionModel` and
  `AlgebraicGeometry.nativeWeilDerivedDirectImageModel`. Their full signatures
  and proof docstrings supply the precise homotopy adjunction, K-injectivity,
  universal comparison β and c_r formula, and naturality on K-injective maps.
  The public import also exposes the actual native framework it imports.
- Its native adjunction is
  `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction`,
  `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`.
- Its homotopy adjunction is
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
  `CategoryTheory.Adjunction.mapHomotopyCategory`.
- Proof input `lem-weil-pbc-kinjective-hom-derived` has mathlib_match
  `CochainComplex.IsKInjective.Qh_map_bijective` in
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`; its full type was read.
  This is why the characterization in clause 2 determines the full composite.
- Proof input `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `Qh`,
  and the homotopy quotient/localization, with its existing size convention.
- `CategoryTheory.Functor.mapDerivedCategoryFactorsh` in Mathlib's
  ExactFunctor.lean, and `rightDerivedFunctor`, `rightDerivedFunctorUnit` in
  native RightDerivedFunctor/Defs.lean: their full signatures/directions were read.

Sources read: the current node and all seven proof steps; both statement dependency
nodes and their bindings; Stacks `derived.tex` at lemma-K-injective (070I) and
lemma-adjoint-preserve-K-injectives (08BJ); current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`,
Step 1, final Hom bijection. No statement correction or disputed fault was found.

Edge cases checked before writing: zero complexes, identity resolution of a
K-injective, different resolutions, identity/inverse derived arrows, identity f,
empty schemes, unbounded complexes and extension morphisms. None is excluded.
No independent equality of site object and morphism universes is assumed. KI uses
an existing K-injective representative, whose image covers exactly the K-injective
objects of the homotopy category; the Hom localization theorem and the model
ensure that the resolution and transpose characterizations are nonvacuous.

Searches made using the prescribed msearch wrapper (raw records in searches.jsonl):

- LeanFinder: `Resolution independent derived Hom transposition using a K-injective
  resolution, with naturality and normalized unit and counit`: 8 results, ordinary
  rightDerived_map_eq and injective-resolution formulas. No complete native statement.
- Loogle: `CategoryTheory.Adjunction.derived, CochainComplex.IsKInjective.Qh_map_bijective`:
  0 hits. Neither the exact native composite nor its normalizations is already stated.
- Mathlib grep: `derivedη_fac_app|derivedε_fac_app|Qh_map_bijective` in CategoryTheory:
  2 hits in Functor/Derived/Adjunction.lean; these are generic derived-adjunction
  normalization interfaces, not the requested resolution composite.
- LeanSearch: `Hom into a K-injective complex is computed by the homotopy category
  and localization is bijective`: 8 hits, led by Qh_map_bijective, which is used here.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and the upstream name index for
  the item id and the new declaration names: no existing match. Concept searches
  for derived Hom/comparison/homEquiv find the native underived adjunction,
  unrelated internal Hom and bounded constructions, not this full statement.

Validation: `scompile.py` compiles the final module cleanly in module mode:
sandbox 14.3 seconds and library-path check 16.7 seconds, within the prescribed
60-second per-file limit. No warning other than the expected theorem sorry occurs.

## Second reading by Q141

The assignment prohibits starting other agents and assigns independent delivery
review to the maintainer. This is an additional in-thread rereading, not a claim
of independent authorship. I reopened the final node and file and checked all six
conjuncts against the node: the resolution equation cancels to exactly c_r inverse,
β has the correct direction, and the K-injective comparison conjugates by β_I
inverse on the source and β_I' on the target. The unit equation multiplies by β_I
on the right; the counit has the explicit α source identification. Both naturality
equations quantify over all derived arrows. The same adjunction for all resolutions
ensures resolution independence, and its naturality under specified isomorphisms
ensures independence of representatives. All named geometric and characteristic
assumptions are included in the theorem binders. The public predicate has no sorry
and only packages the exact equations; it introduces no alternate sheaf category,
functor, coefficient ring, map or arbitrary comparison. The final rendering uses
the Hom graph characterization to avoid expensive expansion of native categorical
structures, without changing any mathematical clause.
