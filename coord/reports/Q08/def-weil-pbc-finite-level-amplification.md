## Worker report

`Sheaf.AlgebraicGeometry.FiniteLevelAmplification` defines
`AlgebraicGeometry.ProEtale.HasFiniteLevelAmplification` and the two helper predicates
`finiteCoefficientCohomologyIn` and `finiteCoefficientPullbackAmplifies` belonging to the
item's interval convention and second clause. Definitions have real bodies. No theorem
is proved. All variables and universes are explicitly bound (`autoImplicit false`).

Hypothesis and clause correspondence:

- The four schemes and arrows are `{X' X Y' Y : Scheme.{u}}`, `g'`, `f'`, `f`, `g`.
  `_square : ChosenCartesianSquare g' f' f g` supplies the chosen fibre-product
  identification, projection equations and commutative square. The property depends on
  the arrows, as AMP does; its value does not depend on the particular identification.
- The arithmetic adic coefficient datum is written explicitly: `A : Type (u+1)`,
  `[CommRing A]`, `[IsNoetherianRing A]`, `I : Ideal A`, `hI : I.FG`, and
  `htorsion : IsAddTorsion (A ⧸ I)`. `hfinite` supplies finiteness of every positive
  quotient. `hperfect` applies the recorded `DerivedCategory.IsPerfectRingComplex` to
  each actual quotient as an A-module in degree zero, using the standard localization.
  This is exactly the coefficient-data paragraph of the adic node. No new adic
  structure is defined: the completed coefficient sheaf, strict reduction tower and
  its normalization maps are not used or replaced in this finite-level definition.
- `[IsNoetherian Y]`, `[IsNoetherian Y']`, `hDimY` and `hDimY'` state both target
  conventions inherited from FIN. The dimension bound uses `WithBot ℕ∞`, including
  dimension minus infinity for the empty scheme. No Noetherian or dimension hypotheses
  are imposed on X or X'.
- `hInvertY` and `hInvertY'` require the additive order of every element of every
  positive quotient to be a unit in every local ring of its respective FIN target.
- `c : ℕ` is the single fixed nonnegative integer, outside the level quantifier.
- `∀ n : ℕ+` means exactly all exponents n ≥ 1, with no off-by-one reindexing.
  `A ⧸ I ^ (n : ℕ)` is literally P_n. The two `letI` in the definition BODY equip
  this quotient with the discrete topology; no let binder appears in any signature.
- The first two conjuncts are the recorded `ConstructibleDirectImageFiniteness`
  applied to f and f', at the same n and c. That predicate uses H^q of ordinary
  K-injective derived direct image on F[0], requires constructibility for every
  constructible F and every integer q ≥ 0, and vanishing for every q > c. In
  particular c is independent of F, of the morphism and of n.
- The final two conjuncts are `finiteCoefficientPullbackAmplifies g P_n` and its g'
  counterpart. These refer to the actual coefficient module derived categories and
  exact termwise derived inverse images. `Functor.Additive` and `Functor.IsTriangulated`
  express additivity and preservation of distinguished triangles with the canonical
  `CommShift ℤ` structure attached to exact termwise descent. Preservation of the
  recorded object predicate `isBoundedConstructibleFiniteCoefficient` is precisely
  restriction to its strictly full subcategory: morphisms are all ambient morphisms,
  and shifts and distinguished triangles are induced from the ambient category.
  Ambient exactness is already available for this actual exact inverse image; it
  imposes no additional mathematical assumption beyond exactness of the restriction.
- The same helper quantifies over `a b : ℤ` with `a ≤ b` and every bounded
  constructible K. Its interval premise and conclusion use
  `finiteCoefficientCohomologyIn`, which is `∀ i : ℤ, (i < a ∨ b < i) → IsZero (H^i K)`.
  These are the same bounds before and after pullback. No interval enlargement,
  absolute-value bound, or assumption about arbitrary squares is asserted.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `AlgebraicGeometry.ChosenCartesianSquare`,
  including `isoPullback`, `hom_fst`, `hom_snd` and inherited `CommSq`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientRealization`, its additivity and exactness instances,
  `finiteCoefficientComparison`, `finiteCoefficientDerivedComparison`, and
  `isBoundedConstructibleFiniteCoefficient`. Their full signatures and docstrings
  were opened. This retains the existing sheafification of continuous functions on
  connected components and its strictly full essential image of bounded constructible
  etale complexes; it introduces no second constructible or coefficient category.
- `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness`:
  `IsConstructibleFiniteCoefficientSheaf`, `finiteCoefficientHigherDirectImage`,
  `ConstructibleDirectImageFiniteness` (the exact Q07 delivery, reused unchanged).
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `Scheme.IsConstructibleEtaleModuleSheaf`, its finite stratification and finite
  constant-module criterion, used by FIN through its original recorded comparison.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`. Its already landed node is added to the
  item's stmt_deps because the explicit coefficient signature uses this predicate.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` publicly retains the
  recorded arbitrary identified-coefficient operations and their adjunction.
  The delivered adapter retains these imports and Q07's canonical finite direct image.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`:
  `ProEtale.upperStar`, defined by Kan extension and sheafification along scheme
  base change, with its additivity, finite-limit and finite-colimit preservation.
- Mathlib `DerivedCategory.singleFunctor`, `homologyFunctor`, `IsZero`, `IsNoetherian`,
  `topologicalKrullDim`, ideal powers/quotients, and `IsAddTorsion`.
  For the Mathlib dependency `def-weil-triangulated-category`, opened the recorded
  `Pretriangulated`, `IsTriangulated`, and `Functor.IsTriangulated` signatures and
  docstrings. No redundant Lean record is added to that Mathlib leaf.

Edge cases checked before finalizing:

- The zero ring and the unit ideal are allowed; there is no Nontrivial assumption.
  The zero ideal is permitted whenever the explicit finite/perfect hypotheses hold.
- Empty schemes, the zero sheaf/complex, disconnected schemes, and empty finite
  constructible stratifications are not excluded. The original etale constructibility
  predicate allows zero strata. No Nonempty site, scheme or index of strata is added.
- n=1 is present. c=0 imposes vanishing in positive degrees. a=b imposes preservation
  of a single cohomological degree, including negative a. All integers i are checked
  outside the interval, with strict inequalities at its two endpoints.
- Small pro-etale site objects remain in universe u+1 and morphisms in u. Coefficients
  and module sections are in u+1; the standard derived localization uses its own larger
  universe. No equality of site object and morphism universes is imposed.
- FIN is a hypothesis on an arbitrary morphism, so properness, finite type and
  universal satisfaction of AMP are deliberately absent from the statement itself.

Searches (msearch logs are in searches.jsonl):

- LeanFinder: “Finite level amplification on a cartesian square uniform constructible
  direct image finiteness and interval preserving derived pullbacks at all quotient
  coefficient levels”: eight hits on finite inverse systems, Mittag-Leffler and scheme
  approximation; none defines AMP.
- Loogle: `CategoryTheory.Functor.IsTriangulated`: twelve hits giving the exact functor
  class and its APIs; none defines the simultaneous all-quotients AMP conjunction.
- Mathlib grep: `amplification|finiteLevelAmplification|FiniteLevelAmplification`:
  zero hits.
- LeanSearch: “Finite coefficient amplification for a Cartesian square with uniform
  constructible direct images and interval preserving derived inverse images”:
  unavailable (Internal Server Error); no mathematical verdict inferred.
- Direct rg over WeilConjectures and lean/Sheaf for the above amplification terms,
  the proposed declaration names and the item id: no matching predicate. Side hits
  concern Brauer matrix amplification and prose in an evaluation theorem. Search
  for the pullback adapter names gave no existing matching declarations.
- Read current server sources with `scompile.py --source`: no existing
  AdicCoefficientDatum or FiniteCoefficientFiniteness module at the attempted paths.
  Then enumerated server delivery branches read-only: found
  `deliver/Q07/def-weil-pbc-constructible-direct-image-finiteness`, read its node records,
  report and both modules, and reused that FIN and canonical direct-image implementation
  rather than retaining the earlier attempt's duplicate definitions.
- The blueprint sources for AMP, FIN and the adic datum were read in full on the server,
  since literature is not materialized in the shared read-only local clone.

No statement correction or disputed statement. No new independent definition node.

## Dependency modules

`def-weil-pbc-constructible-direct-image-finiteness`: the shared/current node had no Lean
record. Its already delivered Q07 module is supplied unchanged in this delivery under
the human's rule to supply unstated dependencies. It introduces no competing FIN:
its declarations retain Q07's exact names, arithmetic hypotheses and canonical higher
image functor. Only the dependency node's lean field is changed, with an explanatory
note; all natural statement fields remain as in the read-only repository.

`def-weil-pbc-proetale-operations`: the recorded module uses constant coefficients at
a different size or takes an inverse-image coefficient-ring isomorphism as input.
AMP needs actual operations at the finite coefficient ring sheaf of continuous
functions, with no arbitrary additional isomorphism hypothesis. The delivery preserves
all recorded public operations. Its direct-image portion is exactly the Q07 module:
coefficient maps are precomposition with the fibre-product first projection followed
by the ring-sheafification adjunction, and direct image is SheafOfModules.pushforward
followed by its ordinary K-injective right derived functor. The added pullback portion
uses the canonical realization equivalence and the recorded fixed-ring upperStar,
then exact termwise derived descent. This equivalence is fixed by the scalar map;
its inverse is determined up to its unique equivalence isomorphism, not selected from
an unconstrained Nonempty family of unrelated functors. The equivalence proof and
Q07's naturality, additivity and K-injective-resolution obligations remain named sorry
theorems belonging to this same owning definition node, each with source and full proof
docstring. No hollow data definition or theorem proof is added.

## Validation

All compilation attempts use the required scompile.py wrapper. The single-file
operations module compiled locally in both sandbox and library positions with no
warnings (8.2 s and 6.9 s). The first multiple-file attempt hit a local temporary-source
FileNotFoundError and then a server OSError 28 (No space left on device) in the
nt_compile.py link-farm creation. A diagnostic retry reproduced both failures.
A subsequent required-wrapper packet retry compiled every module separately in both
sandbox and library positions, with no errors or warnings: operations 5.2/6.1 s,
FIN 4.5/3.8 s, and AMP 3.8/4.1 s (plus the operations preliminary check, 4.8 s).
The temporary infrastructure failures resolved on retry. The prescribed dry run is
the final check; no push is authorized for this worker.

## Second reading by Q08

I reread the node statement, its blueprint source place, the six cited Stacks
places, every dependency node, and the declarations imported by the delivered
modules. The item statement renders as follows.

- The square is `X' X Y' Y : Scheme.{u}`, with arrows `g' : X' ⟶ X`,
  `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y`, together with
  `_square : ChosenCartesianSquare g' f' f g`. Its `isoPullback`, projection
  equations, and inherited commutative square are exactly the node's chosen
  Cartesian square `(f,f',g,g',α)`.
- The coefficient datum is `A : Type (u+1)` with `[CommRing A]`,
  `[IsNoetherianRing A]`, `I : Ideal A`, `hI : I.FG`,
  `htorsion : IsAddTorsion (A ⧸ I)`, the typeclass
  `[∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]`, and the explicit perfectness
  hypothesis on every quotient in degree zero via
  `DerivedCategory.IsPerfectRingComplex`. Thus `P_n` is literally
  `A ⧸ I ^ (n : ℕ)` and no completed coefficient sheaf is substituted.
- `[IsNoetherian Y]`, `[IsNoetherian Y']`, `hDimY`, and `hDimY'` render the
  two FIN target conventions. The dimension bounds use
  `WithBot ℕ∞`, so the empty scheme case is included. `hInvertY` and
  `hInvertY'` quantify over every positive level, quotient element, and target
  point and require the corresponding additive order to be a unit in the local
  ring. There are no hypotheses on `X` or `X'` beyond those in the arrows.
- `c : ℕ` is outside `∀ n : ℕ+`; hence the same nonnegative bound is used for
  every positive level and for both morphisms. The body installs the discrete
  topology on each quotient only in the level predicate, with no signature
  `let` binder.
- For each `n : ℕ+`, the first two conjuncts are
  `ConstructibleDirectImageFiniteness ... f c` and the corresponding `f'`
  predicate. The inspected FIN declaration has exactly the two node clauses:
  constructibility of every nonnegative higher direct image of every
  constructible finite-coefficient sheaf, and vanishing above the fixed `c`.
- The final two conjuncts are `finiteCoefficientPullbackAmplifies g P_n` and
  its `g'` counterpart. That helper states additivity, `Functor.IsTriangulated`,
  preservation of the strictly full object predicate
  `isBoundedConstructibleFiniteCoefficient`, and preservation of every interval
  `[a,b]` for `a ≤ b`. Its cohomology predicate is
  `∀ i : ℤ, (i < a ∨ b < i) → IsZero (H^i K)`, exactly the node's final
  interval convention. The derived pullback is the canonical finite-coefficient
  operation from the repaired operations dependency, with no arbitrary ring-map
  or coefficient-identification hypothesis.

No hypothesis or conclusion mismatch was found. In particular, the Lean does
not add properness, finite type, universal AMP, nonemptiness, a nontrivial ring,
or a characteristic assumption; it retains zero rings, unit or zero ideals,
empty schemes, zero complexes, disconnected schemes, empty stratifications,
`n = 1`, `c = 0`, `a = b`, negative interval endpoints, and all integers in
interval tests. The site and coefficient universes remain those of the
recorded declarations (`Scheme.{u}` and coefficient type `Type (u+1)`).

I checked the dependency records and declarations for
`ChosenCartesianSquare`, `ProEtaleFiniteModules`, the Q07
`ConstructibleDirectImageFiniteness`, the repaired finite-coefficient
operations, `DerivedCategory.IsPerfectRingComplex`, and the triangulated
functor classes. The Q07 FIN module and the finite-coefficient operations
module are required dependency modules in this delivery; their records explain
why the prior interfaces were unusable (missing the exact finite coefficient
ring-sheaf pullback/direct-image operations and the exact FIN interface) and
reuse the canonical constructions rather than private notions.

Searches were repeated with the required independent methods. LeanFinder and
Loogle searches for finite-level amplification, constructible derived
pullback/direct-image predicates, and `Functor.IsTriangulated` found no AMP
notion; the latter only supplied the class used by the helper. Grep over
Mathlib, `WeilConjectures`, and `lean/Sheaf` for amplification names, the item
id, and the helper names found no existing AMP declaration. The LeanSearch
query was unavailable with an internal-server error, recorded in
`searches.jsonl`; no conclusion was inferred from that failure. The Stacks
places were opened: 095U gives the finite cohomological bound, 0GL0 gives
constructibility context, 09C1 and 09C7 define the pro-etale constructible
setting, and 09AK/09AL give the etale/pro-etale pullback compatibility context;
none states this combined AMP predicate.

The only changes made in this second reading were delivery bookkeeping already
required by the missing dependency interfaces: retaining the exact Q07 FIN
module, retaining the canonical finite-coefficient operations adapter, and
recording `def-pc-perfect-ring-complex` in `stmt_deps` because the AMP signature
uses its explicit predicate. The item's statement and Lean signature required
no mathematical repair, and no statement correction or disputed-statement flag
was added. All three delivered modules compile cleanly through `scompile.py`
when supplied together.
