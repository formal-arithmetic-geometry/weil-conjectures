## Worker report

The module `Sheaf.AlgebraicGeometry.OpenGeneralFieldUniformBound` states
`AlgebraicGeometry.Etale.openImmersion_generalField_uniformBound`. Its only theorem
has proof `by sorry`. There are no new definitions, helper theorems, or dependency
repairs. The module and declaration docstrings identify the blueprint source and
reproduce all seven proof steps with their DAG dependencies.

Source read: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`, lines 109–118,
“(1') at the finite stage”, including the general-field use of
`thm-sc-finite-type-torsion-cd`. The node expands this paragraph into the affine-test
argument, module/abelian comparison, and empty-open case. Those clauses are all
included; the existing algebraically closed-field theorem is not an exact match.

Hypotheses, individually:

- The field is `(k : Type u) [Field k]`.
- The nonnegative integer is `(c : ℕ)`; `hc` is the recorded
  `Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c`.
  Its definition quantifies over locally torsion abelian sheaves, with no common
  annihilator and no replacement by prime-to-characteristic torsion.
- The prime and its invertibility are `(ℓ : ℕ) (hℓ : ℓ.Prime)` and
  `(hℓk : IsUnit (ℓ : k))`.
- The schemes are `{U X : Scheme.{u}}`; their open immersion is
  `(j : U ⟶ X) [IsOpenImmersion j]`.
- The structure morphism is `(aX : X ⟶ Spec (.of k))`.
  `[LocallyOfFiniteType aX] [QuasiCompact aX]` is precisely finite type,
  and `[IsSeparated aX]` is separatedness over k. The induced structure map on U
  is j followed by aX; no unrelated structure map or extra finite-type hypothesis
  on U is assumed.
- The finite commutative coefficient ring is
  `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  `hA : ∃ r : ℕ, (ℓ : A) ^ r = 0` is annihilation by a power of ℓ.
  Annihilating 1 is equivalent to annihilating the ring. The exponent is existential
  and never appears in the bound.

Clauses, individually:

- In every displayed bound, `((topologicalKrullDim U).unbotD 0).toNat` is d.
  A nonempty open in a finite-type k-scheme is finite type and has finite natural
  dimension, so this is exactly its topological Krull dimension. Empty U has
  dimension bottom; `unbotD 0` assigns d = 0. No finite-dimension hypothesis is added.
- The first conjunct quantifies over every
  `M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)` and `q : ℤ`, with the strict
  inequality `2*d+c < q`, and concludes `IsZero (higherDirectImage A j q M)`.
  The existing `higherDirectImage` is degree-q cohomology of the ordinary
  bounded-below derived module direct image applied to M[0].
- A is arbitrary in the theorem, and the displayed bound mentions only U and c;
  it therefore works simultaneously for every such A and all indicated A_{E,n}.
  The last phrase is an instance of universal quantification, not an additional
  coefficient construction or a new hypothesis.
- The second conjunct quantifies over every `V : X.Etale` with `[IsAffine V.left]`.
  W is the actual scheme `pullback V.hom j`, not an arbitrary comparison object.
  `LocallyOfFiniteType (pullback.fst V.hom j ≫ V.hom ≫ aX)` and `QuasiCompact` of
  the same morphism assert finite type of W over k.
  `topologicalKrullDim (pullback V.hom j : Scheme.{u}) ≤ (d : WithBot ℕ∞)` is its
  dimension bound, retaining bottom for empty W.
- On W, F ranges over sheaves of modules over `ULift.{u + 1} ℤ` and satisfies the
  existing `Scheme.IsPrimaryTorsionSheaf ... F ℓ`. These are precisely primary
  abelian sheaves: the lifted-integer module action is uniquely the integer action.
  This does not require bounded exponent, constructibility, finite sections, or
  finite stalks. The result uses `cohomology AddCommGrpCat W q` on the degree-zero
  complex of `(moduleAbelianForget ... W).obj F`, asserting that its ordinary
  abelian étale cohomology is zero for every integer q > 2d+c.
- The third conjunct, for every M and every integer q, states a nonempty isomorphism
  from `(moduleAbelianForget A X).obj (higherDirectImage A j q M)` to the degree-q
  cohomology of `(lowerStar AddCommGrpCat j).rightDerivedFunctorPlus` on the
  forgotten M[0]. This is the corresponding ordinary abelian higher direct image.
  It asserts agreement after forgetting the action, without assuming forgetting
  preserves injective objects. The proof plan uses the recorded canonical derived
  comparison and the exactness of forgetting coefficients.
- The last conjunct is conditional on `IsEmpty U`. Its four subclauses quantify over
  every integer degree, with no strict lower bound: module higher direct images;
  abelian cohomology on U; abelian cohomology on every affine-test pullback W; and
  abelian higher direct images. The empty clause allows all abelian sheaves,
  consistently with the node's proof that the empty-site sheaf categories are zero.
- There is no algebraic or separable closedness assumption on k.

Statement dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `def-weil-scheme-morphism-properties` is a convention node, explicitly defining no
  new notion. Its named component nodes give Mathlib's `LocallyOfFiniteType`,
  `QuasiCompact` (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`),
  `IsSeparated` (`Mathlib.AlgebraicGeometry.Morphisms.Separated`), and
  `IsOpenImmersion` (`Mathlib.AlgebraicGeometry.OpenImmersion`). Their full definitions
  were read, together with the component nodes' recorded matches.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, the supremum of the chain
  lengths of irreducible closed subsets, valued in `WithBot ℕ∞`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its public coefficient
  imports: `DerivedCategory`, `.singleFunctor`, `.Plus.singleFunctor`,
  `.Plus.homologyFunctor`, and the ModuleCat-valued étale derived category.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`.
  The live derived API uses its generic `.rightDerivedFunctorPlus`, as documented
  in `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`; the old specialized
  derived-lower-star abbreviation in the historical record has been retired.
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` defines
  `Etale.higherDirectImage` by exactly this formula.
- `WeilConjectures.AlgebraicGeometry.Curve.Assertions`:
  `Scheme.IsPrimaryTorsionSheaf`, the existing stalkwise power-annihilation predicate.
  Its existing node `def-weil-pbc-primary-torsion` is added to stmt_deps under the
  standing rule permitting already recorded existing notions. No node is created.
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison`:
  `Etale.moduleAbelianForget`; its public derived comparison module also supplies
  the proof dependency `isIso_moduleAbelianDerivedLowerStarComparison`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: `Etale.cohomology`, ordinary
  derived sections followed by degree-q cohomology.
- The proof imports include the recorded finite-type torsion dimension theorem,
  higher-direct-image sheafification theorem, local sheafification representatives,
  dimension of schemes, étale local dimension, affine étale cover-density,
  noetherianity, étale base change, and finite presentation modules.

Searches actually performed:

- msearch leanfinder: `Open immersion etale higher direct image torsion cohomology
  vanishes above twice dimension plus cohomological dimension field`.
  Eight hits on étale/formally étale algebra and morphism properties; no match.
- msearch loogle: `AlgebraicGeometry.Etale.lowerStar,
  CategoryTheory.Functor.rightDerived`. Zero hits; upstream identifier
  `AlgebraicGeometry.Etale.lowerStar` is unknown to the Mathlib search index.
- msearch grep: `etale.*vanish|[Cc]ohomologicalDimension`.
  One unrelated étale-algebra cotangent-cohomology hit in RingTheory/Etale/Basic.
- msearch leansearch: `higher direct image etale open immersion vanishing
  cohomological dimension`. Eight hits on open-immersion definitions/properties;
  no bound or matching theorem.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the item ID, general-field/uniform-bound names, direct-image vanishing and
  higherDirectImage definitions. No existing declaration of the item was found.
  The closed-field sibling `etale_direct_image_vanishing_above_twice_dimension`
  requires an algebraically closed field and omits the general-field affine and
  comparison clauses. `EtaleModuleAffineBound` assumes finite or algebraically
  closed k and has bound 2d_X+1, not the present statement.
- rg for primary-torsion definitions located the existing `Scheme.IsPrimaryTorsionSheaf`
  in Curve/Assertions.lean; the DAG node and its complete signature were then read.
- rg for the chosen module/declaration names found no collision in the project or
  upstream declaration index. No search results were invented or treated as proofs.

Edge cases checked against the types and mathematics: empty U (d=0, every integer
q included in the final clause); empty W with nonempty U (dimension bottom ≤ d);
d=0; c=0; q=2d+c excluded by the strict inequality; negative degrees included in the
comparison and empty clauses; the zero ring A; exponent r=0, possible only for the
zero ring; positive characteristic with ℓ invertible; arbitrary nonconstructible
module sheaves and primary sheaves of unbounded exponent. Finite type ensures
`toNat` is never applied to infinity on a nonempty U. Universe u is explicit, and
coefficient/sheaf values use the library's u+1 convention; `autoImplicit false` is
set in the file. There is no statement dispute or source correction.

Validation: the first scompile run found only that a bare pullback within
`topologicalKrullDim` was inferred in Type. Annotating it `: Scheme.{u}` repaired
this elaboration ambiguity. The second run compiled both sandbox and library module
cleanly (12.0 s and 10.5 s). Additional explicit imports for the recorded direct-image
and Mathlib proof modules were then added before the delivery dry run.

## Second reading by Q124

I reread the node and final signature clause by clause after writing it. This is a
second pass by the dispatched worker; no separate agent was started, in accordance
with the dispatch brief. The maintainer supplies the independent delivery review.

The signature retains k, the exact torsion cd bound c, the prime and invertibility,
separated finite type of X, arbitrary open j, arbitrary finite commutative A killed
by an ℓ-power, arbitrary M, integer degrees, and the strict bound. The remaining
conjuncts explicitly retain the affine-test finite-type and dimension claims,
primary cohomology vanishing, the forgotten higher-direct-image isomorphism, and
all-degree empty-open vanishing. There is no closed-field restriction or extra
constructibility/flatness/bounded-exponent condition on sheaves. I checked the
existing primary predicate's signature: its surrounding file discusses curves,
but the definition itself is for arbitrary schemes and contains no curve, base-field,
or constructibility hypothesis. Lifted-integer modules represent all abelian groups,
so using that predicate excludes no primary abelian coefficient sheaf.

The only mismatch found during elaboration was Lean's inference of the pullback's
category in the dimension expression; it was fixed by the explicit scheme annotation.
I also checked the full signatures of `higherDirectImage` and `cohomology` rather
than relying on their names, and retained the full empty-open conclusion instead
of only its positive-degree consequence. The recorded Lean signature is extracted
verbatim from the final theorem, and the original node's statement and proof are
unchanged. The only dependency-list addition names the existing primary predicate.
