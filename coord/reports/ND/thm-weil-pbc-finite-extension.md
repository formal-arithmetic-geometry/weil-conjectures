## Worker report

The module `Sheaf.Paper.FiniteExtensionProperBaseChange` states
`AlgebraicGeometry.Scheme.finiteExtension_properBaseChange`, with `sorry` as its
only theorem proof. Its helper `finiteExtensionRationalExchangeComponent` has
real data: it is the canonical localization functor applied to the full-subcategory
morphism containing the recorded integral completed exchange. It does not select
an arbitrary map or isomorphism.

The source read is the complete blueprint file
`sec-proper-base-change/sk-thm-properbasechange/thm-weil-pbc-finite-extension.md`,
order 1357, together with the current node's more explicit statement and all three
proof steps. The current node makes the domain hypotheses of the integral corollary
explicit. The source and node assert the componentwise invertibility of the exchange.

Hypothesis and clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. A finite extension E/Q_l is
  `(E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- The coefficient ring, uniformizer and ideal are the actual recorded
  `Padic.coefficientExtensionIntegers l E`,
  `Padic.coefficientExtensionUniformizer l E`, and the principal ideal in
  `pbcPadicCoefficientDatum l E`. The datum supplies the noetherian, finite-quotient,
  perfect-quotient and torsion properties; none is an extra input assumption.
- The four schemes and four arrows are explicitly bound. The chosen Cartesian
  identification and commutativity are exactly
  `(sq : ChosenCartesianSquare g' f' f g)`.
- Each scheme has its own `IsNoetherian` instance and its own `_dimX`, `_dimY`,
  `_dimX'`, `_dimY'` finite topological Krull-dimension bound.
- Properness is `[IsProper f] [IsProper f']`. The four `_hlX`, `_hlY`, `_hlX'`,
  `_hlY'` assumptions say l is a unit in the global sections of each scheme,
  equivalently l is invertible on that scheme, as in the integral corollary.
- `(e : ℕ)` supplies e >= 0. `_hFibres` is exactly the corollary's geometric-fiber
  bound, quantifying over algebraically closed fields and their geometric points.
- The integral categories are the dependency's full subcategories
  `PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)`.
  The existential `hRf`, `hRf'`, `hLg`, `hLg'` give the membership witnesses needed
  to restrict precisely `d.push f`, `d.push f'`, `d.completedPull g`,
  `d.completedPull g'`. These conclusions encode that the four integral operations
  denoted in the node are defined; they are not additional preservation hypotheses.
- The rational categories are exactly the already published general construction
  `PbcRationalCategory T d (Padic.coefficientExtensionUniformizer l E)` from
  `Sheaf.Paper.PbcRationalCategory`. This is the raw scalar localization, with the
  same integral objects and localized tensor Hom modules, with no Karoubi envelope.
- The source and target of the helper are the localization of the integral source
  and target composites `constructibleCompleteSource f g d` and
  `constructibleCompleteTarget g' f' d`. Membership is supplied by the four
  restrictions above. On pure tensors the generic `ScalarLocalization.transport`
  sends a tensor to the integral map tensored with its scalar, so these are the
  endpoints of the composites of the rationally extended operations.
- The helper's body is `pbcRationalization.map (ObjectProperty.homMk
  (constructibleCompleteExchangeComponent sq d K.obj.obj))`. Thus the specified
  arrow is exactly Ex_comp tensored with one, not merely an isomorphism between
  the correct objects. This is the component prescribed in rational transport.
- `∀ K : PbcRationalCategory X d uniformizer, IsIso (...)` is every object and the
  precise conclusion in the rational category on Y'.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower`, its canonical
  construction and the `AdicCoefficientDatum` coefficient conventions.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including its chosen pullback iso and
  the two projection equations.
- `Sheaf.Paper.ConstructibleCompleteBaseChange`:
  `constructibleComplete_properBaseChange`, `constructibleCompleteSource`,
  `constructibleCompleteTarget`, `constructibleCompleteExchangeComponent`.
  Their full signatures, proof docstrings and actual-coefficient realization were read.
- `Sheaf.Paper.IntegralUniformCoefficient`, publicly imported by that corollary:
  `pbcPadicCoefficientDatum` and `IsPbcBoundedConstructibleComplete`.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`,
  `PbcRationalDerivedCategory`. The last is the smaller convenience specialization
  with E : Type u and a lifted valuation ring. The theorem instead uses the very
  same module's general definition with the integral corollary's actual coefficient
  ring E : Type (u+1), avoiding any new definition or imposed universe equality.
- `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport`,
  `transport_exact`, `transportNat`, and `WeilConjectures.pbcRationalExchange`.
  The generic transport theorem works on the full categories used here; no repair
  of the smaller finite-extension convenience specialization is needed.
- Proof imports retain the completed pullback, inverse-limit computation,
  finite-extension coefficients, scalar localization and K-injective Hom interfaces
  prescribed by all recorded proof dependencies.

Edge cases checked: e = 0 is included; there is no nonemptiness assumption on the
schemes or on their spaces of geometric points; finite dimension is a bound and
includes the empty scheme's bottom dimension. Every rational object is quantified,
including zero and objects killed by a uniformizer power. There is no characteristic
assumption beyond invertibility of l on all four schemes. Both proper maps remain
hypotheses exactly as in the node. The small-site object/morphism universes remain
u+1/u, with coefficients in u+1; no equality between these universes is added.
Global invertibility and stalkwise invertibility describe the same condition on l:
a globally invertible section has invertible germs, and conversely local inverses
glue uniquely to a global inverse. The existential membership proofs do not alter
the underlying objects, maps, or scalar actions of the full subcategory.

Searches actually run with msearch.py for ND and this item:

- LeanFinder: `Proper base change for constructible derived complexes over a finite
  extension of the l-adic numbers after inverting a uniformizer` returned eight
  hits on BDeRham, condensed modules, adic completions and valuations; no match.
- Loogle: `CategoryTheory.IsIso, CategoryTheory.ScalarLocalization` returned no
  hits (ScalarLocalization is project-specific and unknown to the service).
- Loogle: `CategoryTheory.IsIso, CategoryTheory.Functor.map` returned generic
  `Functor.map_isIso`, `map_inv` and inverse-composition facts, not this statement.
- Mathlib grep: `proper.*base.?change|base.?change.*proper` in AlgebraicGeometry
  returned scheme-morphism stability under base change and valuative-criterion
  facts, not constructible derived proper base change.
- LeanSearch: `Proper base change for rational l-adic constructible complexes`
  returned generic properness/base-change algebra facts, no match.
- `rg` in upstream WeilConjectures, the project Sheaf sources and the recorded
  upstream name table, by node id and by `pbcRationalExchange`, `finiteExtension`,
  `properBaseChange`, `rational.*proper`, `PbcRational`, and exchange/IsIso patterns:
  no existing statement of this node. A final exact-name search for both new
  declaration names in Mathlib, upstream, Sheaf and the upstream name table also
  returned no occurrence. The upstream condensed target uses a
  different coefficient category, as the current node explicitly distinguishes.

No new DAG nodes, dependency modules, statement correction or disputed statement.
Validation: the final file passed scompile.py with exit 0 and no warnings in both
the sandbox and library positions (3.4 s and 3.5 s). An earlier invocation encountered
a stale local PbcRationalTransport artifact and automatically requested server
confirmation; scompile --source confirmed the recorded current module exists, and
the next normal wrapper invocation succeeded after the local overlay caught up.
The prescribed deliver2.py --no-push printed OK (commit 27d112fb5e): compilation
and preflight passed except for the second-reading section, which the independent
second reader supplies. Nothing was pushed. The superseded first server-confirmation
invocation was stopped after the final successful local checks and this dry run.
No proof is supplied in this stage.

## Second reading by ND

I independently read the sandbox node and module, the shared base node, its complete
blueprint source at order 1357, and the signatures and definitions of all five
statement dependencies. I also read Stacks `proetale.tex` at Tags 099L/099N
(lines 4273--4396), 09C1 (line 5768), and 09C9 (line 6187). The blueprint's
short statement is read with the current node's explicit domain and the integral
corollary it invokes. Stacks 099L distinguishes constant from completed coefficients;
099N identifies completed pullback as ordinary pullback followed by completion;
09C9 uses a Noetherian coefficient ring, a torsion first quotient, complete inputs,
bounded-below etale-origin reductions and perfect quotients. The coefficient datum
and the integral constructible category supply these conditions here. There is no
additional field-of-definition or separated finite-type hypothesis on the schemes.

My object/hypothesis/conclusion inventory and its Lean correspondence follows.
Each verdict is PASS.

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. A finite field extension E/Q_l is
   `(E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`. This is finite-dimensionality, without any
   additional topology or arbitrary normed-field structure.
2. The actual integer ring A and chosen uniformizer: the repeated datum is
   `pbcPadicCoefficientDatum l E` and the element is
   `Padic.coefficientExtensionUniformizer l E`. I opened
   `CoefficientExtension.lean`: the absolute value is the spectral extension,
   the integer subring is the valuation-bounded subring supplied by the DVR
   characterization, and the chosen element generates its maximal ideal.
   `IntegralUniformCoefficient.lean` gives precisely `ideal := Ideal.span {...}`;
   its other fields are proofs of properties of these actual data. No new ring,
   ideal, or coefficient realization is substituted in this delivery.
3. The four schemes and maps: `{X' X Y' Y : Scheme.{u}}`,
   `{g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}`.
   `(sq : ChosenCartesianSquare g' f' f g)` is the recorded dependency,
   not merely commutativity. Its `isoPullback`, `hom_fst`, `hom_snd` and inherited
   `CommSq` give the chosen Cartesian identification with both projections.
4. Noetherian finite-dimensional corners: four separate `IsNoetherian` instances
   and the four `_dimX`, `_dimY`, `_dimX'`, `_dimY'` witnesses
   `∃ n : ℕ, topologicalKrullDim ... ≤ (n : WithBot ℕ∞)`.
   No common bound, nonempty corner, or finite-type presentation is imposed.
5. Proper vertical arrows: `[IsProper f] [IsProper f']`, exactly as the current
   node and its integral corollary state. Both are retained even though properness
   of f' follows from the Cartesian square and properness of f.
6. Invertible ell on each corner: the four `_hl... : IsUnit (l : Γ(..., ⊤))`.
   These match the integral corollary's convention. Stalkwise invertibility and
   invertibility of this constant global section are equivalent: local inverses
   exist near every point and glue uniquely. No characteristic-zero hypothesis
   or fixed positive characteristic is added to the schemes.
7. Fiber bound e >= 0: `(e : ℕ)` and `_hFibres`, quantifying over every
   `(Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)` and bounding
   `topologicalKrullDim (pullback f y)` by e. This is the identical test-field
   and fiber signature of `constructibleComplete_properBaseChange`.
8. The integral categories: `PbcBoundedConstructibleComplete T
   (pbcPadicCoefficientDatum l E)`. I read `BoundedConstructibleComplete.lean`:
   this is the full subcategory on the conjunction of intrinsic completeness,
   uniform constructible reductions and compatible etale origins. The membership
   abbreviation `IsPbcBoundedConstructibleComplete T l E` in
   `IntegralUniformCoefficient.lean` specializes exactly that same predicate.
9. The four integral operations denoted by the node are the recorded `.push f`,
   `.push f'`, `.completedPull g`, `.completedPull g'`. The conclusion's four
   existential witnesses `hRf`, `hRf'`, `hLg`, `hLg'` express that these ambient
   functors restrict to the specified full subcategories. They are conclusions,
   not additional preservation hypotheses. Their order precedes `∀ K`, so the
   restrictions work uniformly on every integral object. Fullness fixes their
   maps; the witnesses carry only proof data.
10. Raw rational categories: `PbcRationalCategory T (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)`. I opened the general definition
    in `PbcRationalCategory.lean` and the underlying `ScalarLocalization`: objects
    wrap the integral objects, and Hom is `Localization.Away p ⊗[A] Hom`.
    Tensor symmetry and the recorded uniformizer fraction equivalence identify
    this with the source's `Hom ⊗[A] E`. No idempotent completion or independent
    lattice is introduced. The smaller `PbcRationalDerivedCategory` convenience
    wrapper uses lifted coefficients; it is deliberately unnecessary because
    the same published module supplies this general raw construction.
11. Rational extensions and the specified exchange: the helper's endpoints are
    the localization of `constructibleCompleteSource f g d` and
    `constructibleCompleteTarget g' f' d`, with membership obtained by applying
    the individual restriction witnesses in their actual order. I read these
    abbreviations: they are `d.push f ⋙ d.completedPull g` and
    `d.completedPull g' ⋙ d.push f'`. `ScalarLocalization.transport` uses precisely
    these objects and extends morphisms by `LinearMap.baseChange`; extending a
    composite and composing the extensions have the same objects and pure-tensor
    maps. Thus these endpoints render the two rational composites in the node.
12. The arrow itself is fixed, not existential: the helper body is
    `pbcRationalization.map (ObjectProperty.homMk
    (constructibleCompleteExchangeComponent sq d K.obj.obj))`.
    I checked `constructibleCompleteExchangeComponent` is exactly
    `d.completedExchange sq K`, and opened `CompletedBaseChangeMap.lean` to
    verify it is the recorded ordered inverse-limit exchange. The localization
    functor sends it to `1 ⊗ exchange`. `transportNat` prescribes exactly that
    component. The full-subcategory wrappers change neither the underlying
    component nor its scalar action; its value retains the chosen square.
13. Every object and invertibility in the stated category: the final
    `∀ K : PbcRationalCategory X ...,
    IsIso (finiteExtensionRationalExchangeComponent l E sq K ...)`
    has precisely the arrow of item 12 and codomain in the raw category on Y'.
    It asserts invertibility of this component, not merely existence of an
    isomorphism between its endpoints. The implicit preservation conclusions
    needed to denote the operations have been made explicit without changing
    the mathematical scope of the assertion.

Edge cases: e = 0 is permitted. Empty schemes are permitted because their
Krull dimension is bottom and there is no `Nonempty` assumption. The zero ring
of global sections on an empty scheme causes no obstruction to the unit
condition. Empty collections of geometric points impose no artificial witness.
The quantifier over rational objects includes zero and all uniformizer-power
killed objects. There is no positive degree/reduction-level hypothesis in the
statement to exclude degree zero. Reduction towers in the dependencies index
positive powers by `n + 1`; there is no missing level-one quotient. Every prime,
including 2, is covered. The common scheme universe is arbitrary; the small site
retains its object/morphism universes u+1/u and coefficients lie in u+1, just as
in the integral corollary. No equality of these two site universes or independent,
potentially smaller test-field universe is imposed. Every binder is explicitly
bound with `autoImplicit false`; there are no hidden section-variable hypotheses.

Independent searches (run with msearch.py under this group/item):

- LeanFinder: `The proper base change morphism for constructible completed adic
  complexes becomes invertible in the scalar localization at a uniformizer`.
  Eight hits on algebraic adic completion and BDeRham; no derived sheaf statement.
- Loogle: `"baseChange", CategoryTheory.IsIso`. Six generic Guitart-exact Kan
  base-change results, with unrelated categories; no matching theorem.
- LeanSearch: `Rational l-adic proper pushforward commutes with completed pullback
  on bounded constructible complexes`. Eight ordinary sheaf pullback/pushforward
  and adjunction results; no matching theorem.
- `rg` in Mathlib AlgebraicGeometry, the slopmaster2 `WeilConjectures` tree and
  the shared `lean/Sheaf` tree for `rational.*[Bb]ase[Cc]hange`,
  `[Bb]ase[Cc]hange.*rational`, `[Ii]sIso.*[Ee]xchange`,
  `[Ee]xchange.*[Ii]sIso`, and both proposed declaration names. The nearby
  completed and finite-level integral results do not state rational proper base
  change. The abstract lower-shriek exchange class assumes its invertibility.
  I also opened the actual 51-module framework's
  `ModuleObject/BaseChangeTheorems/Proper.lean`, following
  `coord/pefw-upstream-framework.md`: its theorem concerns condensed continuous
  E-coefficients on separated finite-type schemes over a positive-characteristic
  field. It is not this raw rationalization theorem on the node's scheme domain.
  Neither the theorem nor its helper duplicates an existing declaration.

H4/H5/H6/H8/H9 checks: dependency constructions are reused, including the general
transport API despite its smaller specialized convenience interface. No new nodes
or dependency modules need review. The only new definition has its real map as
its body; the only theorem proof is `sorry`. The theorem docstring carries all
three proof steps, including identity-square preservation, scalar linearity on
K-flat/K-injective representatives, localization of composites and the inverse
identities. Both declarations and the module name the source and exact blueprint
id. There is no local notation/instance, private construction or line over 100
characters. The node's `lean.statement` was checked verbatim against the theorem
signature and is equal. The sandbox node differs from the base only by `lean`;
there is no stage-2 statement correction or citer audit to supply.

Mismatches found: none. I retained the Lean and node unchanged and added this
independent second-reading section. The prescribed scompile.py invocation from
the sandbox passed both sandbox and library positions in 2.5 s and 2.6 s,
respectively, exit 0 with no warnings. The first invocation used a relative path
from the shared root and found no file; rerunning from the sandbox corrected the
invocation without any source change.
