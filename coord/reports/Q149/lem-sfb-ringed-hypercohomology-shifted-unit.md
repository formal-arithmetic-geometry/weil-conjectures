## Worker report

The module `Sheaf.Algebra.Homology.RingedHypercohomologyShiftedUnit` states
`CategoryTheory.RingedHypercohomologyShiftedUnit.shiftedUnitRepresentation`. Its only theorem
has proof `sorry`; its ten helpers are actual expressions in the recorded constructions.
No dependency is replaced and no node statement is corrected. The already landed
`def-sfb-ringed-site-scalar-global-sections` is added to `stmt_deps` under the landed-node
rule, since it gives exactly the scalar-valued global sections used by this statement.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-section-RHom-over-U` (08JA), lines 8873 onward, including the global assertion and
K-flat/K-injective proof; `lemma-sheafification-cohomology` (0BKV), lines 4348 onward,
including the explicit cocycle quotient. The item is an agent-stated combination of these
assertions, not a blueprint unit's own statement.

The hypotheses and clauses correspond as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Ringed site small in the coefficient universe | `C : Type u`, `[SmallCategory C]`, `J : GrothendieckTopology C`; both objects and arrows fit `u` |
| Sheaf of commutative rings | `R : Sheaf J CommRingCat.{u}` |
| Sheaves of modules and their unbounded derived category | recorded `Modules R`, transparently `ringedSiteModules`/`SheafOfModules`, and `[HasDerivedCategory.{w} (Modules R)]` |
| Cohomology sheaves | `DerivedCategory.homologyFunctor (Modules R) n` |
| Commutative scalar ring and its specified global action | `A : Type u`, `[CommRing A]`, `s : A →+* Scalars R`; `Scalars` is the ring of compatible families |
| The point morphism determined by that action | `sections R A s` is its induced module direct image, pointwise with exactly that action; the theorem produces its module left adjoint `P`, not an arbitrary supplied morphism or arbitrary functor |
| Derived global sections computed by K-injectives | recorded `derivedSections R A s`, the canonical `rightDerivedFunctor` of those sections |
| Canonical derived adjunction | existential `L`, left-derived comparison `ε`, its `IsLeftDerivedFunctor` property, and `d : L ⊣ derivedSections R A s`; the chain-map equality fixes its normalization with `rightDerivedFunctorUnitQ` |
| Integers and literal single complexes | `n : ℤ`, `scalarComplex A n` and `unitComplex R n`, using `HomologicalComplex.single` |
| Canonical unit and shift comparisons | ordinary `unit` is pinned by adjunction evaluated at one on every module and every site object; `unitL n` is pinned to `ε` followed by `singleMapHomologicalComplex` and the single image of `unit.hom` |
| Additive bijection for every K | `γ n K : (hyper R A s n).obj K ≃+ (Q.obj (unitComplex R n) ⟶ K)` |
| Inverse of the canonical adjunction/evaluation composite | `evaluate A n _ (d.homEquiv _ _ ((unitL n).hom ≫ γ n K x)) = x`; `evaluate` applies cohomology to the morphism and evaluates on the canonical `scalarOne`; its bijectivity is asserted for every object of D(A) |
| Natural for every derived morphism | the `γ n K' (HⁿG(h) x) = γ n K x ≫ h` clause, for arbitrary `h : K ⟶ K'` |
| Formula on any K-injective representative | quantification over every `I`, `I.IsKInjective`, and `i : Q.obj I ≅ K`; `cocycleClass` uses the canonical derived computation unit and homology comparison |
| Cochain map sending a to az | existential cochain map `f : unitComplex R n ⟶ I`, with `component` transporting its degree-n component through `singleObjXSelf`; its section at every `U` sends every `a` to `a • z_U` |
| Its derived class equals gamma of the cocycle class | `γ ... (cocycleClass ... z) = Q.map f ≫ i.hom` |
| Additive edge map to global sections of the cohomology sheaf | `edge n K : HⁿG(K) →+ (sections R A s).obj (HⁿK)`; this existing module contains precisely the compatible global families |
| Evaluation of the cohomology of gamma at one | the `edge = scalarSection ... (SheafOfModules.unitHomEquiv ... )` equality; `unitHomologyIso` is the canonical Hⁿ(O_n) ≅ O, and `unitHomEquiv` evaluates on the compatible unit sections |
| Naturality of edge for every derived morphism | `sections.map (Hⁿ(h)) (edge n K x) = edge n K' (HⁿG(h) x)` |
| Edge is the sheaf cocycle quotient, independent of representative | for every K-injective `I`, `i` and global cycle `z`, a compatible section `y` of `I.cycles n` has the same degree-n sections, and the edge is its image through `I.homologyπ n` and the canonical comparison to HⁿK |
| No final object, boundedness, flatness or enough projectives | none is a binder or hypothesis; all complexes are ℤ-indexed and all rings, including zero rings, are allowed |

The point's set-topos presentation is suppressed in favor of its uniquely corresponding
module adjunction. This does not assume a final object of C: the scalar sections construction
uses compatible families over all objects. The ordinary unit evaluation identity and the
chain-map derived-adjunction identity exclude a twisted adjunction or a bare arbitrary
isomorphism of units. Existence of P, L and these identities is a conclusion, not a new
hypothesis. On the single scalar complexes the displayed unitL formula is precisely the
canonical single/shift normalization, since the ordinary pullback of A is O.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`; the recorded
  `Modules` abbreviation of `Sheaf.Algebra.Homology.RingedSiteScalarGlobalSections` unfolds to
  this exact category. That module also supplies `Scalars`, `sections`, `derivedSections`
  and `modulesGrothendieck`, preserving the external A-action.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`; its source construction is
  H⁰ after the K-injective right derived functor of Hom(O,-). The scalar sections lift used
  here is the already landed all-degree A-valued version of these same global sections.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`; `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `homologyFunctor` and `homologyFunctorFactors` (in namespace `DerivedCategory`).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `CategoryTheory.Precoverage.IsSiteForCoverings`,
  read as the recorded presented-site convention; the statement uses the resulting
  `GrothendieckTopology`, so no extra covering or pullback hypothesis is imposed.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`, read in
  full, including its structural map and induced module action. Here its specialization
  to the point is expressed directly by the already recorded scalar sections functor.
- `Sheaf.Paper.ProjectionMateExact`: `SheafOfModules.ringedProjectionMateExact`, including
  its `RingedTensorCorner` helpers, derived adjunction, canonical integer shifts and unit.
  It is publicly imported as a statement dependency; its module is not copied or repaired.
- Proof imports include `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`,
  `Sheaf.SixFunctors.ResolvingDerivedAdjunction`,
  `Sheaf.CategoryTheory.RingedToposKFlatPullback`,
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, and Mathlib's derived-category
  KInjective and KProjective localization modules. Their recorded maps and hypotheses
  were read; the proof docstring gives the node's six steps and their dependency ids.

Edge cases checked mathematically before writing: n=0 and negative n (single in degree n,
not shift by n); empty site (compatible families form the terminal/zero section module);
zero coefficient ring or zero ring sheaf; zero K; a site with no final object; unbounded I;
nonflat A→Γ(O). No nontriviality, final-object, boundedness or flatness restriction occurs.
A separate derived morphism is universally quantified, so naturality includes derived maps
that have no chosen initial cochain representative. Every K-injective representative and
its isomorphism to K is quantified, which gives the claimed resolution independence.
The chosen localization universe w is explicit and shared; no equation between independent
site universes is introduced because this node explicitly assumes the site is small in the
coefficient universe.

Searches actually run through `msearch.py Q149 lem-sfb-ringed-hypercohomology-shifted-unit`:

- LeanFinder: `hypercohomology of ringed site as derived morphisms from shifted structure
  sheaf unit with cohomology edge evaluation`; eight hits, including `Sheaf.H`, its
  presheaves and `HomComplex.CohomologyClass.toSmallShiftedHom_mk`. These do not state
  the unbounded ringed-module assertion, canonical adjunction and edge formula together.
- Loogle: `DerivedCategory, SheafOfModules`; zero hits.
- Mathlib grep: `hypercohomology|shiftedUnit|[Uu]nit.*homology` in
  `Algebra/Category/ModuleCat/Sheaf`; zero hits.
- LeanSearch: `Ringed site hypercohomology in integer degree n is naturally additively
  equivalent to derived maps from the structure sheaf concentrated in degree n with
  canonical adjunction and edge evaluation at one`; eight hits, including `Sheaf.H`,
  `HomComplex.Cochain.fromSingleEquiv`, `CohomologyClass.homAddEquiv` and
  `InjectiveResolution.extAddEquivCohomologyClass`. These supply pieces, not this statement.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for hypercohomology, shifted units,
  unit/cohomology patterns, the item id, and the proposed namespace/declaration. The
  existing `AlgebraicGeometry.derivedStructureSheaf_hom_hypercohomology` was opened:
  it concerns n=0 on schemes, with no all-degree edge or canonical adjunction normalization.
  The existing scalar sections definition was found, opened, and reused. No exact match.

Validation: scompile.py compiled both the sandbox probe and the final named module cleanly
(8.4 s and 7.0 s), under the prescribed 60-second per-file limit. The only compile repairs
were using the existing scalar sections module as the additive edge target and binding
its compatibility arguments explicitly. No theorem proof was filled in.

## Second reading by Q149

Author's separate source/signature pass, not an independent reviewer: the dispatcher brief
forbids starting other agents; the maintainer performs the independent reading of delivery.
I reread the node's full statement and all six proof steps against the finished signature.
The global coefficient map is retained rather than forgotten to abelian groups. The point
morphism is expressed through its actual module direct image; the left adjoint and its
normalization are conclusions. UnitL is not merely existential: its map is fixed by ε
and the ordinary unit. Evaluation uses the homology class of one via the canonical single
homology isomorphism. The inverse identity, bijectivity of evaluation and additive gamma
supply exactly the displayed inverse composite. The gamma formula includes every scalar a,
every U and every K-injective representative. Both the cohomology evaluation and the actual
sheaf cycles quotient formula are present for edge, with derived naturality.

This pass caught that a bare `SheafOfModules.sections` has no additive-group instance in
Mathlib. The target now uses the already recorded scalar sections module, whose elements
are the identical compatible families; `scalarSection` is only the explicit conversion.
No mathematical hypothesis or clause changed. All helpers have source/blueprint docstrings,
no data contains sorry, autoImplicit is disabled, and every line is at most 100 characters.
No STATEMENT-DISPUTED or statement correction is needed.
