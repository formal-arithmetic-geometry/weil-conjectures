## Worker report

The module `Sheaf.Paper.TraceBoundedQuotientStalkRealization` states
`WeilConjectures.trfBoundedQuotientStalkRealization`, with `sorry` as its entire
proof. All other declarations are real wrappers or abbreviations for the constructions
or the clauses of this single node. No definition contains `sorry`; no theorem is proved.
The node's mathematical statement and its approved seven-step split are unchanged.
The previous attempt's stage-1 live-wins objection does not apply to this stage-2 statement.

Hypotheses and clauses, in the order of the node:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. Its `D.k` is the recorded
  algebraic closure of the finite field; `pointFibreBaseIsAlgClosed D` supplies the
  algebraic-closed-field instance. The prime and coefficient extension are
  `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. This uses the coefficient datum
  underlying `TraceFormulaCoefficientConventions`, without imposing its auxiliary
  finite-type scheme or fixed reduction level on the arbitrary scheme T.
- `Padic.coefficientExtensionIntegers l E` is R, with the published uniformizer and
  `Padic.coefficientExtensionRing l E (n + 1)` equal to A_(n+1). Natural indices
  begin at zero, hence exponent n+1 always begins at one. The common `ULift.{u+1}`
  permits coefficients in sheaves on the actual small pro-etale site; it is the
  same lift used by the point fibre and stalk interfaces.
- `(T : Scheme.{u}) [∀ x : T, Invertible (l : T.residueField x)]` gives the scheme
  and invertibility condition; `v : Spec (.of D.k) ⟶ T` is the geometric point.
  Finite pullbacks quantified over X carry the same invertibility condition.
  All module categories are modules over the published completed sheaf, never over
  the discrete constant integral sheaf. Site object and Hom universes remain u+1 and u.
- `M : DerivedCategory (integralTowerModules l E T)` with
  `sfIntegralConstructible l E T M` is exactly D^b_c(T,R), including derived
  completeness, constructible reductions, and their one common cohomological interval.
- `P : (integralOperationsGoodComplex l E T).FullSubcategory` supplies precisely
  K-flatness and flat terms, as in the recorded independent-coefficient resolution
  theorem. `q : DerivedCategory.Q.obj P.obj ≅ M` is its arbitrary representative
  identification. There is no bound on the terms of P and no Tor-amplitude predicate.
- `trfQuotientTower` packages the already constructed
  `unrestrictedIntegralComplexFunctor` and `unrestrictedIntegralTransition` as a
  functor in P. Thus its objects are actual quotients, restricted along the actual
  completion projections, and its maps are actual quotient transitions. It does
  not select separate derived reductions or unrelated comparison isomorphisms.
- The existential p,r in `TrfBoundedQuotientStalkRealized` gives a single p≤r with
  `CochainComplex.IsGE ... p` and `CochainComplex.IsLE ... r` at every positive
  reduction level. The next clause covers EVERY p≤r with these bounds.
- `trfUpperTower`, `trfBoundedTower`, `trfUpperArrow`, `trfLowerArrow` are direct
  applications/whiskerings of Mathlib's canonical truncation functors and their
  boundary natural transformations. Their transitions are the induced strict
  transitions. `TrfBoundedZigzag` states both arrows are levelwise quasi-isomorphisms
  and that every term outside [p,r] is zero. It also explicitly includes the p=r
  cohomology object. The upper boundary is the existing `truncLEXIsoCycles` kernel;
  the lower boundary is the existing `truncGEXIsoOpcycles` cokernel. Thus no stupid
  truncation or arbitrary bounded replacement has been substituted.
- Functoriality in arbitrary tower maps is built into these functors and the
  whiskered boundary natural transformations. `TrfTruncationCompatible`, asserted
  for every finite coefficient scheme pullback and every p,r, gives natural
  isomorphisms for both good truncations and their actual boundary-arrow equations.
  Whiskering by a tower proves compatibility of transitions and the entire zigzag.
  The upper comparison is fixed by its monic boundary, the lower by its epic boundary.
- `trfCompletedPointFibre` is `integralDerivedPullback l E v` followed by the
  recorded `pointFibreIntegralAmbient D l E`. It is the underlying ambient derived
  R-module object of Fib_s(Lv*M). Constructibility preservation places Lv*M in the
  recorded point-fibre subcategory; its inclusion has exactly this value.
- `trfQuotientStalkTower` applies `integralCoefficientModuleStalkFunctor l E v`
  to the actual quotient tower, term by term. Its scalars are restricted along the
  existing `integralConstantStalkGerm`, so all levels and all quotient maps lie over
  the SAME integral ring. Its underlying objects are precisely the finite stalks
  (P_n)_v; the finite-module action is forgotten only to the specified integral action.
- The natural isomorphisms γ_n and δ_n in `TrfQuotientGermNormalized` prescribe the
  finite coordinates. γ_n sends x to [s,id,x]; its inverse is [U,u,x]↦u*x, by the
  pointed-neighbourhood colimit relations. δ_n sends the pullback-unit section
  restricted along ANY pointed lift θ to [U,u,x]. This is exactly the germ rule of
  `proEtalePullbackStalkCoherence`, followed by identity-point sections. The use of
  the independent-coefficient pullback interface is normalized by its actual
  adjunction unit, so no identification with a different chosen left adjoint is assumed.
  Each δ_n is a natural isomorphism on ALL finite module sheaves, so it applies
  degreewise to unbounded complexes as well as their good truncations.
- `e : trfQuotientSectionTower ... ≅ trfQuotientStalkTower ...` is an isomorphism
  of functors into the strict tower category. Its components equal δ_n on every
  degree and section by the final normalization clause. Consequently it commutes
  with differentials, every quotient transition (including the first), and every
  chain map, before localization. The germ conditions fix its maps, rather than
  merely asserting that two towers happen to be isomorphic.
- `integralOperationsRoos` is the existing Cone(1-s)[-1]. Its mapping-cocone
  coordinates are (b,a), with differential (-db-(1-s)a, da).
  `trfQuotientStalkRealizationArrow` explicitly composes the defining completed
  pullback comparison, its image under exact point sections, the exact-section
  localization comparison, `scalarRoosMap` for those sections, and
  `integralOperationsRoosMap` of the normalized e. The first map on cones is
  characterized on both projections by `scalarRoosMap_existsUnique`; the second
  is the published diagonal product map. Thus both b and a use their sectionwise
  product identifications and there is no off-diagonal component or triangle filler.
- For EVERY M,P,q the theorem supplies an isomorphism ε in the derived category
  whose hom is exactly that arrow, and asserts that the section-cone comparison
  itself is an isomorphism. This is the specified e_(v,P) at the derived level,
  not just a list of isomorphisms of individual cohomology modules.
- Agreement with the displayed bounded zigzag uses the same finite δ_n on each
  term of its upper and bounded truncations, not new comparison choices. Their
  naturality on finite sheaves commutes with both boundary arrows; the pullback
  truncation comparisons above identify the section versions with these very
  finite pullbacks. The two explicit `QuasiIso (integralOperationsRoosMap ...)`
  clauses say the SAME stalk zigzag gives invertible derived comparison maps.
  Thus the fixed diagonal realization passes through both arrows of that zigzag.
- The final equality quantifies over arbitrary constructible M,M', representatives
  P,P', identifications q,q', chain maps w and derived maps h satisfying
  `[w] ≫ q'.hom = q.hom ≫ h`. It is the required naturality square using the
  actual diagonal Roos map. This applies to each leg of a comparison roof;
  invertibility for its quasi-isomorphism leg permits inversion of that square,
  and composition gives the statement for roofs. K-flat resolutions of intermediate
  roof objects exist by the recorded resolution theorem. The result is independent
  of the roof because its value is the already fixed derived functor applied to h.

Dependency interfaces read and reused:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`: the recorded conventions and
  their underlying `FiniteFieldDatum` and coefficient extension data.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its public
  `IntegralDerivedOperations`: `integralDerivedPullback`, its normalized representative
  comparison, `integralOperationsGoodComplex`, the strict finite pullback tower,
  `integralOperationsRoos` and its diagonal map.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`, the underlying
  derived functor of the full-subcategory `pointIntegralFibre`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor` and
  `Sheaf.Paper.CompletedIntegralCoefficientGerm`: `finiteCoefficientModuleStalkFunctor`,
  `geometricRingModuleStalkFunctor`, `integralCoefficientModuleStalkFunctor`,
  `integralConstantStalkGerm`, `pointIntegralSections`, `pointFiniteSections`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the field and Spec morphism
  encode the geometric point without duplicating it.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: canonical completed scalar
  actions and the same completed coefficient sheaf, via its public imports.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; its flat-term
  K-flat predicate is the one used by `integralOperationsGoodComplex`.
- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: publicly re-exports the
  actual good truncations of Mathlib used here. Its primary new declaration
  `IsSequentialHomotopyColimit` is not confused with good truncation.
- `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence`:
  `proEtalePullbackStalkCoherence`, the prescribed germ rule and stalk functors.
- Added the already landed `lem-pur-integral-operations-scalar-extension` to
  stmt_deps to use `Sheaf.Paper.IntegralOperationsScalarComparisons.scalarRoosMap`
  (namespace `WeilConjectures`), with its uniqueness theorem, rather than creating
  another product/cone comparison. Nothing else of the base node is changed.
- Every already-stated proof dependency is imported as a plain proof import. The
  proof-only node `lem-trf-point-pullback-representative-diagram` has no Lean record
  at this base, so there is no module to import. No object or construction from it
  is needed to type this statement: the source's specified representative comparison
  already exists in `integralDerivedPullbackComparison`. Its remaining proof is
  postponed in the sole theorem sorry, with all seven steps in the docstring.

Searches (2026-10-22):

- msearch leanfinder: "Completed geometric stalk realization as the Roos homotopy
  limit of a uniformly bounded quotient tower". Eight hits about smooth/topological
  stalks and module tilde germs; no completed quotient-stalk comparison.
- msearch loogle: `"truncLE"`. Twelve hits, including the generic good truncation
  construction. It is used via Mathlib, not defined again.
- msearch grep: `truncLE|truncGE|mappingCocone`, in `Algebra/Homology`. Twenty-five
  hits, including good truncations and mapping cocones; no node statement.
- msearch leansearch: "Exact additive functors commute with good truncation of
  cochain complexes". Eight hits including the generic truncation functors and
  exact/additive functor APIs. These supply constructions, not this comparison.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  this node id and the new declaration names found no existing realization.
  Concept searches located the existing canonical Roos comparison, actual strict
  quotient tower and integral stalk functor, all reused.
- Read the dependency modules' signatures and docstrings, and Stacks 0993,
  05V1, 0941 and 0118 in their local TeX sources. Read blueprint Euler-product
  proof Step 1, Local powers (b), in the current main-20261015 snapshot.

Edge cases: M=0 has zero reductions and zero stalks; no nonzero hypothesis is made.
For v=id the prescribed germ is the identity-neighbourhood section map. Index n=0
is exactly the first positive quotient, and its transition is included in the strict
natural transformation. For p=r the bounded term is explicitly H^p. T may be empty
(the theorem then ranges over its actual geometric points); no Nonempty or finite-type
condition is imposed on T. Arbitrarily negative bounds and unbounded K-flat terms
are permitted. There is no independent scheme/coefficient size restriction beyond
those already present in the recorded coefficient and constructibility categories.
The cone differential squares to zero since the transition is a chain map; both
normalized coordinate maps commute with 1-s and d.

No statement dispute, statement correction, new node or dependency repair was needed.
The only data-bearing choices used by the wrappers are previously published canonical
constructions or comparisons characterized uniquely by their prescribed formulas.

Compilation through scompile.py passed without warnings in sandbox and library module
modes (10.0 s and 9.8 s respectively). The two earlier interface errors were repaired
by fully qualifying cochain truncation predicates and maps and spelling out the
small-Hom coefficient-module localization used by the published point fibre.
No global build, live-source edit, direct Git command or subagent was used.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
