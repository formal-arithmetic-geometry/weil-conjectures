## Worker report

This repairs returned immutable head 37a2252d1a51. The former etale alias and tautological
x=x theorem have been removed. All operations in the new statement act on
`DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ))`. Only the retained
witness L is on the etale site. The theorem has one postponed proof; every helper has
real construction data and no sorry.

Clause-by-clause correspondence:

* `k : Type u`, `[Field k]`, `l`, `[Fact l.Prime]` and `_hl : IsUnit (l : k)` render
  the arbitrary field and invertible prime. `E`, its field, Q_l-algebra and
  finite-dimensional instances render the finite coefficient extension. `n` and
  `hn : 1 ≤ n` retain the positive-level condition. The statement sets
  `Λ := Padic.coefficientExtensionRing l E n`, exactly O_E/varpi_E^n, and obtains
  its finite instance from `Padic.finite_coefficientExtensionRing`.
* The `Over (Spec (.of k))` instances, separated/locally-finite-type/quasi-compact
  structure maps, and `IsOver` instances render separated finite-type k-schemes
  and k-morphisms. The same three morphism-property instances on h and f render
  separated finite type. Neither h nor f is assumed proper.
* `d : Compactification f`, `e : Compactification (h ≫ d.i)` are exactly the
  supplied tower. Set i=d.i, q=d.g, a=e.i and p=e.g. The compactification equations
  give pa=ih. `H=e.restrict.Z`, `b=pullback.fst e.g d.i`, `r=e.restrict.g` and
  `j=e.restrict.i` are the actual pullback construction, not extra arbitrary
  scheme data. `e.isPullback_restrict` supplies pb=ir and Cartesianity;
  `e.restrict_i_fst` supplies bj=a; `e.restrict.comm` supplies rj=h.
* `towerP Λ t` and `towerJ Λ v` abbreviate the published ordinary pro-etale
  `lowerStar.rightDerivedFunctor` and exact `openImmersionLowerShriek.mapDerivedCategory`.
  `towerPull` is exact derived inverse image. These are the ordinary constant-Lambda
  module presentation used by the recorded `originComposition` declaration.
* `towerExchange` is explicitly the r unit, the canonical pullback-pasting square
  comparison, and the p counit. `towerPullPushAdjunction` only identifies exact
  pullback's total left-derived functor with its termwise derived functor.
  Thus Ex^p is specified independently of all compact-support composition maps.
* `towerOpenUnit` is the exact derived image of the actual open sheaf-adjunction
  unit. `towerLambda` is Ex^p at J_b N followed by P_r of its inverse, in exactly
  the node's order. `towerGamma` is the inverse lambda's preimage under the actual
  J_i/right-restriction Hom bijection. Its defining transpose is consequently
  i^*(gamma) eta_i = lambda^{-1}, equivalently the node's identity equation.
  Its `hLambda` argument is only a proof needed to take the inverse. The theorem
  *supplies* that proof existentially; invertibility is never an added assumption.
* The first conjunct quantifies over N, a bounded-below etale K on H and the
  specified isomorphism nu_H^*K ≅ N. It asserts lambda invertibility and gamma
  invertibility for every such witnessed input. The second conjunct binds
  `L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat Λ))`, sets
  `M=nu_U^*L` and `N=J_j M`, and gives the specified composition formula together
  with invertibility of gamma at this input. Thus arbitrary witnessed objects,
  including identity and changed witnesses, are covered.
* `towerOriginComposition` is the component of the published
  `AlgebraicGeometry.ProEtale.originCompositionAmbient`, the ambient realization
  of `originComposition` from thm-sf-comp-composition. The three
  `HasCompactification` instances establish existence only: this Prop-valued class
  cannot select a particular compactification. `towerCandidateComparison` transports
  the canonical etale common-refinement comparison through the named site comparisons,
  then descends it uniquely along the origin equivalence. `towerOriginComposition`
  conjugates the canonical alpha by these comparisons at the source, intermediate
  origin object, and target. Thus alpha is actually on the *supplied candidates*.
  This construction does
  not reference towerExchange, lambda, gamma, or the formula's RHS.
* The formula first applies `P_q.map gamma`, then
  `(finiteDirectImageComposition Λ e.g d.g).inv.app`, then P_(p≫q) of E. This is
  precisely `(D_{q,p} E_{b,j}) ∘ P_q(gamma)`. `towerOpenComposition` is obtained
  by uniqueness of the left adjoint to canonically composed open restriction;
  `towerOpenCongr ... e.restrict_i_fst` identifies that composite with J_a.
  No arbitrary isomorphism, mere Nonempty choice or renaming of the etale map
  occurs on either side.

Dependency declarations actually used include:
`Sheaf.Paper.CanonicalOriginCompactSupportComposition` / `originCompositionAmbient`,
`comparisonUpperStarPlusEtaleOrigin` from the upstream origin framework;
`Sheaf.Paper.FiniteDirectImageComposition` / `finiteDirectImageComposition`;
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` /
`Padic.finite_coefficientExtensionRing`; and the upstream Compactification,
restriction/composite, pro-etale direct/inverse image, open extension, their
adjunctions, exact-derived comparisons, and upperStarComp. All are imported
through these actual modules. The witness-retaining category's recorded
`EtaleOriginDerivedCategory` is imported by the composition module; the statement
uses its ordinary fixed-scalar full-origin presentation and explicitly retains
K and its comparison isomorphism, rather than imposing an arbitrary-lift assumption.

The theorem docstring now carries all eight proof steps: geometric hypotheses,
origin witnesses, normalized site transport, identification of exchange and unit,
uniqueness of the open transpose, the two final compositors, expansion of the
canonical alpha, and invertibility from the two proper/open specializations.

Edge cases checked: identities for h or f remain admissible, as do identity opens
and identity proper factors. Empty schemes and zero complexes are permitted.
A=0 is not excluded by the helper interfaces. The actual theorem retains n≥1
as in the node. No properness of h or f, algebraic closedness or perfectness of k,
finite maps, extra Noetherian assumptions, or equality of unrelated site universes
has been imposed. The source Construction paragraph was reread in the current
main-20261015 blueprint; its order is exactly open/proper interchange, open
composition and proper direct-image composition.

Searches: the saved packet's msearch LeanFinder, Loogle and Mathlib grep searches
found no exact statement. The repair additionally searched all project and upstream
pro-etale modules with rg for `originComposition`, `properOpenTransportExchange`,
`properOpenTransportProEtale`, `finiteDirectImageComposition`,
`openImmersionLowerShriekComp`, and derived open adjunctions. It found the canonical
origin compositor and finite direct-image compositor now used, and the Plus-level
exchange/unit construction in ProperOpenSiteTransport. That module's gamma wrapper
assumes finite horizontal maps, so it cannot supply this proper-tower interface.
The unbounded exchange is built by the same actual unit-square-counit construction;
the new gamma helper is a Hom-bijection construction and its invertibility remains
in the theorem. The repeated msearch requests and their results are in searches.jsonl.

## Second reading by Q38

I reread the node's statement, all eight proof steps and the repaired module with
particular attention to the maintainer's return. The previous module had the wrong
site, a renamed RHS as its LHS, no etale-origin object, no exchange/unit/adjunct
construction, no field hypotheses, and no invertibility conclusion. Each has been
replaced explicitly as matched above. The LHS is now originCompositionAmbient conjugated to the
three supplied candidates by the normalized common-refinement/site comparisons,
while the RHS uses a separately defined ambient exchange. In the self-check I caught
that HasCompactification is a Prop-valued existence interface, so passing a witness
cannot select the supplied model; the explicit three conjugation factors repair that
issue rather than asserting a false definitional identification.
Both types are pro-etale. The first conjunct additionally checks arbitrary witnessed
N; the second checks M=nu_U^*L and N=J_j M. The open-adjunction orientation was checked:
gamma maps J_i P_r N to P_p J_b N, its transpose is lambda inverse, and D is the
inverse of the recorded direct-image comparison. The final E maps J_b J_j to J_a,
not its inverse. The source equality and gamma-invertibility clauses are both present.
The two dependency modules change imports only, and retain every declaration and
body of their previously recorded canonical interfaces. No change to the natural-
language node statement was needed.

## Dependency modules

`thm-sf-comp-composition`: the published canonical origin-composition module mixed
retired `ProEtale.Derived` modules with the current finite-coefficient closure.
The initial compile rejected duplicate `derivedComparisonAdjunctionPlus`. Its
three derived root imports now name `ProEtale.FiniteCoefficient.Derived` directly;
all canonical composition and coherence definitions and statements are unchanged.

`lem-weil-derived-direct-image-composition`: its finite compositor now imports the
current `FiniteCoefficient.Derived.UpperLowerStar`, so it can be used with the
same canonical origin-composition framework. Its signature and entire construction
are unchanged. Both are existing statement dependencies; only lean records change.

## New nodes

None. P/J/Pull are abbreviations, and exchange, unit, lambda, gamma, E and the
canonical candidate comparison/evaluation are helpers belonging to the item's already stated notion.

Validation: scompile.py compiled all three delivered files separately in dependency
order, both as sandbox modules and under their real library module paths, against
the published server build. The final run was clean, with no errors or warnings
(the intended theorem proofs remain sorry). The tower module's real-path check
completed in 8.7 seconds. Only lean fields differ from the current node copies.
