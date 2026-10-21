## Worker report

The module `Sheaf.Paper.ConstantDerivedLimitResolutionUnit` states
`AlgebraicGeometry.Scheme.constantDerivedLimitResolutionUnit`, with `sorry` as its
only proof. No definitions, new nodes, dependency repairs or statement corrections
are needed. The node copy changes only `lean`.

Hypotheses and clauses, checked against the node and the source:

- The scheme is `T : Scheme.{t}`. The commutative Noetherian adic datum, including
  its ideal, torsion, finite positive quotients and perfectness, is the recorded
  `d : AdicCoefficientDatum A`, for `A : Type (t + 1)` with `[CommRing A]`.
  `d.completedRing T` is the actual completed coefficient sheaf A_T. No condition
  on the scheme, such as nonemptiness, Noetherianity or dimension, is added.
- Mod(A_T) is `reductionModules T (d.completedRing T)`, transparently the recorded
  `ringedSiteModules` / `SheafOfModules`. The strict tower category is `d.towers T`.
  Its index `ℕᵒᵖ` is the existing indexing convention: Lean n is paper level n+1.
  Thus no positive level is lost, and the transition direction is unchanged.
- Delta is exactly `d.constantTower T`; its termwise complex functor is
  `(d.constantTower T).mapHomologicalComplex (.up ℤ)`. Delta_D is the existing
  `d.derivedConstantTower T`, defined by exact `mapDerivedCategory`.
- `DerivedCategory.Q` and `HomotopyCategory.quotient` are the recorded localization
  functors. The termwise factorization is the recorded
  `(d.constantTower T).mapDerivedCategoryFactors`.
- The fixed functorial replacement is the arbitrary functor `J` and the natural
  transformation `ι : 𝟭 _ ⟶ J`. The hypotheses `hι` and `hJ` say, for every tower
  complex M, respectively that ι_M is a quasi-isomorphism and J(M) is K-injective.
  `CochainComplex.IsKInjective` means exactly that maps from acyclic complexes
  are null-homotopic. No additivity of J, boundedness, termwise injectivity or
  monomorphism of ι is imposed.
- Rlim is the actual `completedRlim T (d.completedRing T)` and ordinary lim is
  `completedTowerLimit T (d.completedRing T)`, applied degreewise. The existential
  `z` is a natural transformation on complexes, with object component exactly
  C → lim J(Delta C).
- The first conjunct is `π_n z_C = (ι_(Delta C))_n`, in Lean composition order:
  `(z.app C).f i ≫ limit.π ... (op n) = ((ι.app ...).f i).app (op n)`.
  It is imposed for every integer degree i and every positive tower level n+1.
- The second conjunct quantifies over any other chain map `w` into that same
  ordinary limit and asserts `w = z.app C` if all these projection equations hold.
  This is ordinary limit uniqueness, with no derived joint-monicity assumption.
- The third conjunct supplies a natural transformation η from identity on
  `d.derived T` to Delta_D followed by Rlim. Its normalization equates η with the
  existing `(d.constantRlimAdjunction T).unit`, the constant-tower map already used
  by `d.completionUnit` and `d.pullComparison` in the completed-pullback module.
- For each complex C, the representative formula reads
  η_QC ; Rlim(phi_C ; Q(ι_DeltaC)) = Q(z_C) ; u_JDeltaC.
  Here phi is `mapDerivedCategoryFactors.hom`, and u is `completedRlimUnit` on
  the homotopy image of J(Delta C). Both sides have the same actual target.
  This is precisely the node's fixed comparison, written without an inverse:
  phi and Q(ι) are invertible by exact localization and `hι`; u is invertible
  by `completedRlim_computation` and `hJ`. Multiplying by the inverse of the
  displayed Rlim image gives beta_C Q(z_C), with beta the fixed resolution
  comparison. No arbitrary objectwise isomorphism or cone arrow is introduced.
- The last conjunct quantifies over every `C D : d.derived T` and every derived
  morphism `h : C ⟶ D`, and states
  `η.app C ≫ Rlim.map (Delta_D.map h) = h ≫ η.app D`.
  In particular it includes morphisms represented using inverse quasi-isomorphisms;
  it is not restricted to localized chain maps.

Dependency declarations read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`, `reductionModuleRing`,
  `reductionModules`, `reductionTowerCategory`, `AdicCoefficientDatum.completedRing`,
  `.derived`, `.towers`. The signatures preserve pro-etale site object universe
  t+1 and morphism universe t, with module universe t+1.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`, confirming the inverse-system convention.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`: `Abelian.functorCategoryAbelian`,
  with levelwise evaluation exactness underlying the constant functor.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, its localization instance.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (the exact null-homotopy definition).
- `Sheaf.Paper.CompletedRlimFunctor`: `completedTowerLimit`, `completedRlim`,
  `completedRlimUnit`, `completedRlim_computation`; all are the recorded Rlim
  interface, with its actual universal comparison.
- `Sheaf.Paper.PbcQbarCompletedPullback` retains through public imports
  `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.constantTower`,
  `.derivedConstantTower`, `.constantRlimAdjunction`, `.completionUnit` and
  `.pullComparison`. The statement uses this retained integral ambient interface;
  no Qbar category, field, prime or constructibility assumption is imported into
  its binders.
- Proof imports: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits` supplies
  `SheafOfModules.hasLimitsOfSize` and `evaluationPreservesLimitsOfSize`;
  `Mathlib.CategoryTheory.Localization.Predicate` supplies `Localization.liftNatTrans`,
  `liftNatTrans_app` and `natTrans_ext`. These are the recorded Mathlib leaves.

Source reading: opened the current main-20261015 blueprint proof
`sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`,
which invokes completed pullback and Rlim, and Stacks `injectives.tex`, Tag 079P,
`theorem-K-injective-embedding-grothendieck` (lines 1806 onward), including its
functoriality assertion. The node's six expanded proof steps are reproduced in
order in the theorem docstring. The blueprint itself asserts no invertibility of
this constant-tower unit.

Edge cases checked: zero, acyclic, and single-degree complexes remain allowed;
all degrees are ℤ, without a lower bound. Empty T and zero coefficient rings are
allowed by the same ambient interfaces. The zero and unit ideals are not excluded.
Identity, zero and arbitrary derived morphisms are included. No finite-support
or stabilization hypothesis appears. Naturality of J is used without additivity.
The uniqueness clause applies only to the ordinary limit of complexes. The node
makes no claim that η is an isomorphism, and the Lean makes none either.

Searches actually run (msearch log is `searches.jsonl`):

- LeanFinder: "A functorial K injective resolution of a constant inverse tower
  defines a natural transformation from identity to derived inverse limit".
  Eight hits, including `InjectiveResolution.toRightDerivedZero'`, concern ordinary
  nonnegative derived functors and do not state the unbounded resolution formula.
- Loogle: `CategoryTheory.Localization.liftNatTrans`. Ten hits; the existing
  generic descent interface is used, but it does not supply this resolution unit.
- Mathlib grep: `constLimAdj|derivedη_fac|constant.*[Kk]Injective`. Ten hits;
  ordinary constant-limit adjunction and generic derived-adjunction formulas,
  not the full fixed-resolution statement.
- LeanSearch: "The unit from a complex to the derived inverse limit of its
  constant tower agrees with factoring a functorial K injective resolution
  through the ordinary limit". Eight hits, including `constLimAdj` and
  `HomologicalComplex.instHasLimit`; no exact statement match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  `constantDerivedLimitResolutionUnit|constant.*[Kk]Injective|[Kk]Injective.*constant|completedConstantRlimUnit_exists`.
  The old `CompletedTowerDerivedLimitFunctor.completedConstantRlimUnit_exists`
  normalizes its unit by the ordinary constant-limit unit and universal derived
  comparison, but does not quantify over a specified arbitrary functorial J,
  provide its projection-defined z, or prove uniqueness of that ordinary factorization.
  Reusing the canonical functors and unit is possible; recording that theorem as
  an exact existing match would omit the node's resolution clauses.
- `grep -rn 'lem-cbc-constant-derived-limit-resolution-unit' lean/WeilConjectures`:
  no result. Searches of the completed-pullback modules found and reused the
  existing constant-tower functor and its derived adjunction unit.

Validation: scompile.py compiled the sandbox and library forms cleanly (6.9 s
and 6.3 s on the initial complete signature). Final imports are checked again by
scompile.py and the required delivery dry run. No `STATEMENT-DISPUTED` flag or
source/node fault was found.

## Second reading by NI

A separate reading pass by this same worker was made with the node, source module
and dependency signatures open. No separate agent was started, as the dispatcher
explicitly forbids it; the maintainer's independent delivery review remains required.
The pass checked each of the hypotheses and clauses listed above. In particular,
`hι` is not omitted, `hJ` is on tower complexes rather than individual levels,
Delta is the existing exact functor, and the factorization uniqueness concerns
chain maps. The localization formula was checked for orientation: phi points from
Delta_D(Q C) to Q(Delta C), followed by Q(ι), so the left side lands in Rlim(Q J).
The right side lands there through the recorded universal unit. Its inverse
comparison therefore gives exactly the node's beta_C Q(z_C). The existing derived
adjunction unit fixes the identification with completed pullback, while the final
universal quantifier covers all derived morphisms. No mismatch required a node
correction; direct Mathlib dependency imports were added after the first compile.
