## Worker report

Repaired `Sheaf.Paper.FiniteEtaleDescent` after the independent H3 return on
immutable head `87772e94d5bf`. The required initial dry run of the retained packet
passed at `ba0520003d`, but the retained Lean signature still lacked the canonical
comparison's invertibility and the explicit inverse-transpose identification.
This repair adds those assertions; it is not an unchanged re-push. The source
statement and DAG proof are unchanged. Comparison with the current shared node
shows that only `lean` differs. The delivery wrapper rebuilds on current
newtargets-dag; no direct Git command was run in the shared repository.

The module states `WeilConjectures.finiteCoefficientEtaleDescent` with one `sorry`.
Every helper has real data; no additional postponed theorem or new notion is needed.
All eight declarations (seven helpers and the main theorem) are now listed in
`lean.declarations`.

Hypothesis-by-hypothesis correspondence:

* The global datum fixing the algebraic closure k is `D : FiniteFieldDatum.{u}`;
  the prime is `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`.
* The single finite coefficient field is `E : Type u`, with `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`. There is no
  second field L or arbitrary ring homomorphism binder.
* The coefficient levels are `m n : ℕ`, `hm : 1 ≤ m`, `hn : 1 ≤ n`, and
  `hmn : m ≤ n`. A is the canonical universe lift of
  `Padic.coefficientExtensionRing l E n`; B is the corresponding ring at m.
  Every coefficient change uses `finiteEtaleReduction l E m n hmn`, the lift
  of `Ideal.Quotient.factor` for the inclusion of the nth power ideal into
  the mth power ideal. Thus phi is exactly the specified quotient A_n → A_m.
* `X Z : Over (Spec (CommRingCat.of D.k))` are k-schemes. The three instances
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on each structure
  morphism express separated finite type. `i : Z ⟶ X` is over k and
  `[IsClosedImmersion i.left]` supplies closedness.
* `M` is in the ordinary small-etale A-derived category. Its hypothesis `hM`
  is the recorded `Etale.DerivedCategory.constructibleFiniteTor`: bounded
  constructibility and the finite Tor interval against degree-zero sheaves.
  There is no flatness or projective-dimension assumption on B over A.

Clause-by-clause correspondence:

1. `finiteEtaleExceptional` and `finiteEtaleExceptionalAdjunction` give G_R
   as the right adjoint to the actual ordinary etale R i_*. They install the
   positive-stage finite-ring instance and use the recorded ambient adjunction.
2. The first and second output conjuncts give finite-Tor constructibility of
   G_A M and TM, as established in the node's proof and retained from the
   returned version. The third conjunct gives G_B TM in D^b_ctf(Z_et,B).
   The fourth conjunct, newly added, gives T G_A M in that very same category.
3. The existential `b` has exactly the source T G_A M and target G_B TM.
   `IsIso b` renders its isomorphism assertion. The next conjunct explicitly
   asserts `IsIso c` for the recorded `Etale.finiteCoefficientDirectImageMap`
   at G_A M. The typed existential `cInv` has source i_{*,B} T G_A M and
   target T i_{*,A} G_A M, and `c ≫ cInv = 𝟙 _` and `cInv ≫ c = 𝟙 _`
   uniquely identify it with c^{-1}. The equation
   `b = (finiteEtaleExceptionalAdjunction ...).homEquiv _ _
     (cInv ≫ T.map epsilon_A)` now states the required exceptional-counit
   transpose literally. The original equation
   `c ≫ i_*(b) ≫ epsilon_B = T(epsilon_A)` is retained too. Thus the claimed
   equivalence no longer relies on an unstated invertibility assumption.
4. The final existential supplies the exceptional identifications `eA` and
   `eB`. Their homs are required to equal
   `finiteEtaleExceptionalComparisonMap` at M and TM, respectively. This
   helper uses `Adjunction.rightAdjointUniq` with the canonical proper
   direct-image isomorphism and then applies the ordinary exceptional
   functor and comparison pullback to the actual derived comparison unit.
   Hence these are the normalized transported-exceptional identifications;
   the theorem does not accept arbitrary endpoint isomorphisms.
5. Tensor pullback uses the existing canonical
   `ProEtale.pbcComparisonReduction`, in the inverse direction t: C_B T ≅
   T^p C_A. Its definition is the mate of the actual restriction-of-scalars
   comparison and its inverse is normalized on K-flat pure tensors. The
   last equality is, in the node's notation,
   `C_Z,B(b) ≫ eB.hom ≫ G_B^p(t_X,M) =
    t_Z,G_A M ≫ T^p(eA.hom) ≫ b^p_(i,C_X,A M)`.
   `finiteEtaleClosedShriekMap` is exactly `finiteClosedShriekMap` for this
   quotient, with only the two finite-ring instances installed. This is
   the missing equality with the recorded pro-etale map at nu_X^* M.
6. The preceding universal conjunct quantifies over any bounded-below
   ordinary etale B-objects K,N and any two arrows f,g between them. It
   states `f = g ↔ C_Z,B.map f = C_Z,B.map g`. Composing either path in a
   diagram gives such a pair, so this is precisely the requested test for
   diagram equality. It applies to the two outputs by their bounded typing.

Dependency declarations and supporting canonical interfaces used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient-ring and
  power-ideal constructions it imports.
* Mathlib scheme predicates: `AlgebraicGeometry.IsClosedImmersion`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`; the recorded bounded constructibility
  interface and `Etale.DerivedCategory.constructibleFiniteTor`.
* `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules` and its specified module pullback.
* `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt` reexports
  `SfFiniteExceptionalInverseImage`; the fixed small-coefficient presentation
  used by the required closed-shriek map is `ProEtale.sfFiniteExceptionalFixed`,
  through `WeilConjectures.finiteClosedExceptional`.
* `Sheaf.Paper.FiniteClosedShriek`: `finiteClosedDerived`, `finiteClosedScalar`,
  `finiteClosedExceptional`, and `finiteClosedShriekMap`.
* `Sheaf.Paper.FiniteCoefficientDirectImage`:
  `Etale.finiteCoefficientDirectImageMap`.
* `Sheaf.Paper.EtaleDerivedScalarTensor`: `Etale.scalarExtension`, the recorded
  ordinary derived coefficient extension in fixed-ring coordinates; its
  reexports retain the ring-sheaf change-of-rings interfaces.
* `Sheaf.Paper.WitnessCompatibility` (reexported by the preceding modules):
  `ProEtale.pbcComparisonReduction`, the canonical tensor-pullback isomorphism.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar`:
  `Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`.
* `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`:
  `Etale.rightDerivedUpperShriek` and its adjunction.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison`:
  `ProEtale.derivedComparisonAdjunction` and its actual unit.
* Mathlib `CategoryTheory.Adjunction.rightAdjointUniq` fixes the bridge
  between the two ordinary etale right-adjoint presentations.

The old checkout lacks some current source modules. They were read with the
prescribed `scompile.py --source`, notably the current etale upper shriek,
canonical maps, lower shriek, and finite-coefficient derived comparison modules.
The 51-module framework and `coord/pefw-upstream-framework.md` were read in the
specified shared checkout. No source or live artifact was edited directly.

Edge cases checked: m=n is included, and the actual quotient map is retained
in that case; m=1 is allowed and n=0 is excluded exactly by positivity. Empty
Z, the identity immersion, and M=0 are allowed. Non-flat reductions, such as
O_E/varpi^2 → O_E/varpi, remain included. No additional coefficient or site
universe equality, flatness hypothesis, choice of scalar map, or unspecified
exceptional adjunction was introduced. For equality tests, parallel maps
may include zero arrows, and the formulation applies to arbitrary composites.

Searches run before writing:

* `msearch.py Q03 lem-coef-finite-etale-descent leanfinder "closed immersion exceptional inverse image coefficient quotient comparison descends from pro etale to etale constructible finite Tor amplitude"`: only general étale algebra and scheme/sheaf infrastructure; no match.
* `msearch.py ... leansearch "etale proetale comparison closed immersion exceptional inverse image change finite coefficients quotient"`: only closed-immersion predicates; no theorem.
* `msearch.py ... leanfinder "exact conservative pullback reflects bounded constructible etale complexes from proetale site comparison"`: coherent-topology sheaf comparisons; no match.
* `msearch.py ... loogle "exceptional"`: `LinearEquiv.IsExceptional` and unrelated linear algebra.
* `msearch.py ... grep "exceptional|proetale|proétale" Mathlib/AlgebraicGeometry`: pro-étale site infrastructure only.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` for `lem-coef-finite-etale-descent`,
  `finiteCoefficientEtaleDescent`, and exceptional coefficient descent: no existing
  declaration of this item; related ordinary direct-image and pro-étale closed-shriek
  interfaces were reused.


Repair searches:

* `msearch.py ... leanfinder "canonical comparison of derived scalar extension and
  etale to proetale pullback using the exceptional adjunction unit"`: eight
  generic Mathlib hits, none the required coefficient/exceptional comparison.
* `msearch.py ... loogle "Adjunction.rightAdjointUniq,
  ProEtale.pbcComparisonReduction"`: no indexed hits (unknown identifier).
  Direct source inspection found both existing canonical interfaces.
* `msearch.py ... grep
  "pbcComparisonReduction|rightDerivedLowerShriekIsoRightDerivedLowerStar"
  CategoryTheory`: no Mathlib match.
* `rg` in project `lean/Sheaf` found `WitnessCompatibility.pbcComparisonReduction`
  and the exceptional transport definitions, which are reused. `rg` in the
  specified upstream checkout found no item declaration. The project
  `LowerShriekToLowerStar` source gives the required proper isomorphism.

No new node, dependency repair module, statement correction, or
`STATEMENT-DISPUTED` flag is needed. The three added helper definitions belong
exactly to the canonical identifications and positive-ring-instance adapters
required by this node. They are source documented and listed in the lean record.
The theorem docstring now spells out the seven DAG proof steps, including
tensor compatibility and exceptional-counit normalization.

## Second reading by Q03

This is the repairing worker's self-check; no second agent was started, as the
repair brief explicitly prohibits other agents. I reread the current node, the
saved report, the full revised Lean signature, the canonical comparison sources,
and the consumer `lem-coef-finite-free-extension` step 17.

Return (1) is repaired by the explicit comparison equation at nu_X^* M and the
universal bounded-below equality test; eA/eB are fixed by the actual unit maps,
and the tensor isomorphism is the existing normalized scalar mate. These two
clauses supply exactly the map identification and diagram descent needed by
consumer step 17. Return (2) is repaired by E alone, `hmn : m ≤ n`, A at n,
B at m, and the specified reduction in every coefficient position. Return (3)
is repaired by the fourth finite-Tor output conjunct. Return (4) is repaired
by recording every declaration; each of the seven helpers is used by the
main signature or a helper that it uses. There are no unused helper definitions.

The first repaired compile elaborated successfully and reported only three long
lines and one blank line inside the theorem command. Those formatting issues were
fixed before the final compile. Every definition contains real data, and the
main theorem remains the only `sorry`. The final per-file `scompile.py` check passed without errors or warnings
(sandbox 6.6 s; library file 21.4 s). The delivery dry run is rerun before the push.

## Repair of return at 87772e94d5bf

H3 is repaired in the conclusion, with no new hypothesis: `IsIso c`, a two-sided
inverse of that exact canonical c, and the explicit adjunction `homEquiv`
identification of b with the exceptional transpose of c^{-1} followed by
T(epsilon_A). The source and target of cInv were checked against
`Etale.finiteCoefficientDirectImageMap`; the adjunction is the existing
`finiteEtaleExceptionalAdjunction`. No arbitrary map replaces c and no stronger
coefficient assumption is used. The extra inverse witness is uniquely determined
by its two inverse equations. The earlier report's claim that the bare counit
equation was equivalent to the transpose was insufficient without IsIso c;
that missing assertion and the transpose identification are now explicit.

The final rereading matches the base-field, prime, coefficient field, positive
levels, specified quotient, separated finite-type k-schemes, closed immersion,
and finite-Tor constructible input binders to the unchanged node. It checks all
four finite-Tor conclusions, IsIso b, the canonical inverse-transpose equation,
the normalized exceptional and tensor transport equality with the specified
pro-etale map, and equality reflection on bounded-below etale objects. The
new assertions still include m=n, m=1<n with nonflat reduction, the identity
immersion, empty Z and M=0. At m=n the quotient and its canonical comparison
remain the actual maps rather than arbitrary identifications. All helper data
and all seven helper declaration records remain unchanged; only the main
signature and lean note/date are refreshed. There is exactly one postponed
proof, the theorem's existing `sorry`.

Validation of the final module by `scompile.py` passed cleanly (sandbox 10.7 s,
library file 23.0 s; default 60-second per-file limit). The node's lean.statement
was re-extracted verbatim from that final signature. The final delivery dry run
and push follow this self-check. This is the repairing worker's own reading;
no other agent was started, as expressly required by the dispatcher brief.
