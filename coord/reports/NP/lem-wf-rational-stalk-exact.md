## Worker report

The delivery states `WeilConjectures.wfRationalStalkExact` in
`Sheaf.Paper.RationalStalkExact`. The only postponed declaration is that theorem,
with `sorry`; its docstring gives all four proof steps of the node. The node's
statement, statement dependencies, proof, and proof dependencies are unchanged.
All ten helper definitions have actual data. They supply the common-stage
specialization of the local operator needed by this item, as authorized by the
brief's missing-helper rule; they introduce no independent replacement notion.

Hypothesis and clause correspondence:

- The global tuple `(p,a,q,k₀,k)` is the existing `FiniteFieldDatum.{u}` named `D`.
  Its fields include primality of `p`, `1 ≤ a`, `q = p^a`, `Nat.card k₀ = q`,
  and `IsAlgClosure k₀ k`. The coefficient prime is `l` with `[Fact l.Prime]`
  and `hl : l ≠ D.p`. The fixed coefficient closure is `Ω` with `[Field Ω]`,
  `[Algebra (Padic l) Ω]`, and `[IsAlgClosure (Padic l) Ω]`.
- The model is `Y₀ : Over (Spec (.of D.k₀))`. Finite type is exactly
  `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`, and separatedness is
  `[IsSeparated Y₀.hom]`. The geometric fibre is the dependency's
  `(D.geometricFiber Y₀).left`, used throughout, not a new base-change model.
- `F₁ F₂ F₃ : sfCommonStageWeilSheaf D l hl Y₀ Ω` are precisely the full
  heart-carrier fixed pairs of the two recorded dependency modules. These are
  neither arbitrary sheaves on the pro-etale topos nor the derived category of
  Weil sheaves. The arrows `i` and `j` belong to this category, so their
  underlying maps commute with the Weil isomorphisms by the IsoAlgebra Hom
  condition. No additional commutation hypothesis is introduced.
- `wfHeartForget` maps these pairs into `sfCommonStageHeart`, retaining their
  literal carriers and underlying arrows. `w` is their zero composite there;
  `hS` is `ShortComplex.ShortExact` for those same two arrows. This expresses
  a short exact sequence of Weil sheaves by its underlying heart sequence,
  the usual induced exact structure. In particular no exactness is assumed
  in the ambient triangulated category. The separate zero-composite proof
  packages the sequence; it imposes no further mathematical condition beyond
  being a short complex. `ShortExact` means exact, mono first map, epi second.
- The closed point is `y : {y : Y₀.left // y ∈ closedPoints Y₀.left}`.
  Its chosen residue-field embedding is `ι : Y₀.left.residueField y.val →+* D.k`.
  A unital map of fields is injective. `hι` specifies that it is over `k₀`,
  which is required to form the associated point of the geometric fibre.
  That point is exactly the recorded `localClosedPoint D Y₀ y ι hι`.
- `wfPointFunctor` is the recorded `commonStageDerivedPullback` followed by
  the recorded `pointQbarFibre`. `wfSheafFibre` restricts it to the heart and
  applies `DerivedCategory.coefficientQbarCohomology l Ω 0`. Thus the fibre
  is the prescribed degree-zero rational coefficient fibre over `Ω`, including
  the canonical scalar realization from its finite coefficient stage.
- The conclusion's `∃ w'` and `ShortComplex.mk ... w' |>.ShortExact` give
  exactly the short exact sequence of the two induced fibre maps, including
  injectivity at the left and surjectivity at the right. The following three
  `FiniteDimensional Ω` clauses apply respectively to `F₁`, `F₂`, and `F₃`.
- `wfClosedFrobenius` is the common-stage counterpart of the recorded
  `localClosedFrobenius`: iterate the Weil isomorphism, iterate point transport,
  use the recorded `localClosedPoint_return`, then pull back the iterated
  isomorphism. Its positive-power index is `localClosedPointDegree ... - 1`,
  hence its exponent is the actual positive residue degree. The return is
  `g_Y^r xbar = xbar g_s^r`; the point is not falsely assumed fixed as a scheme map.
  `wfSheafClosedFrobenius` applies coefficient H^0 to that operator. The final
  two equalities assert `i_x ≫ F₂ = F₁ ≫ i_x` and `j_x ≫ F₃ = F₂ ≫ j_x`.

Dependency declarations read and used:

- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty` and
  `sfCommonStageHeart`, the recorded intersection of the two standard classes
  and its full subcategory.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilSheaf`, `sfWeilPrimeInvertible`.
  `IsoAlgebra` and its faithful forgetful functor are those imported from
  `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPullbackComposition`,
  `localPullbackObjectIso`, `localPositivePower`, `localClosedPoint`,
  `localClosedPointDegree`, `localClosedPoint_return`. Its finite-E operator
  is preserved and used as the source convention, not duplicated at E.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`,
  `commonStageDerivedPullback_existsUnique`, `commonStagePullbackObject`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `inclusion` and the
  existing literal finite-stage pair construction.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointQbarFibre`,
  `pointQbarFibre_existsUnique`, and `pointQbarFibreObj`.
  `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `frobeniusPointTransportQbar`, `frobeniusPointQbarPullbackObj`,
  `frobeniusPointPrimeInvertible`, `frobeniusPointIso`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `coefficientQbarCohomology`.
- `Sheaf.Paper.IntegralPullbackComposition`: the stated proof dependency,
  whose specified natural integral comparison is localized by
  `localPullbackComposition` and included at the literal finite stage by
  `wfPullbackComposition`. All specified object equalities are transported by
  `eqToIso`; no arbitrary natural-isomorphism choice is substituted.

The other proof-only nodes (`lem-dl-a1-constructible-fibres-exact`,
`lem-weil-frobenius-point-transport-natural`,
`lem-trf-integral-pullback-comparison-realization`, and
`lem-trf-local-frobenius-transport-normalization`) have no recorded Lean module
in the read base. They are cited in the theorem's full proof docstring and
are not extra statement prerequisites. No node is silently restated.

Edge cases checked: the empty model has no closed point, so the assertion is
vacuous; zero fibres and the zero short exact sequence remain allowed, with
no nonzero-vector-space assumption. A degree-one closed point uses positive
index zero and one application of the Weil isomorphism and point transport.
An arbitrary higher residue degree uses exactly that degree, without choosing
an unrelated extension degree. All choices of the residue embedding are
quantified. There is no assumption that the chosen geometric point is fixed
by Frobenius as a scheme map. No torsion or integral fibre is substituted for
the rational fibre. Arbitrary algebraic closures are allowed as the existing
coefficient category permits; `u` is arbitrary and a common ambient universe
contains all the finite-field and coefficient data. No site object/morphism
universe equality is imposed.

Searches made (2026-10-17 UTC):

- `msearch.py ... leanfinder "Exact rational constructible Weil sheaf coefficient fibres and Frobenius equivariance"`:
  eight unrelated perfection/Witt-vector results, including `PreTilt.coeff_frobenius`
  and `WittVector.IsocrystalHom.frob_equivariant`; no matching statement.
- `msearch.py ... loogle "ShortComplex.ShortExact"`: no hits because the short
  identifier was not recognized. The actual Mathlib declaration was read in
  `Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean` and reused.
- `msearch.py ... grep "localFrobenius|WeilSheaf|stalk.*[Ee]xact"`:
  six hits, ordinary topological stalk exactness in `Topology/Sheaves/Abelian.lean`
  and `Stalks.lean`; none concerns these adic common-stage fibres.
- `msearch.py ... leansearch "The stalk functor on rational constructible Weil sheaves preserves short exact sequences"`:
  eight hits, primarily topological stalk definitions and preservation of monos;
  the relevant generic result `CategoryTheory.ShortComplex.ShortExact.map_of_exact`
  supplies abstract exact-functor calculus, not this coefficient/frobenius statement.
- `rg -n 'short exact|Exact|exact.*[Ff]ibre|Frobenius.*commut|commut.*Frobenius|localFrobenius' lean/Sheaf`:
  the recorded local operator, point fibre, and many unrelated exactness results;
  no complete attachment for this node.
- `rg -n 'shortExact|stalkFunctor' WeilConjectures/WeilSheaf/StalkFunctor.lean`
  and the source concept search found `AlgebraicGeometry.WeilSheaf.stalkFunctor`
  and `stalkAt_frobenius_map`. Their full types were read. They use the older
  `AlgebraicGeometry.WeilSheaf`, `AdicSheaf`, `WeilCoefficients`, and the literal
  `AlgebraicClosure k₀`, rather than the recorded common-stage heart and rational
  point fibre. They therefore are not an exact existing match for this node.
- `grep -rn 'lem-wf-rational-stalk-exact' WeilConjectures`: no hits.
- Grep for the delivered `wf...` declaration names in both source trees: no collisions.

No statement dispute, source correction, new definition node, or dependency-record
repair is required. The missing helpers are canonical parts of the node's named
rational Frobenius fibre, using the exact dependency constructions.

## Second reading by NP

This is the same worker's separate rereading; the dispatcher forbids starting
other agents, and the maintainer performs the independent delivery review.
I reopened the node and the final module and matched all hypotheses and the six
conclusion clauses. The final statement uses Ω coefficients and the recorded
common-stage heart. I specifically checked that short exactness is in the heart,
not the ambient derived category, that the maps are actual commuting Weil maps,
and that both intertwining equations have the correct source and target.
The middle term in the first equation is F₂, and the third term in the second
is F₃. The three finite-dimensionality assertions name all three fibres.
The point helper uses the chosen residue embedding and its k₀ equation, and
the return helper uses reparametrization with the actual residue degree.
The construction contains no extra finite-stage presentation assumption and no
assumed compatibility theorem. Its comparison is the existing integral comparison
localized at the literal stage. No definition has postponed data. The theorem's
proof is `sorry`, with the node's complete proof in its docstring. The earlier
scratch draft at finite E was discarded; it is not part of the delivery. The
final node has only its `lean` field changed.
