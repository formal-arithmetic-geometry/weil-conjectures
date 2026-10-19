## Worker report

The module `Sheaf.Paper.InternalAdjunctionPairingChange` states
`AlgebraicGeometry.Etale.CoefficientPairingChange.internalAdjunction_pairing_change`.
Its sole new theorem has proof `sorry`. Its helper definitions contain real data;
they expand the operations and maps already specified by this node. There is no
new independent notion, arbitrary map replacement, or asserted Hom-comparison
invertibility.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The fixed algebraic closure of a finite field is `D : WeilConjectures.FiniteFieldDatum`.
  Its `p`, `k₀`, `k`, prime/cardinality fields and algebraic-closure instance are the
  recorded global datum. `l`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E`, `[Field E]`,
  `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]` render the coefficient
  setting. The chosen uniformizer is `Padic.coefficientExtensionUniformizer l E`.
- `n m : ℕ+`, `hmn : m ≤ n` express exactly `n ≥ m ≥ 1`. `coefficient l E n/m` is
  `ULift (Padic.coefficientExtensionRing l E n/m)`, in the required coefficient
  universe `u+1`. `reduction` is the actual quotient factor homomorphism for the
  inclusion of uniformizer-power ideals, lifted by `RingHom.ulift`.
- `X.Over (Spec (CommRingCat.of D.k))` and the `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated` instances on the structure morphism express separated finite type
  over k. `g : Z ⟶ X` with `IsClosedImmersion g` and `j : S ⟶ Z` with
  `IsOpenImmersion j` express the specified factorization. No finite-type,
  separatedness, Noetherian or compactness assumptions on S or Z are added.
- All objects use `Etale.DerivedCategoryModule`, the ordinary unbounded derived
  category of `Sheaf T.smallEtaleTopology (ModuleCat A)`. `scalarExtension` is the
  published ordinary derived extension of scalars, not completed tensor.
- `M`, `L`, `_hM`, `_hL` render membership in Dᵇ_ctf. The existing
  `WeilConjectures.finiteTorConstructibleEtale` is the conjunction of the recorded
  small-etale bounded constructibility and an interval of Tor amplitude tested
  on every degree-zero module sheaf. `_hN` and `_hQ` impose the same property on
  exactly N and Q, rather than on unrelated witnesses.
- `exceptional A g j` is the actual right adjoint of `Rg_*`, followed by exact
  derived open restriction. Thus its object at M is N. `derivedHom` evaluated at
  `(op L,N)` is Q. `shriek A g j` is exactly `Rg_* ∘ j_!`.
- `star A g j` writes ordinary direct image as `Rg_* ∘ Rj_*`, under its canonical
  composition identification. `ordinaryCounit` is the counit of the composed
  adjunction `Lg^* ⋙ Lj^* ⊣ Rj_* ⋙ Rg_*`. `ordinaryComparison` is `c_g` followed
  by `Rg_*(c_j)`, hence `c_s` under the same canonical identification and the
  composition normalization of `finiteCoefficientDirectImageMap`.
- `projection` first applies the published proper projection map for g to the
  pushed object **j_!L**, then applies `Rg_*` to the inverse published open
  projection isomorphism. The resulting tensor order is `L ⊗ s^*T`, consistently
  with the existing left-tensor/Hom adjunction. This is the node's projection
  pairing after its canonical tensor symmetry, not an arbitrary projection iso.
- `internalAdjunction` transposes this projection, followed by `s_!` of tensoring
  the ordinary counit with L, then the actual tensor-Hom evaluation counit, then
  `counit A g j M`. The last counit is literally the counit of the composite
  `j_! ⊣ j^*` and `Rg_* ⊣ Rg^!` adjunctions. Thus I_A and I_B are defined by the
  required pairings. Calling the helper at B supplies exactly the B pairing.
- `compactComparison` is literally `c_{g,j_!L}` followed by `Rg_{*,B}(q_{j,L})`.
  It uses the published fixed `openScalarExtension`; it does not replace q_s by
  an arbitrary map or by a mere existence of an isomorphism.
- `b` is an isomorphism from `F_S N` to `s_B^! F_X M`. `_hb` is exactly
  `q_{s,N} ≫ s_{!,B}.map b.hom ≫ ε_{s,B} = F_X.map ε_{s,A}`, using Lean's
  left-to-right composition convention. The node assumes this equation; no
  extra compatibility condition on b is imposed.
- `evaluationComparison` is the actual B tensor-Hom transpose of the published
  normalized `etaleHomTensorComparison` followed by scalar change of A evaluation.
  At `(S,L,N)` this is u; at `(X,s_{!,A}L,M)` it is v. Its construction imposes
  no IsIso hypothesis or inverse. The added landed dependency
  `lem-coef-etale-hom-thick-locus` owns the normalized tensor comparison used here.
- The conclusion `PairingChangeEquation` is a transparent definition of exactly
  the displayed equality; `CounitCompatible` transparently expands `_hb`. Its
  equality composes, in order, `c_s`, `Rs_{*,B}` of u followed by
  `H_B(1,b)`, I_B, and the contravariant Hom map induced by q_s. The right side
  is scalar change of I_A followed by v. Both are maps out of `F_X Rs_{*,A}Q`
  into `H_B(F_X s_{!,A}L,F_X M)`. This states equality of the actual arrows,
  including the last sentence identifying the evaluation transpose.

Dependency declarations inspected and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public coefficient
  construction: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionIdeal`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` (existing dependency repair below).
  The conjunction is reused through
  `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`: `Etale.derivedHom` and
  `Etale.derivedTensorHomAdjunction`, the existing constant-coefficient
  specialization of derived internal Hom. The recorded general
  `CategoryTheory.derivedInternalHomOfUniverses` and its K-injective construction
  were read; the different ringed-module presentation is not copied here.
- `Sheaf.Paper.EtaleDerivedScalarTensor`: `Etale.scalarExtension`, the public
  `ProEtale.pbcFixedScalarExtension` specialized to the small-etale topology.
  The recorded `DerivedChangeOfRingsCochainModel` signature and docstring were
  read; the constant-coefficient specialization already exists.
- `Sheaf.SixFunctors.EtaleOpenTensor`: `Etale.derivedExtension`,
  `Etale.derivedRestriction`, `Etale.openScalarExtension`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `Etale.rightDerivedLowerStarProjectionMap`.
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`:
  `Etale.derivedOpenImmersionLowerShriekProjectionIso`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`, hence the
  actual `Functor.rightAdjoint` and `Adjunction.ofIsLeftAdjoint`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`:
  `Etale.finiteCoefficientDirectImageMap`, normalized by its counit equation;
  its composition formula justifies the composition coordinates for c_s.
- `Sheaf.SixFunctors.EtaleHomThickLocus`:
  `Etale.etaleHomTensorComparison`, fixed uniquely by the K-flat balancing
  normalization. No thick-locus or Hom-invertibility result is assumed.
- Proof imports: `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`,
  `CategoryTheory.scalarInternalHomAdjunction_exists`, and
  `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`,
  `Etale.internalAdjunctionEvaluation`. Their full signatures and normalization
  docstrings were read. The proof dependency `lem-coef-etale-locally-closed-shriek`
  has no recorded module at this base; its q_s construction is explicitly
  composed from the recorded open and closed maps, and the needed exceptional
  counit equation is already the item's hypothesis, so no additional theorem
  is used as a prerequisite.

Edge cases checked against the actual expressions: m=n (quotient identity), m=1,
j the identity (S=Z, closed case), g the identity (open case), empty S, and zero L
or M. No Nonempty assumption on the strata or objects, positive cohomological
bound, flatness of the reduction, or invertibility of u/v is present. Site object
universe u+1 and morphism universe u are retained with module values in u+1.
All universe and term variables are explicitly bound; `autoImplicit` is false.

Searches made before drafting:

- `msearch.py ... leanfinder "scalar extension compatibility with internal Hom
  adjunction pairing for compact support direct image"`: condensed internal-Hom
  pointwise naturality, ordinary ModuleCat scalar adjunctions and compact-support
  continuous maps; no match for this derived pairing equality.
- `msearch.py ... loogle "CategoryTheory.Adjunction.homEquiv,
  CategoryTheory.MonoidalClosed.curry"`: three generic curry/uncurry formulas;
  none states this coefficient/open/closed compatibility.
- `msearch.py ... leansearch "Coefficient change commutes with the internal
  adjunction pairing for compact support on an etale stratum"`: unrelated
  root-pairing, coalgebra, and condensed locally-constant adjunction hits; no match.
- `msearch.py ... grep "internalAdjunction|exceptionalCounit|compactSupport.*Hom"
  CategoryTheory`: zero Mathlib hits.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`
  for internalAdjunction, compact-support/Hom and coefficient comparison terms
  located the published tensor-Hom adjunction, evaluation lemma, scalar tensor
  comparison, open tensor maps and direct-image coefficient maps used here.
  `FiniteClosedShriek` was inspected and rejected for reuse: its helpers live on
  the **pro-etale** site and use the opposite closed-then-open factorization.
- `rg` for the item id in upstream sources and `dag/lean_names_upstream.json`
  found no binding. Searches for the proposed namespace and theorem name in
  upstream and `lean/Sheaf` found no existing declaration. A broad search for
  evaluationComparison found unrelated enriched-presheaf structure fields only.

No statement correction or STATEMENT-DISPUTED flag is needed.

## Dependency modules

`lem-asd-internal-adjunction-evaluation`: module-format repair only. Its published
file begins with imports and has no `module` header. The required scompile run
rejected its import from the new module with `cannot import non-module
Sheaf.SmoothPurity.InternalAdjunctionEvaluation from module`. The delivered copy
adds `module` and changes the existing imports to `public import`. Its entire
mathematical declaration, existing proof docstring, and sorry proof are retained.
This fixes the actual compiler failure without dropping the required proof import.

`def-weil-pbc-constructible-complexes`: existing-interface repair only. The current
record points to `OrientedNearbyCycles.IsBoundedConstructible` on the transported
`EtaleDerived` category, while this node uses ordinary `DerivedCategoryModule`.
The exact existing small-etale declaration
`Etale.DerivedCategory.isBoundedConstructible` is already publicly imported by
that transported wrapper. The lean-only repair records this declaration and
`BoundedConstructibleDerivedCategory` with existing:true, adding no module or
second definition. The record's note explains both presentations.

## Second reading by Q74

Author self-check under the dispatcher protocol; no independent reviewer is
claimed. I reread the node with the complete Lean file open. The coefficient
levels and quotient map, separated finite-type X, actual open/closed maps,
four finite-Tor constructibility hypotheses, specific projection factors,
ordinary counit, evaluation, pasted exceptional counit, and the normalization
hypothesis on b are all matched above. I checked the direction of every map in
the final equality, especially contravariance in q_s and covariance in b. The
ordinary direct-image composition is used consistently in its counit and its
coefficient map, so no unmatched composite-map identification is suppressed.
The source proof paragraph was read in full; the construction uses exactly
its evaluations and adjunction counits. The dependency changes repair import
format and presentation lookup only, without changing their mathematical text.
Independent mathematical review is left to the maintainer as the brief specifies.

Elaboration repair: the coefficient-generic transparent propositions
`CounitCompatible` and `PairingChangeEquation` keep the exact normalization and
map equality while avoiding repeated elaboration of the Padic quotient type in
each factor. They contain the formulas, not quantified arbitrary diagrams.

Validation: the prescribed `scompile.py Q74 lem-coef-internal-adjunction-pairing-change`
run compiled each delivered file separately in dependency order, including its final
library path, without errors or warnings. Final-path times were 6.3 seconds for the
module-format dependency repair and 11.0 seconds for the main statement. The earlier
unfactored quotient-specialized equation timed out; the transparent generic formula
repair above resolved it without changing the statement or increasing the time limit.
