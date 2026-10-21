## Worker report

The module `Sheaf.Paper.FdCompletionInverseScalarCoherence` states
`WeilConjectures.fdCompletionInverseScalarCoherence`, with its single proof `sorry`.
It supplies the specified integral completion comparison and the coherent rational
inverse. Three owning-node helpers package the conclusion: the predicate
`FdInverseScalarCoherence`, the integral comparison record
`FdCompletionIntegralComparison`, and the combined record
`FdCompletionScalarComparison`. These are explicit definitions/structures with no
postponed data. They introduce no independent coefficient category or scalar functor.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The global datum is `_D : FiniteFieldDatum.{d}`. The prime is `l`, with
  `[Fact l.Prime]` and `_hl : l ≠ _D.p`. The ambient closure is `Ω : Type w`
  with `Field`, `Algebra ℚ_[l]`, and `IsAlgClosure ℚ_[l]` instances.
* `T : Scheme.{u}`, `[IsNoetherian T]`, `dT`, and `iT` respectively express the
  scheme, noetherian, finite-dimensional, and stalkwise invertibility assumptions.
  The universes of the global datum, scheme, and algebraic closure are independent.
* Finite fields are exactly `Padic.FiniteCoefficientFields l Ω`. The recorded
  `pbcFiniteField.{u}` and framework `Coefficient.{u}` give their canonical small
  models. This size transport excludes no finite extension, including the base field.
* The hypothesis `stage : ∀ E, FdRationalStageComparison l Ω T E` is precisely
  the stipulated integral identity `I` and raw rational identity `J`. Its
  `integral_identity` fixes restriction along the quotient-normalized coefficient
  isomorphism; `objects`, `tensors`, `shift_normalization`, `exact`, and
  `inverse_triangles` retain identity on integral objects and tensor factors and
  the stipulated exact shifts. No coefficient-comparison datum containing scalar
  coherence is assumed: only its already defined finite-stage identity portion.
* `FdCompletionIntegralComparison.ordinary` uses the existing
  `FdOrdinaryScalarTransport`; its `generators` field fixes ordinary transport on
  every sheafified tensor generator. `comparison` is the ambient integral iso
  from ordinary PBC extension to framework strict-tower extension after transport.
* `chi` is verbatim the complex-localization normalization of
  `FdCoefficientComparison.chi`, with the new comparison substituted. It includes
  `pbcComplexCounit`, `fdCoefficientTransportFactors`, the specified
  `integralScalarExtensionComparison`, and `ordinary.completion`. That last map
  is explicitly the tensor transport followed by `completedScalarChainComparison`:
  its quotient-map coordinates and zero shifted-product coordinate are exactly the
  ones of `completedScalarChainComparison_existsUnique`. This retains the actual
  specified chi map, rather than an arbitrary isomorphism of its endpoints.
* `integral` is its restriction to the two integral full subcategories.
  `restriction` equates its underlying ambient component with `comparison`.
* `FdCompletionScalarComparison.family` is a morphism of the ACTUAL framework
  and PBC scalar systems from the dependency record; `finite_functor` identifies
  its finite functors with the supplied `J`. Its `β` points from ordinary PBC
  extension to framework extension; consequently the comparison called `j` in
  the node is exactly `(family.β h).symm`.
* `scalar_lift` says that `β.hom` is the raw localization of the integral chi
  comparison, preceded by `pbcScalarIntegralComparison`. Thus its inverse is
  exactly the rationalized inverse, including the nontrivial tensor-unit
  normalization at equal fields. This is the same integral-lift equation used by
  `FdCoefficientComparison.integral_scalar_lift`.
* `finite_shift_normalization` fixes the finite functor shifts to those of `J`;
  `scalar_shift` requires BOTH `β.hom` and `β.inv` to commute with these specified
  integer shifts. `exact` records exactness of the finite functors; the scalar
  extensions have their existing specified exact structures. Hence `β.symm` is
  an exact natural isomorphism, including its last-arrow shift equation.
* `unit` identifies `j` at `E = E` with `J` of the framework unitor, while PBC's
  scalar system has literal identity transitions. The existing framework
  unitor uses tensor multiplication followed by the completeness comparison.
  The cocycle below, with `h` or `k` reflexive, is exactly the two unit comparison
  squares. All fields equal gives their common degeneration.
* `FdInverseScalarCoherence` first states
  `j_k(S_h K) ≫ P_k(j_h K) ≫ aP_hk(J_E K) = J_M(aS_hk(K)) ≫ j_hk(K)`.
  Lean's `≫` reads left to right, so this is exactly the displayed equation in
  the node, whose `∘` reads right to left. The scalar associators are the recorded
  ones: framework `stageSystem` uses the chi-conjugated
  `sfRationalScalarComp`, and PBC `pbcScalarSystem` uses the normalized balancing
  `pbcScalarAssociator`. The forward cocycle also remains in `family.coh`.
* The second conjunct of `FdInverseScalarCoherence` explicitly writes the
  threefold successive inverse comparison `D`, followed by each of the two PBC
  associator contractions. BOTH equal `J_N` of the first framework associator
  contraction followed by `j_N/E`. The framework pentagon identifies the other
  framework contraction with this one. These are the two contractions of the
  stated four-field compatibility diagram, not an unrelated associator equality.
  Every inclusion uses `≤`, never strict inclusion.

Dependency declarations read and used (each module is under `Sheaf.Paper` unless
otherwise stated):

* `FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension` and its
  uniquely prescribed integral object and tensor formulas.
* `PbcRationalCategory`: `AlgebraicGeometry.Scheme.PbcRationalDerivedCategory`
  and `pbcRationalization` (raw scalar localization, unchanged objects).
* `SfScalarExtensionComposition`: `sfIntegralOrdinaryComparison`,
  `sfIntegralScalarComp`, `sfRationalScalarComp`, `sfRationalScalarUnit`, and
  `sfRationalScalar_coherence` (specified ordinary conjugation, units, pentagon).
* `PbcScalarExtension`: `AlgebraicGeometry.Scheme.pbcCoherentScalarExtension`,
  with `pbcRationalScalarComp`/`pbcStageAssociator` and normalized units. The
  comparison datum already specifies their small-field presentation through
  `FiniteStagePairCategory.pbcScalarSystem`; its `pbcScalarAssociator` is the
  localization of that same normalized ordinary balancing, not a fresh choice.
* `IntegralPullbackComparisonRealization`: `integralComparisonScalarAssociator`
  and `integralPullbackComparisonRealization`; the former's formula is the
  ordinary tensor associator conjugated by the same completion maps.
* `FiniteFreeCompletedScalarComparison`: `completedScalarChainComparison`,
  `completedScalarComparison`, and `finiteFreeCompletedScalarComparison`,
  including both chain coordinates, descent equation and equal-field unit.
* `FdCoefficientComparison`: `FdRationalStageComparison`,
  `FdOrdinaryScalarTransport`, its `complex` and `completion`,
  `fdCoefficientTransportFactors`, and the normalization formulas of
  `FdCoefficientComparison`. We use the definition's interface, never its
  existence or downstream pair-equivalence fields as a hypothesis.
* `IntegralStratifiedPerfectCharacterization`:
  `AlgebraicGeometry.Scheme.integralDetailedTransport`,
  `integralDetailedCoefficientComparison`, and
  `integralStratifiedPerfectDetailed` (identification of the two integral full
  subcategories on allowed schemes).
* `GeneralAlgebraicallyClosedCoefficients`: `stageSystem`, `unitor`, and
  `integralTransition`, the existing presentation of framework scalar extension.
* `WeilConjectures.CategoryTheory.StageSystem.Functor`:
  `CategoryTheory.StageSystem.Morphism`, its finite functors, beta and cocycle.

All recorded proof-dependency modules are imported as proof-only imports unless
already reached through public statement imports. The sole postponed theorem's
docstring gives all eight steps of the DAG argument, including the countable
product exactness check needed for quotient-scalar descent.

Edge cases checked before drafting and again on the final formulas: empty T;
zero object and zero morphisms; base coefficient field; identity coefficient
inclusions; `E=L`, `L=M`, all fields equal, and every four-field repetition;
integer shifts 0, 1 and -1; scheme universe different from coefficient-closure
and global-datum universes. No properness, finite-type, nonempty-scheme,
strict-extension, finite Tor-amplitude, or Karoubi-completion assumption appears.

Searches for an existing statement:

* msearch LeanFinder: `Inverse finite free completed scalar comparison between
  rational coefficient categories preserves shifts and satisfies unit cocycle and
  four field associativity`. Eight hits about derived single functors, Dold--Kan,
  free categories and localization shifts; none gives the specified comparison.
* msearch LeanSearch: `canonical finite free completed coefficient extension
  inverse comparison coherent scalar functors`. Eight hits; ordinary
  `ModuleCat.extendScalars_assoc`, its pseudofunctor and generic abstract
  completion do not compare these integral/derived/rational categories.
* msearch Loogle: `NatTrans.CommShift, NatIso, Functor.associator`.
  Zero hits (remote service does not know NatTrans.CommShift).
* msearch grep in Mathlib/CategoryTheory:
  `completion.*[Ii]nverse|[Ii]nverse.*[Cc]ompletion|CommShift`.
  Twenty-five hits on shifts and generic localization; no specific theorem.
* rg in `lean/WeilConjectures` and `lean/Sheaf`:
  `completion-inverse-scalar-coherence|[Cc]ompletionInverse|[Cc]ompletion.inverse|Fd.*Scalar|fd.*Scalar`.
  Found the existing Fd ordinary-transport definitions and unrelated point-fibre
  and internal-Hom comparisons; no theorem of this statement.
* Exact node-id search in upstream WeilConjectures sources: no hit.

No statement correction, disputed statement, missing notion, or dependency repair
was needed. Helpers package clauses of this node's own conclusion, as explicitly
permitted for owning-node helpers. Only this node's `lean` field changes.

## Second reading by Q10

Self-review in this dispatcher workflow (no other agents are authorized): reopened
the source node, the final module and each recorded dependency interface. Checked
all hypotheses and clauses against the correspondence above. The initial draft
expanded concrete scalar-system formulas repeatedly and exceeded elaboration
limits. The final predicate writes the identical cocycle and two four-field
contractions in the existing abstract stage-system language, then specializes to
the actual two systems; it changes no mathematical scope. Auxiliary structure
code generation is disabled to avoid unnecessary generated lemmas. Compiler time
limits and universes are unchanged.

Checked specifically the direction: `integral.comparison` and `family.β` point
PBC-to-framework, while the node's `j` is their inverse. `scalar_lift` uses `β.hom`
and the integral HOM, and the explicit coherence predicate uses `β.inv` in all
three places. Checked the four-field expressions have the same source and target,
and that each contains all three successive inverse comparisons. Unit normalization
is imposed at every field, and the cocycle allows reflexive inclusions. Checked
that the stage hypothesis contains no scalar family or cocycle (unlike assuming
`FdCoefficientComparison` itself, which would be circular). All definitions have
real data, the only theorem has `sorry`, the full proof is in its docstring, and
all declaration docstrings carry the owning blueprint id.

Validation: prescribed scompile.py passed both the sandbox and library module
checks without errors or warnings (41.5 s and 43.9 s respectively); the delivery
dry run recompiles the final file and performs the server preflight.
