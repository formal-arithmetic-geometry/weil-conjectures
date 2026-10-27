## Worker report

The delivery states `CategoryTheory.finite_formal_quotient_pullback` and supplies a
supported-arrow helpers in the item module, importing the unchanged global
formal-quotient definition. The theorem
proof is `sorry`. All definitions have explicit data. No statement correction or
new DAG node is proposed.

Hypotheses and conclusions, in the order of the node:

- The algebraically closed field Ω is `[Field Ω] [IsAlgClosed Ω]`.
- X is the existing `BasedCategory` over `Spec Ω`; `hX` is precisely
  `IsDeligneMumfordModuliStack X`. `hnoeth` asks for a locally Noetherian étale
  surjective scheme atlas, with all the actual algebraic-space base changes and
  their projections retained. It does not assume finite type over Ω.
- The geometric object x is a map from the represented `Spec Ω` groupoid.
- H has `[Group H] [Finite H]`. R has its Ω-algebra, local, Noetherian and
  maximal-ideal-adic completeness instances. `res` identifies its residue field
  with Ω as an Ω-algebra. No domain or reducedness condition occurs.
- `α : H →* (R ≃ₐ[Ω] R)` is the Ω-linear ring action; `hcont` uses the actual
  maximal-ideal-adic topology. `ρ` is the associated left scheme action; `hρ` specifies its maps as inverse
  pullback. The result uses the same specification for `ρC` and `σ`. These scheme
  actions are redundant encodings fixed by inverse pullback, not independent actions.
- f is the given affine chart. `hx` identifies its restriction through the
  specified residue map `formalResidueMap res` with x.
- θ and `hchart` express the specified formal quotient presentation. They retain
  coherent action arrows, all supported test maps, étale local lifts of objects,
  the arrow description, and uniqueness of labels on nonempty tests. Formal
  support on Spec R is the zero locus of its maximal ideal. Completion in X is
  the existing `ModuliCompletionAt x`. On a Noetherian atlas its finitely generated
  ideal means support is equivalent to locally killing an ideal power, so this
  is the functor-of-points description of the compatible infinitesimal system,
  not a completion of rings of isomorphism classes.
- Y is a stack (`hY`) and p is representable finite (`hp`), tested on every scheme
  by the existing `IsRepresentableFiniteModuliMap`. No normality, dense open,
  normalization, reducedness, dominance, or surjectivity is assumed for Y or p.
- The result supplies C, its commutative ring and Ω-algebra structure and
  structural Ω-algebra map φ from R. `Module.Finite` is explicitly interpreted
  using φ's R-module structure. The next conjunct is `IsAdicComplete m C` for
  that same module. This says precisely that the canonical map to the compatible
  quotients C/m^nC is bijective (the node's completion definition).
- g and η give the actual square with Spec C. The specified
  `moduliTwoFiberLift ... η.symm` is an equivalence, so C represents the required
  2-pullback over Spec R; this is not an arbitrary finite algebra.
- σ is a group homomorphism to Ω-algebra automorphisms of C. Its equation with φ
  is the semilinearity/extension requirement. Continuity is for the topology
  associated to `m.map φ.toRingHom`, namely mC, with no choice of topology.
- ψ and the final quotient predicate identify the completion of Y with the
  supported C-quotient. Its target predicate is `ModuliCompletionAt x (t.comp p)`,
  i.e. completion along the inverse-image gerbe, rather than one selected point
  of Y. `FormalQuotientPullbackArrows` says that after applying p the ψ-arrow is
  exactly the θ-arrow conjugated by η, on every object over every test scheme. The equality δ transports the source
  along the semilinearity equality; equality proofs add no chosen mathematical
  datum. This fixes the descent arrows and the equivalence over the original
  formal quotient, including its reduction-compatible 2-comparison.

Dependency declarations used:

- `Field`, `IsAlgClosed` from Mathlib field and algebraic-closure definitions;
  `IsNoetherianRing`, `Module.Finite`, `IsAdicComplete`, and `Ideal.adicTopology`
  are the recorded ring notions and their standard adic topology.
- `AlgebraicGeometry.Spec`, `Spec.map` and `IsFinite` are the recorded affine
  spectrum and finite-scheme definitions.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory`-based
  stack vocabulary, `IsModuliStack`, `IsDeligneMumfordModuliStack`,
  `moduliTwoFiberProduct`, `HasSpaceBaseChange`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, `ModuliTwoIso`, and `discreteModuli`.
- `Sheaf.AlgebraicGeometry.FormalModuliQuotient`: `moduliChartMap` and
  `ModuliCompletionAt`, reused by the item and its supported-arrow helpers.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `IsRepresentableFiniteModuliMap` (added its already landed definition node).
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `moduliTwoFiberLift`
  (added its already landed owning node; no normalization condition is used).
- `Sheaf.AlgebraicGeometry.AffineActionQuotientStack`: `affineActionScheme`
  (added its already landed owning node; no finite-type or fppf-quotient
  hypothesis from the separate quotient construction is used).
- Proof imports: `WeilConjectures.RingTheory.FiniteModuleComplete` and
  `Sheaf.AlgebraicGeometry.ActionGroupoidQuotientCriterion`, as recorded by the
  proof dependency nodes. Their full signatures and proof docstrings were read.

Edge cases checked: H trivial; nonfaithful actions; nontrivial stabilizers;
characteristic dividing |H|; R=Ω and m=0; nonreduced R and C; the empty finite
pullback (C the zero ring); finite non-surjective p; and disconnected test schemes
with locally constant group labels. Empty tests impose no uniqueness of group
labels, because the predicate requires `Nonempty T.left` there. Arbitrary étale
covering sieves retain nontrivial torsors. C is not required to be local; mC,
not its radical or an independently selected maximal ideal, defines its topology.
All scheme/ring tests use the same u, and stack object and morphism universes
remain independently polymorphic.

Searches actually run through msearch.py:

- LeanFinder: “Finite representable pullback of formal quotient stack by finite
  group induces semilinear action on complete finite algebra”: eight unrelated
  FDRep/Galois/tannakian hits, no match.
- Loogle: `"QuotientStack"`: zero hits.
- Mathlib grep in AlgebraicGeometry:
  `residualGerbe|FormalCompletion|quotientStack`: zero hits.
- LeanSearch: “formal completion quotient stack finite group torsor”: eight
  abstract Galois/group-quotient hits, no stack-completion theorem.
- rg of WeilConjectures and Sheaf for formal quotient, residual gerbe,
  FormalCompletion, formalCompletion, and the item id: scheme/module completion
  tools and the existing FormalModuliQuotient definition, no theorem matching
  the item. Read the latter rather than duplicating its completion predicate.
- DAG searches found the existing formal-quotient, finite scheme-test, affine
  quotient, action-groupoid criterion and chart-normalization nodes. Blueprint
  search for “formal quotient” supplied no equivalent imported statement.

Sources read: spaces-groupoids.tex lemma-quotient-stack-2-cartesian (04M9) and
lemma-quotient-stack-isom (044W); algebra.tex lemma-completion-tensor (00MA),
part (3), and lemma-completion-finite-extension (07N9). The latter is not needed
for the general finite module completeness clause. The theorem docstring records
all six accepted proof steps, including the canonical arrow comparison.

## Repair of H13

The returned head 408894de749b replaced the landed NI record for
`def-sfb-formal-moduli-quotient`. That record is now excluded from the delivery:
its module `Sheaf.AlgebraicGeometry.FormalModuliQuotient`, primary declaration
`CategoryTheory.IsFormalModuliQuotient`, and all six registered declarations
remain byte-identical to side-live. The item imports that original module directly.

`SupportedModuliAtlasAction` and `IsSupportedFormalModuliQuotient` have moved,
with their mathematical definitions unchanged, into
`FiniteFormalQuotientPullback.lean`. Both appear in the item's `lean.declarations`
and their source/blueprint docstrings now identify this item. The separate
`SupportedFormalModuliQuotient.lean` file is removed from the packet. The supported
interface restricts the original coherent action to test maps supported on the
formal completion; its local objects/arrows and nonempty-test label uniqueness
are checked against `IsFormalModuliQuotient`. No theorem hypothesis, conclusion,
proof step, or statement-dependency list changed in this repair.

The independent return approved the item statement clause by clause, its edge
cases, explicit universes, theorem-only `sorry`, and six-step proof docstring.
This repair addresses its single ownership/record-preservation defect.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
