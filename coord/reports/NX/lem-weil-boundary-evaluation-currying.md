## Worker report

The module `Sheaf.SixFunctors.BoundaryEvaluationCurrying` states
`AlgebraicGeometry.Etale.boundaryEvaluationCurrying` with one `sorry` proof.
The other five declarations are fully defined conclusion predicates or the evaluation
counit in the source category; none chooses unspecified data. The natural-language
DAG statement is unchanged. No statement is disputed. This repair addresses H7 on
immutable head a8964ab64854: the base proof dependencies
are restored, and the new definition node records existing canonical definitions
in the unchanged published alpha-normalization module.

Clause-by-clause rendering:

- The finite-field datum is `D : WeilConjectures.FiniteFieldDatum`; `l`, `Fact l.Prime`
  and `_hl : l ≠ D.p` render the coefficient prime. `E`, `Field`, `Algebra (Padic l)`
  and `FiniteDimensional` give exactly the finite extension. `n : ℕ` indexes level
  `n+1`, including every level at least one. `boundaryCoefficient l E n` is the
  canonical `ULift` of `Padic.coefficientExtensionRing l E (n+1)`. This is the quotient
  by the recorded chosen uniformizer, with its existing finite-ring instance.
- `T`, `Z`, `aT : T ⟶ Spec (.of D.k)` and `i : Z ⟶ T` give the schemes over k;
  the structure morphism of Z is the composite `i ≫ aT`. `IsSeparated aT`,
  `LocallyOfFiniteType aT`, `QuasiCompact aT`, and `IsClosedImmersion i` give the
  stated geometry. Closed immersions preserve this separated finite-type setting
  for Z, so no extra assumption on Z or on i's base is introduced.
- The etale category is `Etale.DerivedCategoryModule`, namely the ordinary unbounded
  derived category of sheaves valued in `ModuleCat.{u+1}`. For the general pro-etale
  currying clause it is `DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat A))`.
  This is the fixed-scalar presentation of modules over the constant ring sheaf, as
  supplied by the recorded `finiteCoefficientRealization` and its equivalence theorem;
  it is neither a condensed-module category nor a completed derived category.
  Site objects and morphisms keep their existing independent size convention; the
  coefficient lift matches the existing module-sheaf universe and imposes no universe
  equality. `BoundarySiteCurrying` is asserted for both Z and T, on both sites.
- `finiteTorConstructibleEtale` renders D^b_ctf, using the recorded conjunction of
  bounded constructibility and existence of one finite Tor interval uniform over
  all degree-zero sheaves. `DerivedCategory.isBoundedConstructible` renders D^b_c
  in the projection hypothesis. These predicates are not replaced by arbitrary classes
  in the main theorem.
- The actual `boundaryData` fixes `s` to `L(upperStar (ModuleCat A) i)`, F to derived
  direct image, and G to its selected ambient right adjoint. Thus F=Ri_*=Ri_! for
  the closed immersion. Its `adj.counit` is the stated mu. This uses the recorded
  ambient exceptional-adjunction existence, not a constructible adjoint. `boundaryOmegaT`
  is `dualizingComplex (ModuleCat A) aT`, and omega_Z is exactly `G.obj omega_T`.
  `boundaryData.H` and `.J` are the existing derived-Hom bifunctors.
- `_hs`, `hG`, `hD`, `_hDZ` are the four preservation hypotheses for s,G,D_T,D_Z
  on precisely the finite-Tor constructible predicates. `hPF` asks invertibility
  of the actual `boundaryProjection` for every bounded constructible B and every
  finite-Tor constructible M. The inline restriction
  `fun B hB M hM ↦ hPF B hB.1 M hM` supplies the bounded-constructible part of
  finite-Tor constructibility, without using `boundaryPFOnFiniteTor`; it does not
  replace hPF. The
  public alpha-normalization import supplies the existing definitions recorded by
  def-weil-boundary-data; no theorem conclusion is used in the statement.
- `TensorHomCurrying` asserts the isomorphism from `H(B,H(C,H))` to `H(B tensor C,H)`.
  Its first three equations are naturality in B, C and H (contravariantly in B,C).
  Its fourth equation identifies the isomorphism under arbitrary represented-Hom
  tests with iterated uncurrying and the actual associator. Thus the isomorphism
  is evaluation-normalized, not an arbitrary natural iso with those endpoints.
  Its next conjunct is the formula for right-order uncurrying by identity tensor
  evaluation, using the given parameterized tensor-Hom adjunction. This is the
  stated natural Hom bijection; its counit is evaluation. Its final conjunct
  states involutivity. The two site instantiations use the canonical derived signed
  symmetry, descended from the Koszul swap, and the canonical derived associator.
  The variables in this clause range over the full unbounded category, with no
  constructibility or Tor restrictions.
- `BoundaryData.q`, reused directly in `Conclusions`, is the exceptional transpose
  of the inverse canonical projection, conjugated by the two actual symmetries,
  followed by identity tensor `adj.counit`. The first conjunct of `Conclusions`
  gives exactly its naturality square for arbitrary arrows f,g between admissible
  objects, with tensoring of both maps explicit. The two inverse components are
  obtained from hPF and hG, not supplied as new maps.
- `BoundaryData.evaluation` is the tensor-Hom counit after the specified signed
  swap, so it is ev_K in DK tensor K order. `BoundaryData.alpha` is precisely the
  transpose of the specified `BoundaryData.r`, which is sigma, q, then G of the
  opposite-order evaluation. These are existing definitions, not new choices.
- In `OppositeCurrying`, P is `d.L.obj ((d.H.obj (op L)).obj W)` and U is
  `d.G.obj L`. The map `d.G.map ((d.aD.adj DL).homEquiv L W (d.evaluation W L))`
  is G(delta_L): transpose of ev_L in left-tensor-DL coordinates, equivalently the
  opposite-order transpose of ev_L sigma_(L,DL). Its composite with `d.alpha W DL`
  is exactly c_L. The left side tensors that map with identity_P and follows it by
  `sourceEvaluation`, the actual ev_P with codomain G(W). The right side is
  sigma_(U,P), then q_(DL,L), then G(ev_L), exactly b_L sigma_(U,P).
  The hPF components needed here are justified by hD twice and hG; in particular
  DDL is admitted, and neither delta nor alpha is assumed invertible.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the recorded quotient construction.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, `DerivedCategory` and its existing cohomology interface.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, and the fixed-coefficient realization equivalence.
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible` (pro-etale constructibility convention).
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`.
- Mathlib `AlgebraicGeometry.Morphisms.ClosedImmersion`, `.FiniteType`, `.Proper`:
  `IsClosedImmersion`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and `.LowerShriekLeftAdjoint`:
  `rightDerivedLowerShriekOfCompactification`,
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` (which publicly imports
  `DerivedInternalHomOfUniverses` and the ordinary etale derived Hom) and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom`:
  `derivedHom`, `derivedTensorHomAdjunction₂`, `derivedTensorHomAdjunction`.
- `Sheaf.Paper.DualityPairing`: `Etale.AmbientDualityPairing` and
  `AmbientDualityPairing.bidualityMap`, with their evaluation/transpose normalization.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap` and its adjunction formula.
- `Sheaf.SixFunctors.BoundaryAlphaNormalization`: `boundaryData`, `boundaryCoefficient`,
  `boundaryCoefficientFinite`, `boundaryG`, `boundaryOmegaT`, `boundaryDT`, `boundaryDZ`,
  `boundaryProjection`; `CategoryTheory.BoundaryData.q`, `.r`, `.alpha`, `.evaluation`
  and their full definitions. The item's only added statement dependency is the new
  definition node `def-weil-boundary-data`. The published module supplies these
  definitions through the new definition
  node, independently of its alpha-isomorphism conclusion. All names
  retain their existing definitions; there is no private copy or arbitrary map.
- Proof-only imports are the recorded ringed derived closed symmetric monoidal
  theorem, Mathlib Yoneda full faithfulness, and derived inverse-image tensor comparison.

Sources read: current blueprint `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower/cor-weil-boundary-duality-discharge.proof.md`, second paragraph;
local Stacks `sites-cohomology.tex`, `lemma-internal-hom` and
`lemma-section-RHom-over-U` (08J9,08JA). The node's five proof steps are carried
in the theorem docstring; no proof has been attempted in this stage.

Edge cases checked before writing: n=0 in the Lean index is level one, not the
excluded level zero; every positive level occurs. Zero complexes, zero arrows,
empty schemes, disconnected schemes and the identity closed immersion are admitted.
No nonempty hypothesis or quasi-projectivity hypothesis is added. Internal currying
accepts arbitrary unbounded objects. The final identity continues to make sense
without alpha or delta invertible, and no such assumption appears. Naturalities
use arbitrary pairs of admissible endpoints, including the equal-endpoint cases.

Searches for existing statements (2026-10-24):

- msearch LeanFinder: `Derived tensor Hom adjunction and natural exceptional evaluation
  opposite currying identity for closed immersion`: eight results, including ordinary
  scheme module restriction adjunctions, LightCondensed.ihomPoints_symm_comp and
  ExponentiableMorphism evaluation identities; no exact statement.
- msearch Loogle: `"curry", "ev"`: twelve results, chiefly MonoidalClosed curry/uncurry
  counit identities and Filter.currying; no exceptional evaluation identity.
- msearch grep: `exceptional.*(tensor|evaluation)|opposite.*curr`: no Mathlib hits.
- msearch LeanSearch: `Ringed site derived tensor Hom currying exceptional adjunction
  evaluation naturality`: eight results, including ihom.ev_naturality_assoc and
  MonoidalClosed.internalHomAdjunction₂; no exact statement.
- Direct rg over the project and upstream for the node id and boundary/opposite currying:
  no existing declaration of this node. Searches for boundary evaluation, q and alpha
  located BoundaryAlphaNormalization and BoundaryQTransport. The former supplied the
  exact canonical constructions, reused in their published module; the latter concerns site transport of
  the pairings, not this identity. Mathlib InternalCurrying.ihomCurryIso supplies an
  abstract currying iso, not the exceptional identity or this complete site assertion.
  No second tensor/Hom or exceptional-map construction is written.

Validation uses only scompile.py and the prescribed delivery wrapper. The only
new Lean file is BoundaryEvaluationCurrying; the existing definitions receive the
wrapper's server-side declaration checks. The published alpha-normalization module
and node are unchanged. The theorem signature is copied verbatim into the item
record; its sole postponed proof is sorry. No local/global build is run.

## Second reading by NX

A separate self-audit pass reopened the DAG statement, all six declarations and the
canonical map definitions. No second agent was started, as the dispatch brief forbids
it; the independent delivery reading belongs to the maintainer. This section records
the worker's second pass and does not claim an independent worker review.

The audit matched all hypotheses and clauses as itemized above. It checked the order
of both tensor factors, all three contravariant/covariant currying squares, the
right-order Hom bijection, the exceptional counit's direction, and the codomain G(W).
It found that mere natural existence of a currying iso would forget its canonical
normalization, so the arbitrary-test iterated-uncurrying equation was added. It also
restricted the first conclusion to the two sites of Z and T, rather than all schemes.
Both corrections were made before the final successful compile. The opposite-currying
identity uses the canonical alpha and the canonical biduality transpose; its first
projection is at (GL,DL), its second at (GDDL,DL), exactly as required. Preservation
of s and D_Z remains explicitly present even though that final formal calculation
only needs preservation of G and D_T. No mismatch or disputed clause remains.


## New nodes

`def-weil-boundary-data` records existing definitions in
`Sheaf.SixFunctors.BoundaryAlphaNormalization`, with `existing: true` and no file.
Its main declaration is `AlgebraicGeometry.Etale.boundaryData`; its declarations
list includes the abstract BoundaryData and its canonical q/r/alpha/evaluation,
projection, independent Hom chain, coefficient ring, G, omega_T and D_T/D_Z.
The source is the current blueprint cor-weil-boundary-duality-discharge proof,
second paragraph, where adjunction identifies the two maps with restriction of
evaluation. The maps are precisely the published canonical constructions; the
new node provides their definition record without depending on the theorem that
alpha is invertible. No definition or theorem is copied or relocated.

Recorded searches: LeanFinder `Canonical boundary exceptional evaluation q alpha
projection data` and LeanSearch `Canonical exceptional adjunction projection
transpose evaluation boundary data` returned unrelated general constructions;
Mathlib grep `BoundaryData|boundaryAlphaQ` found no match. Project rg located the
exact definitions only in BoundaryAlphaNormalization; upstream rg and DAG /
blueprint searches found no other boundary-data definition node. These searches
are preserved in mathlib_searches. Finding the existing implementation is the
reason for existing:true, rather than a new implementation.

## Returned H7 repair

The item's proof_deps is exactly the six-entry base list specified by the return:
lem-sf-ringed-derived-closed-symmetric-monoidal, lem-galois-yoneda-fully-faithful,
def-kun-projection-formula-map, lem-kun-inverse-image-monoidal,
thm-amb-etale-exceptional-adjoint, lem-weil-duality-pairing. The natural-language
statement and proof are unchanged, and no statement_change is introduced.
The new definition remains in stmt_deps. Its lean record points to the existing
published alpha-normalization module and lists definitions rather than the
alpha-isomorphism theorem. BoundaryData.lean and the alpha-normalization node
and module repair are omitted from this packet. The item publicly imports the
existing module to use those definitions; it retains the inline restriction
`fun B hB M hM ↦ hPF B hB.1 M hM`.

The retained item body matches the accepted previous statement. Clause and edge
case checks from the independent return still apply: n=0 represents level one,
Z may be empty, L may be zero and i may be the identity; both sites and their
universes are retained. There is no alpha/delta invertibility hypothesis and no
new universe equality. Comparison with the current live source confirms the
recorded definitions are still in BoundaryAlphaNormalization. Only the item
module, item record, new existing-definition node and this report are delivered.

Validation for this H7 repair: scompile.py compiled the sole delivered module
cleanly (sandbox 9.7 s; library 8.9 s). All Lean lines are at most 100 characters.
The delivery dry run also checks every declaration listed by the existing-definition
node on the server.
