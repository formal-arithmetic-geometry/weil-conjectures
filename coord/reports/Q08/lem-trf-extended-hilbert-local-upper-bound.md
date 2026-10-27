## Worker report

This is a stage-2 statement delivery for lem-trf-extended-hilbert-local-upper-bound,
not a resplit of Q25's accepted stage-1 work. The stage-2 handoff in
coord/brief-stage2.md section 0 expressly permits this. The live item has no lean
record and appears in coord/queue.tsv at stage 2. No repair note exists. The
previous stage-1 stale-assignment refusal therefore does not apply.

The module Sheaf.AlgebraicGeometry.ExtendedHilbertLocalUpperBound states the node
in three theorems. Every theorem has exactly `by sorry`. The helper
`closedPrincipalParts` constructs the specified principal-parts module by the
existing `DiagonalJets.principalParts` and Mathlib's `ModuleCat.restrictScalars`;
its data contains no postponed proof or choice. It belongs to the principal-parts
clause of this node, so it is recorded among this node's declarations.

Hypothesis and clause correspondence:

- Characteristic-zero field: `{k : Type u} [Field k] [CharZero k]`.
- Smooth affine finite-type k-scheme U: `[IsAffine U]`, the `U.Over (Spec (.of k))`
  structure, and `Smooth`, `LocallyOfFiniteType`, `QuasiCompact` of its structure
  morphism. The presentation clause only needs its explicitly given affine open.
- Etale coordinates t_1,...,t_d: `c : MvPolynomial (Fin d) k →+* Γ(U, ⊤)` and
  `Etale (U.toSpecΓ ≫ Spec.map (.ofHom c))`. The equality `hc` says c is over the
  stipulated k-structure; it does not introduce a second unrelated field action.
- Closed subscheme X: `I : U.IdealSheafData`, with X=`I.subscheme` and closed
  immersion `I.subschemeι`. Mathlib provides its closed-immersion instance.
  This parametrizes every closed subscheme of affine U, with no reducedness or
  additional coherence assumption. Its ideal of global equations is
  `RingHom.ker I.subschemeι.appTop.hom`; on U0 it is `I.idealOfOpens U₀`.
- Centered Taylor map at every point: `T y` and `hT` use the existing
  `isTaylorMap c (U.Γevaluation y).hom`. This pins scalar values, residues and
  t_j ↦ t_j(y)+T_j, hence the canonical completed diagonal expansion on the
  etale chart. It is not an arbitrary uncharacterized map.
- K_y is `taylorIdeal (RingHom.ker I.subschemeι.appTop.hom) (T y)`.
- H_y(q) is named by H, with `hH` identifying it exactly with `Module.finrank`
  of the existing `MonomialDiagram.truncation`. That quotient is literally
  kappa(y)[[T]]/(K_y + (T)^(q+1)). This avoids replacing field dimension by the
  length-valued helper `extendedHilbert`; it introduces no second definition.
- H_y=0 outside X: the first conclusion of
  `extendedHilbert_principal_parts_realization` uses `y ∉ Set.range I.subschemeι`.
- a in X and affine neighbourhood U0: `a : I.subscheme`, `IsAffineOpen U₀`, and
  `ha : I.subschemeι a ∈ U₀`.
- Finite set of local functions: `ℋ : Finset (ℕ → ℕ)` with `hℋ` equating its
  underlying set to `H '' (U₀ : Set U)`. Choosing a Finset represents precisely
  a finite set; no decidable equality is assumed on sequences.
- Finite modules realizing each degree: `M : ℕ → ModuleCat.{v} Γ(U, U₀)`,
  `hM`, and `hdim`. The fibre is the actual tensor extension via the canonical
  `U.evaluation U₀ y hy`, through Mathlib `ModuleCat.extendScalars`.
- V open, containing a, inside U0: `∃ V : U.Opens`, center membership, `V ≤ U₀`.
- All degree bounds: the second membership equivalence for V says exactly
  `y ∈ U₀ ∧ ∀ q : ℕ, H y q ≤ H (I.subschemeι a) q`.
- Lexicographic consequence: `HilbertSamuel.le (H y) (H (I.subschemeι a))`, using
  the recorded non-strict lexicographic relation with least differing degree.
- Every finite module has a finite presentation:
  `extendedHilbert_presentation_loci` concludes `Module.FinitePresentation`,
  then supplies m,n,B,pi with `Function.Surjective π` and
  `Function.Exact B.mulVecLin π`. It applies to every finite module realizing a
  degree, not just the canonical principal-parts modules.
- Matrix-minor open sublevels: for every integer b the same theorem asserts
  openness and equality with the locus `0 ≤ b ∧ ∃ rows cols, ev(det(...)) ≠ 0`,
  where rows and columns are embeddings of `Fin (n - b.toNat)`. This is the
  union of their nonvanishing basic opens on U0. There are finitely many
  embeddings, so the matrices and union are finite. Using embeddings instead
  of increasing subsets merely repeats determinants up to sign.
- Witness degree for every bad h: Q with `H_a (Q h) < h (Q h)` whenever h is in
  the finite value set and fails pointwise comparison. Q on other values is
  immaterial and does not add constraints on them.
- V is precisely the finite intersection of those witness sublevels: the first
  membership equivalence for V. When no h is bad its universal test is empty,
  and the equivalence forces V=U0. No infinite intersection constructs V.
- Finitely many additional bounds: the `∀ E b` conclusion allows any finite
  degrees with b(q)≥H_a(q). Every y in V satisfies them simultaneously; hence
  intersecting these open sublevels leaves that same neighbourhood.
- Degrees distinguishing every pair: the final finite E and its pairwise
  distinguishing property include every pair of distinct h,h' in ℋ.
- Local validity of the hypotheses: the last theorem produces an affine U0
  around each a, finite image H(U0), and finite/finitely-presented modules at
  every degree with the required fibre equality at every ambient point.
- These are specifically the principal-parts modules of X∩U0:
  `closedPrincipalParts k Γ(U,U₀) c₀ (I.idealOfOpens U₀) q`, where c₀ is c on
  constants followed by section restriction. Its definition sets A=R/I and
  forms `(A ⊗[k] A)/J^(q+1)`, then restricts scalars along R→A. Thus A is the
  coordinate ring of the restricted closed subscheme, rather than global O(X)
  before restriction. This is the meaning made explicit in accepted proof step 6.
- No closed-point hypothesis occurs on a or y; `Fin d` retains all coordinates.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth (and the
  SmoothOfRelativeDimension/Etale signatures of the recorded dependency).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType; the
  associated QuasiCompact class supplies the other finite-type clause.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion,
  instantiated by the closed subscheme inclusion.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField, residue,
  evaluation, Γevaluation and Hom.residueFieldMap.
- Mathlib.RingTheory.MvPowerSeries.Basic: MvPowerSeries, with `Fin d` variables.
- Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum:
  AlgebraicGeometry.HilbertCoefficient.isTaylorMap and taylorIdeal.
- Sheaf.RingTheory.FormalInitialDiagram: MonomialDiagram.truncation.
- Sheaf.AlgebraicGeometry.HilbertSamuelInvariant: HilbertSamuel.le (and lt).
- Sheaf.RingTheory.DiagonalJets: DiagonalJets.principalParts.
- Mathlib.Algebra.Module.FinitePresentation: Module.FinitePresentation,
  Module.finitePresentation_of_finite, and its finite-free presentation interface.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module:
  Scheme.IdealSheafData.idealOfOpens, defined as the kernel on sections.
- Mathlib.Algebra.Category.ModuleCat.ChangeOfRings: ModuleCat.extendScalars and
  ModuleCat.restrictScalars.

The five already-landed definition nodes for Taylor data, truncated quotients,
lexicographic order, principal parts and finite presentation are added to
stmt_deps because their recorded declarations occur in the statement. No new
node, dependency repair, statement change, proof change or resplitting is made.
The current proof dependencies' available modules are imported privately;
JetDiagramHilbertControl supplies the geometric comparison/finiteness input.

Edge cases checked before writing and during the second reading: d=0 leaves the
coefficient field as the series ring; q=0 is the residue quotient; zero ideal
X=U gives the ordinary free-coordinate truncated dimensions; unit ideal gives
empty X and H=0, with no possible center; nonreduced X such as V(t²) remains
allowed; generic and closed points of A¹ use the same one Taylor variable.
For matrices, negative b gives false, b≥n uses the size-zero determinant 1,
positive unavailable minors yield an empty set, and zero-row or zero-column
presentations work. If ℋ has no bad value, V=U0; with a center ℋ cannot be empty.
A singleton ℋ needs no distinguishing degree; zero modules and q=0 remain valid.

Searches actually performed (2026-10-23):

- msearch.py leanfinder: "Taylor Hilbert functions finite local values principal
  parts fibre dimensions simultaneous pointwise upper bound on an open
  neighbourhood". Eight hits, on analytic Taylor series and CPolynomialAt;
  none states this algebraic result.
- msearch.py loogle: "UpperSemicontinuous, Module.FinitePresentation". Zero hits.
- msearch.py grep: "Taylor|taylor|HilbertSamuel", RingTheory. Seventeen hits,
  on univariate polynomial Taylor transforms/Henselian/resultant arguments;
  none is this statement.
- msearch.py leansearch: "Finite module over noetherian ring fibre dimension
  upper semicontinuity finite presentation minors open neighbourhood". Eight
  hits, including Module.finitePresentation_of_finite (used), local-freeness
  ranks and unrelated finite fibres; no simultaneous Taylor bound.
- rg over lean/WeilConjectures and lean/Sheaf: Taylor/taylor, extendedHilbert,
  extended_hilbert, jetDiagram, diagonalJets/diagonalJet; direct item-id search
  in WeilConjectures; simultaneous-Hilbert/Hilbert-upper-bound/local_upper_bound.
  Found the reused definitions and JetDiagramHilbertControl, but no declaration
  stating the item. RegularHilbertCoefficientData has a downstream datum with a
  bound field, not this theorem, so is neither reused as proof nor imported.
- Read the current blueprint locality node and proof via literature/blueprint/latest;
  read BM 1997 online, printed pp.275--277 (Remarks 9.1, Lemma 9.3), and Stacks
  algebra.tex at lemma-Noetherian-permanence and
  lemma-Noetherian-finite-type-is-finite-presentation. BM source:
  https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf

No STATEMENT-DISPUTED or node fault. The source discusses lexicographic
semicontinuity; the accepted DAG's finite-witness argument gives its stated
pointwise refinement. Every clause is retained.

Validation: scompile.py compiled the delivered module against the live server
library in both sandbox mode (3.5 s) and library mode (3.1 s), exit 0, no errors
or unexpected warnings. Three named theorem proofs remain sorry as required.

## Second reading by Q08

The dispatcher explicitly prohibits starting another agent and provides no lead.
This is a separate self-review pass, not a claim that an independent agent read it.
I reopened the live node, its six proof steps and all statements in this file,
then checked each clause against the correspondence above. In particular I
checked both V equivalences, strict witness inequality, arbitrary additional
integer sublevels, canonical evaluation for scalar extension, and the actual
R/I principal-parts construction. The zero/oversized minor cases use truncated
natural subtraction only after b≥0, so b<0 cannot incorrectly select a minor.
All d coordinates remain at nonclosed points. The definition names and
signatures were read in their source modules; no data is chosen from a sorry.
No mismatch was found; no source statement or accepted split needed correction.
The maintainer's independent delivery review remains required.
