## Worker report

Stage 2, O1, 2026-10-22. The existing Q71 PASS in ledger line 24987 is the stage-1
split, not a Lean delivery: the live node has neither lean nor reviewed_lean. The prior
worker's stale-assignment conclusion was mistaken. This delivery retains the mathematical
statement and the fourteen-step proof verbatim. It adds two definition nodes, imports the
already landed definitions below, and records eleven statement-only theorems in
Sheaf.AlgebraicGeometry.JetDiagramHilbertControl. Every proof is sorry; definitions have
real data and no postponed existence is used to choose arbitrary data.

Sources read: the full current node, all eight original statement dependency records and
their actual source declarations/docstrings; the four additional landed definition nodes
and modules; ILO VIII printed pp.93--94 (PDF pp.99--100), Remarks 2.3.11 and 2.3.13;
Bierstone--Milman--Temkin, https://arxiv.org/html/0905.3580v1, sections 6.1 and 6.5.
The latter explicitly gives the nonclosed-point transcendence correction, degree-lex
exponents, minimal vertices, complementary counts and iterated summation for free variables.
BM alg-geom/9508005 was inspected, but that arXiv version contains only Chapter I;
the detailed §3/§9 arguments used here are the owning node's fully written proof.

Clause and hypothesis correspondence (all declarations here have namespace DiagonalJets):

| Node clause/hypothesis | Lean rendering |
| --- | --- |
| Field k of characteristic zero | `[Field k] [CharZero k]` in the geometric/jet results. The purely formal assertions use any field L, as in the formal-ideal paragraph. |
| Finitely generated k-algebra A | `[CommRing A] [Algebra k A] [Algebra.FiniteType k A]` in `finite_and_fibre_dimension`. No nontriviality assumption on A. |
| J is the multiplication kernel; P^n has the first-factor A action | `DiagonalJets.principalParts`: quotient by `(KaehlerDifferential.ideal k A)^(n+1)`, with Mathlib's left tensor-product algebra structure. The existing ideal is literally the multiplication kernel. |
| P^n finite for each n | The first conjunct `∀ n, Module.Finite A (principalParts k A n)`. |
| Every x in Spec A, residue field and fibre | The second conjunct quantifies `x : Spec (CommRingCat.of A)`. `affineEvaluation x` goes through `Scheme.ΓSpecIso` and `Scheme.Γevaluation`. `fibreDimension` is the finrank of κ(x) ⊗_A P^n, canonically the same fibre as P^n ⊗_A κ(x). |
| t_x, local length h_x, inclusive Λ; equality for all n | RHS is the landed `HilbertSamuel.function (Spec.map (ofHom (algebraMap k A))) x n`. Its actual definition is the iterated `summation` by `Cardinal.toNat (Algebra.trdeg k κ(x))` of `localFunction`, whose values are `Module.length` converted to Nat. Finite type ensures these conversions are literal. |
| Étale chart in smooth ambient U | `c : MvPolynomial (Fin d) k →+* Γ(U, ⊤)` and `[Etale (U.toSpecΓ ≫ Spec.map (ofHom c))]`. This is exactly the morphism to affine d-space; smoothness over k follows, so no additional smoothness assumption is imposed. U need not be affine. |
| Coherent ideal defining closed X in U | `I : U.IdealSheafData` and `Scheme.Modules.IsQuasiCoherentFiniteType I.toModules`. U is locally Noetherian from the chart, so this recorded predicate is coherence here. X is the actual `I.subscheme`, with its canonical closed immersion `I.subschemeι`. |
| x in X; actual Taylor ideal | `a : I.subscheme`; ambient point `I.subschemeι a`. `existsUnique_taylor` asserts the unique stalk homomorphism satisfying the landed `isTaylorMap` with actual stalk residue and germ coordinates. `taylor_dimension` quantifies any such uniquely characterized T and takes the landed `taylorIdeal (stalkIdeal I x) T`. No coefficient-field section or arbitrary map replaces Taylor expansion. |
| Taylor truncation has the same fibre dimension | `taylor_dimension` equates the finrank of `MonomialDiagram.truncation` to the same intrinsic `HilbertSamuel.function`, using the actual induced structure morphism of X. `finite_and_fibre_dimension` identifies this number with the jet fibre on affine charts. |
| First exponents in degree-lex order | `MonomialDiagram.IsFirstExponent`: nonzero coefficient at α and zero coefficients at all smaller `Finsupp.DegLex` exponents. `initialDiagram` takes exactly those arising from elements of K. Zero cannot contribute an exponent. |
| Finite minimal vertices and generated orthants | `initial_diagram_vertices` asserts additive upward closure and a finite `Fin s` family satisfying the existing `IsOrderedVertexFamily` and equality with `generated α`. The existing predicate enumerates exactly the coordinatewise minimal elements, so the vertex set is unique. |
| G_i in K with first exponents the ordered vertices | Binders `K`, `α`, `hα`, `G`, `hG` in `unique_supported_division`; nonzero is built into `IsFirstExponent`. Leading coefficients are not assumed normalized. |
| Regions E_i, translated Δ_i and complement E_0 | Existing `MonomialDiagram.quotientSupport α i` is precisely Δ_i: no earlier vertex divides α_i+β. It is the translation of E_i; the remainder predicate is `β ∉ initialDiagram K`. |
| Unique F = sum Q_i G_i + R with supports | `unique_supported_division` uses `∃! qr` for the pair of the entire quotient family and remainder, with this equality and the existing `HilbertCoefficient.supported` for each support condition. |
| Dimension equals complementary monomial count | `formal_quotient_dimension`, for each K,n: the quotient is finite over L and its finrank is `hilbertCount (initialDiagram K) n`. The count is the ncard of exponents outside D with total degree ≤n. |
| Taylor diagrams locally take finitely many values on U | `taylor_diagrams_locally_finite`: for every x in U there is an open V containing x with finite image of the actual Taylor-diagram function on V. T is the family of uniquely characterized stalk Taylor maps; existence was asserted separately. Points outside X are included, with unit Taylor ideal. |
| No infinite lexicographically decreasing sequence of additive-diagram counting functions | `no_infinite_hilbert_descent`: negated existence of D indexed by Nat, each additively upward closed, and strict `HilbertSamuel.lt` from term i+1 to term i. |
| Formation of P^n commutes with étale localization | `etale_principal_parts`: an actual B-algebra isomorphism B ⊗_A P^n(A/k) ≃ P^n(B/k), pinned on every pure generator b ⊗ [a ⊗ a′]. Its formula identifies the canonical comparison, rather than an arbitrary isomorphism. |
| Taylor expansion and dimensions commute with étale localization | `etale_taylor_compatibility` takes an étale ring chart c, an étale map f, compatible evaluations ev/ev′ and field map ι. Its three conclusions are coefficientwise commutation of the uniquely specified Taylor maps, equality of initial diagrams for I and I.map f, and equality of all truncation dimensions. Ordinary open localizations are included. On any affine neighbourhood these are the restrictions of the stalk maps above; uniqueness gives the same maps. Together with the preceding canonical jet comparison these give compatibility of the dimension identities and residue-field fibres. |
| Adjoining r free variables | `free_variables`: extension along the actual `MvPowerSeries.rename (Fin.castAdd r)` gives the product diagram `freeExtension`, and its complementary counts are `(HilbertSamuel.summation^[r])` of the original counts. Variables are ordered first by the old Fin d coordinates and then the new r coordinates. |

Dependency declarations reused, with source modules read:

- Mathlib.RingTheory.Length: `Module.length`.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Γevaluation`, `Scheme.Hom.residueFieldMap`; Mathlib.AlgebraicGeometry.Scheme:
  `Scheme.ΓSpecIso`.
- Mathlib.RingTheory.AlgebraicIndependent.Basic: `Algebra.trdeg`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: `AlgebraicGeometry.Etale`;
  Morphisms.Smooth: `Smooth`; Morphisms.ClosedImmersion: `IsClosedImmersion`.
  The latter two notions are provided by the actual étale chart and canonical ideal subscheme.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  `Scheme.Modules.IsQuasiCoherentFiniteType` (the recorded interface, not a private copy).
- Mathlib.RingTheory.MvPowerSeries.Basic: `MvPowerSeries`, `coeff`, `X`, `map`;
  Rename: `rename`. Mathlib.RingTheory.Kaehler.Basic: `KaehlerDifferential.ideal`.
- Sheaf.AlgebraicGeometry.HilbertSamuelInvariant: `summation`, `localFunction`,
  `function`, `lt`; Sheaf.AlgebraicGeometry.MarkedIdealOrder: `stalkIdeal`.
- Sheaf.RingTheory.SupportedHomogeneousDivision: `IsOrderedVertexFamily`,
  `generated`, `quotientSupport`.
- Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum: `isTaylorMap`,
  `taylorIdeal`, `supported`. No substitute definitions are introduced.
- Proof-plan imports are the recorded Mathlib modules for finite type/Noetherianity,
  Dickson, length, smooth base change and differentials, and the three recorded upstream
  modules FlatUnramifiedFormallyEtale, SeparableExtensionFractionFieldOfSmoothAlgebra,
  SeparablyGeneratedDifferentialsDimension. The two genuinely unstated proof nodes
  (smooth-rational-point-completion and implicit-taylor-coordinate-calculus) are not
  imported: no Lean declaration is recorded for them, and their objects are not needed
  to type this statement. They remain the existing proof tasks, not new helpers.

Edge cases checked mathematically before writing:

- A=0: the jet quotient is zero and Spec A is empty; finiteness still holds and the
  pointwise formula has no points. No `[Nontrivial A]` excludes it.
- n=0: P^0=A, the fibre is one-dimensional at each existing point, and the local
  length and any number of inclusive sums have value 1 at zero.
- Generic point of A=k[t]: local ring k(t) has h(n)=1 and transcendence degree 1;
  the formula is n+1. This verifies that nonclosed points retain a free Taylor variable.
- K=0: empty diagram and vertex list; division gives Q empty, R=F, and the count
  is the entire degree ball. K=(1): diagram all exponents, unique vertex 0;
  quotient and remainder are zero, and the unique quotient is F/G for its unit G.
- d=0: the series ring is L and its only field ideals are zero/unit; the only exponent
  is zero. Empty Fin sets are allowed throughout. r=0 is identity renaming and zero
  iterations. For a zero diagram in one variable, adjoining one variable takes n+1
  to (n+1)(n+2)/2, as inclusive summation requires.
- Empty U or X is permitted. The local finite-values statement includes points off X.
  No rational-point, reducedness, algebraic-closedness or affineness assumption was added.
- Diagram order is kept separate from the order of Hilbert functions; the DCC theorem
  uses counting functions and its own diagonal finite-degree-ball argument.

Searches actually run:

1. msearch.py leanfinder: `principal parts jet modules Taylor ideals formal power series
   initial exponents Hilbert Samuel dimension`: eight univariate power-series hits,
   no diagonal jet/initial diagram definition.
2. msearch.py loogle: `MvPowerSeries, Algebra.TensorProduct.lmul`: unknown identifier
   Algebra.TensorProduct.lmul, no hits. The exact multiplication map was subsequently
   found by reading Mathlib's KaehlerDifferential.ideal (lmul′).
3. msearch.py leansearch: `Diagonal principal parts quotient and formal initial exponent
   diagrams with cumulative Hilbert functions`: eight Hilbert-polynomial, local-cohomology,
   ideal-quotient and univariate division hits; no exact statement or missing definitions.
4. msearch.py grep `principalParts|initialDiagram|initialExponent|TaylorMap|taylorIdeal`,
   subdirectory RingTheory: zero hits.
5. Direct rg across Mathlib/RingTheory, project WeilConjectures and Sheaf for
   Taylor/taylor, PrincipalParts/principalParts, initialDiagram/InitialDiagram,
   HilbertSamuel/hilbertSamuel, formalDivision, diagonalIdeal. Found and reused all
   existing definitions listed above. Curve principal parts refer to meromorphic
   quotients and do not define diagonal jets. Direct rg for the item id in
   lean/WeilConjectures had no matches.
6. tools/blueprint_refs.py search `principal parts` and `initial exponent`: zero
   imported blueprint nodes for both. Ancestor query returned lem-trf-local-term-locality.
   DAG definition search found no node defining either new notion. The existing
   regular-coefficient and supported-division nodes are used for all overlapping helpers.

No STATEMENT-DISPUTED flag or source-based correction is needed.

## New nodes

- def-trf-diagonal-jets / Sheaf.RingTheory.DiagonalJets: the literal diagonal
  quotient, its fibre dimension, and affine evaluation into the existing residue field.
- def-trf-formal-initial-diagram / Sheaf.RingTheory.FormalInitialDiagram: first
  exponent predicate, actual initial diagram, complementary count, actual truncated
  quotient and extension by free coordinates. Ordered vertices and division supports
  remain the existing definitions. Neither node asserts a theorem.

Both have all §5 fields, real definitions, actual searches, the current item's chapter
and unit, and the ancestor/via chain computed from the blueprint. The item gains only
these and the four landed definition dependencies, together with its lean record.

## Second reading by O1

I reread the original statement and all eleven signatures after the first clean compile.
The mathematical statement and proof remain byte-for-byte unchanged. The clauses above
account for each of its hypotheses and conclusions. I specifically checked the tensor
factor giving the A-action, κ(x) as the actual scheme residue field, the transcendence
summation at a nonclosed point, strict degree-lex rather than coordinatewise first
exponents, exact quotient supports including s=0, and uniqueness of the whole division
pair. I checked that the chart hypothesis is a morphism to Spec of the polynomial ring,
not the too-strong assumption that the whole ambient is affine or its stalk is finitely
presented over that polynomial ring. Coherent ideals are interpreted via the recorded
finite-type interface on this locally Noetherian smooth ambient. The jet comparison is
pinned on generators; Taylor maps use the existing specification and have a separate
unique-existence assertion. This prevents replacing canonical objects by arbitrary data.
The free-coordinate extension uses Fin(d+r), avoiding the non-total default LT relation
on a Sum index. The definition module initially re-exported an unused regular-coefficient
module; that import was removed, and the item imports its used definitions directly.
A metadata extraction accidentally saw the words `theorem with` inside a proof docstring;
that spurious declaration was removed from lean.declarations. All real declarations
are recorded. All Lean lines are at most 100 characters and autoImplicit is false.
The worker performed this second reading in-thread; no separate agent was started.

## Validation

The prescribed scompile.py compiled all three modules separately in dependency order.
The initial full pass was clean (6.6 s, 7.0 s and 9.7 s reported library times); the final
pass after import cleanup was also clean (6.6 s, 2.8 s and 7.6 s library times). No proof was attempted. The only admitted
proofs are the eleven named theorem clauses of the owning DAG node, with its complete
natural-language proof steps in their docstrings. Dry run and delivery results follow.

The new nodes preserve the search wrappers’ captured output verbatim in mathlib_searches.

The first dry run passed server preflight and per-file compilation at commit 733848fed1a.
A final dry run validates the metadata-only cleanup (verbatim captured search outputs and
§5's newtargets-dag provenance value); no Lean source changed after the clean final compile.
