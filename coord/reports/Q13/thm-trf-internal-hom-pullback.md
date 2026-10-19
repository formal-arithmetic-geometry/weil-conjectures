## Worker report

The item is stated in `Sheaf.Paper.InternalHomPullback`, with primary declaration
`WeilConjectures.internalHomPullback`. Nothing is proved: the two theorem proofs
in that module are `sorry`. Definitions contain actual data. The canonical arrow
`finiteHomPullback` is the closed transpose of the inverse canonical tensor
comparison followed by derived pullback of evaluation. In particular its
invertibility concerns that arrow, not an unspecified isomorphism.

Hypothesis and clause correspondence:

- Finite coefficients A=O_E/varpi_E^n: `l`, `[Fact l.Prime]`, `E`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` and
  `finiteCoefficientRing l E (n + 1)`. The natural-number index is shifted by
  one, so all and only the positive exponents occur. These are the recorded
  coefficient quotient rings, not an alternative coefficient model.
- Global finite-field convention and ell different from its characteristic:
  `D : FiniteFieldDatum` and `hl : l ≠ D.p`. Schemes have the recorded
  `Over (Spec (.of D.k))` structures. `finiteHomPrimeInvertible` transports the
  unit `finiteFieldDatumPrimeUnit D l hl` to each residue field by the actual
  morphism from its spectrum; no extra invertibility assumption is imposed by
  the theorem. The auxiliary arrow works with arbitrary invertibility data.
- A morphism of finite-type schemes: `X Y : Scheme`, `g : Y ⟶ X`, and
  `LocallyOfFiniteType` plus `QuasiCompact` on both structure morphisms. There
  is no separatedness hypothesis on either scheme, no flatness on g, and no
  assumption that g itself is etale, proper or an immersion.
- M belongs to the ambient D(X,A) and is site-perfect:
  `M : proEtaleDerivedCategory X ...` and
  `IsFiniteCoefficientSitePerfect l E X n M` in
  `FiniteHomPullbackProperties`. This is the dependency's actual covering and
  bounded finite-free-retract predicate, with locally variable bounds and ranks.
- N is in D^b_ctf(X,A): the hypothesis
  `finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X N` is the recorded
  bounded constructibility and finite Tor amplitude intersection.
- The displayed canonical comparison is an isomorphism:
  `IsIso (finiteHomPullback l E n g M N)` with precisely the source and target
  derived internal Homs and pullbacks in the display. Its definition uses
  `finiteIntrinsicTranspose`, `finiteIntrinsicEvaluation` and the inverse of
  `canonicalFinitePullbackTensor` on `(H(M,N),M)`.
- Naturality in both variables: `finiteHomPullback_naturality` gives the square
  for every `a : M' ⟶ M` and `b : N ⟶ N'`, including noninvertible a, hence in
  particular for the stipulated perfect and finite-Tor constructible inputs.
  This auxiliary naturality identity does not require perfectness; the primary theorem keeps
  the stated hypotheses for invertibility and compatibility.
- Compatibility with all integer shifts of N:
  `FiniteHomPullbackRightShift` is the component square for the two composite
  functors' specified `commShiftIso`. The Hom shift is the uniquely
  representative-normalized unsigned reindexing, and pullback uses its
  termwise-derived shift. The source and target do not choose arbitrary shifts.
- Compatibility with all integer shifts of M:
  `FiniteHomPullbackLeftShift` uses the signed representative-normalized
  `RingedHomUniverses.sourceShift` and the inverse pullback shift on the
  contravariant argument. Its square includes the shift -s on the result.
- Distinguished triangles in N: for a distinguished `T` whose three vertices
  satisfy `finiteTorConstructible`, `FiniteHomPullbackTriangle` asserts that
  the two image triangles are distinguished and that there is a
  `TriangleMorphism` between them with all three components equal to the same
  canonical comparisons. Its third commutation equation includes the
  connecting arrow and the shift of the first component.

The item gains the already recorded
`lem-weil-pbc-ringed-internal-hom-exact-restriction` in `stmt_deps`, since its
specified shift interfaces are now needed to read the statement. It was already
in `proof_deps`. No natural-language statement, proof plan or blueprint unit is
changed. No new DAG node is introduced.

Dependency declarations used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions` and its coefficient conventions, with
  the original `FiniteFieldDatum` and Padic extension objects reexported.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`.
- `Sheaf.Paper.SitePerfectComplex`: `IsFiniteCoefficientSitePerfect`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteCoefficientRing`,
  `finiteDerivedPullback`, `finiteIntrinsicDerivedInternalHom`,
  `finiteIntrinsicTranspose`, `finiteIntrinsicEvaluation`.
- `Sheaf.Paper.FinitePullbackTensorComparison`:
  `canonicalFinitePullbackTensor` with its existing K-flat and ordinary-unit
  normalization.
- `Sheaf.Paper.DirectImagesConstructible`: `finiteFieldDatumPrimeUnit`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `RingedHomUniverses.hom`, `homCommShift`, `sourceShift`,
  `hom_isTriangulated`; the repaired dependency reexports its earlier interface.
- Size and scheme-morphism convention nodes define no object; universes and
  `Scheme`, `Over`, `LocallyOfFiniteType`, `QuasiCompact` are explicit.

Proof imports retain the recorded closed-symmetric-monoidal structure,
coherent monoidal pullback, site-perfect duality, duality maps, normalized
coefficient tensor-Hom model, exact derived pullback, and Hom complex modules.
The Mathlib leaf uses `tensorLeftAdjunction`, `tensorRightAdjunction`,
`Adjunction.leftAdjoint_preservesColimits`, and
`Adjunction.rightAdjoint_preservesLimits`; their full source signatures were
read. Every postponed theorem has the source and a stepwise proof in its docstring.

Edge cases checked before drafting: n=0 is exponent one, not the zero quotient;
there is no excluded positive exponent. The zero complex and empty scheme are
allowed, as are locally varying perfect bounds and an unbounded ambient M.
All integer shifts, including zero and negative shifts, occur. The naturality
square permits noninvertible first-variable maps. Identity pullback uses the
existing canonical tensor comparison. Triangles include zero vertices and their
connecting map. Neither first-variable perfection of the pulled-back complex
nor constructibility of the comparison objects is added as a hypothesis.
The small pro-etale site remains at object universe u+1 and morphism universe u.

Searches made (2026-10-18):

- `msearch.py ... leanfinder`: “Derived pullback commutes with internal Hom from
  a site perfect complex naturally with shifts and distinguished triangles”.
  Eight hits on ordinary module pullback; none states the derived comparison
  and its compatibility clauses.
- `msearch.py ... loogle`: “expComparison, CommShift”. No hits; the service did
  not recognize expComparison. Focused source grep supplied the generic
  `expComparison` interface for cartesian closed functors instead.
- `msearch.py ... grep`: “expComparison|[Hh]om.*[Pp]ullback”, restricted to
  CategoryTheory/Monoidal. Twelve hits: generic closed-functor comparison,
  pullbackHom, and cartesian-over constraints; no matching coefficient-site theorem.
- `msearch.py ... leansearch`: “Derived inverse image internal Hom perfect first
  argument canonical comparison isomorphism”. Eight generic resolution and
  homology-comparison results, none matching this statement.
- `rg` of the upstream WeilConjectures sources, the project's Sheaf sources, and
  `dag/lean_names_upstream.json`: no existing names `finiteHomPullback`,
  `finiteHomPrimeInvertible`, or `RingedHomUniverses`.
- Read upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Pullback`, theorem
  `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`.
  It states only a `Nonempty` iso for a dualizable etale complex; it does not
  specify the canonical arrow, naturality, shifts or triangle compatibility,
  and uses a different site presentation. It cannot be an existing attachment.
- Read the current main-20261015 item and its unit statement, and each statement
  dependency's statement, record, full used signatures and docstrings. Read all
  proof-dependency statements and their recorded declarations. The current item
  retains the finite-type and finite-Tor constructible hypotheses even though
  the ambient unit theorem has greater generality.

No STATEMENT-DISPUTED flag is needed. Compilation and delivery validation results
are recorded below after the final checks.

## Dependency modules

`lem-weil-pbc-ringed-internal-hom-exact-restriction` is repaired under §1(B) by
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`. Its recorded signed
calculus fixes the site object and morphism universes to the same value; the
actual small pro-etale site has different universes. The new module publicly
imports the entire old interface, preserving its tensor adjunction, restriction,
exactness and signed calculus. It adds the same target exactness and signed
shift comparisons at independent site, coefficient and derived universes.

`RightFormula` and `LeftFormula` specify every Hom-product projection of the
ordinary shift isomorphisms: unsigned target reindexing and source reindexing
with factor (-1)^(s*k). `RightNormalization` and `LeftNormalization` identify the
derived maps through the fixed ordinary-to-derived comparison; they quantify
over an arbitrary derived object M, every representing complex L, and every
representative isomorphism QL≅M. This last clause prevents an unconstrained choice
on objects outside the literal image of Q. The existence theorems assert unique
normalized families, from which the two definitions select real data. Thus the
repair does not choose from a bare existence of unspecified isomorphisms.
`hom_isTriangulated` supplies the connecting-arrow-compatible exactness for the
same normalized target shift. Its cone proof and both reindexing proofs are in
their docstrings. Only the dependency node's `lean` record changes, with `lean.note`
explaining this universe and normalization repair. Its previous declarations
remain publicly available through the public import. The new record lists only
the declarations actually made by its own file, as preflight requires.

## Validation

The prescribed `scompile.py Q13 thm-trf-internal-hom-pullback` invocation compiled
both delivered files separately in dependency order, including the wrapper's
sandbox and library confirmation passes. Exit code 0; no errors or warnings.
The final sandbox passes took 3.5 s and 36.9 s, and the final library confirmation
passes took 18.6 s and 19.5 s, within the unchanged 60-second per-file limit.
The node records' signatures match the final source verbatim. No unbound implicit
variables or universes and no lines longer than 100 characters remain.

The first delivery dry run compiled both files cleanly, then rejected imported
old declaration names in the dependency record. The record was repaired to list
only declarations actually made by the new module; its public import still
reexports the full previous interface. No Lean source or theorem changed.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
