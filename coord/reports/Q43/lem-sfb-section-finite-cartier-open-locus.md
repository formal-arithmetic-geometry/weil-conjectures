## Worker report

The module `Sheaf.AlgebraicGeometry.SectionFiniteCartierOpenLocus` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_finiteCartierZeroLocusOpen`, with
`sorry` as its only theorem proof. Two transparent predicate definitions bundle
the conditions and their universal property; they introduce no new geometric
notion or chosen data. Both helpers belong to this node and are listed in
`lean.declarations`. The node's statement and dependencies are unchanged.

Hypothesis and clause correspondence, read against the complete node:

- Any scheme T and family Y: `{Y T : Scheme.{u}} (p : Y ⟶ T)`; the explicitly
  declared universe `u` is arbitrary. Neither scheme is assumed nonempty.
- Proper, flat and finitely presented: `[IsProper p] [Flat p]
  [LocallyOfFinitePresentation p]`. Properness already gives quasi-compactness
  and quasi-separatedness, so the last hypothesis is exactly finite presentation
  in this context, not a weakening to a non-quasi-compact family.
- Open U smooth of relative dimension one: `(U : Y.Opens)` and
  `[SmoothOfRelativeDimension 1 (U.ι ≫ p)]`. The canonical open subscheme is
  `U.toScheme` and its inclusion is `U.ι`.
- Invertible M and N and O-linear morphism: `(M N : Y.Modules)
  [M.IsInvertible] [N.IsInvertible] (a : M ⟶ N)`. These are the recorded
  Scheme.Modules invertibility and module morphism notions, not substitutes.
- Zero scheme cut out locally by coefficient b: `a.zeroLocus`, the dependency's
  existing `Scheme.Modules.Hom.zeroLocus`. Its docstring and
  `Hom.ideal_zeroLocus` identify the ideal with `(b)` on trivializing affine
  opens. No alternate definition of the zero scheme is introduced.
- Nonnegative integer d: `(d : ℕ)`, including zero.
- Unique open subscheme: `∃! V : T.Opens, ...`. Opens encode canonical open
  subschemes, so uniqueness is literal equality of opens rather than equality
  of unrelated presentations of an open immersion.
- Every morphism h:T'→T: `IsFiniteCartierZeroLocusOpen` quantifies
  `∀ (T' : Scheme.{u}) (h : T' ⟶ T)`. No flatness, finite-type, reducedness,
  or Noetherian restriction is put on either the test map or base.
- Factoring through V: `∃ j : T' ⟶ V.toScheme, j ≫ V.ι = h`.
- Pulled-back zero scheme: the ideal
  `a.zeroLocus.comap (pullback.fst p h)` on `Limits.pullback p h`.
  Its `subschemeι` is the closed immersion of that zero scheme. Ideal extension
  gives the scheme-theoretic pullback for every h, not only flat h; the existing
  `Hom.comap_zeroLocus` explicitly states equality with the zero ideal of the
  pulled-back module morphism for arbitrary maps.
- Support in U after pullback: `∀ y, y ∈ J.support → y ∈ U`, evaluated at
  the extended ideal and `pullback.fst p h ⁻¹ᵁ U`. A closed subscheme factors
  through an open exactly when its underlying support lies in that open.
- Relative effective Cartier on Y_T'/T': `J.IsRelativeEffectiveCartier
  (pullback.snd p h)`, the existing predicate of an invertible ideal and
  flatness of its closed subscheme over the base.
- Finite locally free of rank d: `(J.subschemeι ≫ pullback.snd p h).
  IsFiniteLocallyFreeOfDegree d`. This is the exact recorded declaration of
  def-pc-finite-locally-free: finite, flat, locally finitely presented, with
  all fibre algebra dimensions d. Stacks 02KB (lemma-finite-flat), read at
  morphisms.tex:12375 onwards, identifies this with finite local freeness of
  the direct image structure algebra; its local module rank is its fibre
  dimension. Thus it gives precisely the stated local O^⊕d condition,
  including over nonreduced bases.
- Arbitrary base change: the second conjunct says for each h that `h ⁻¹ᵁ V`
  satisfies `IsFiniteCartierZeroLocusOpen` for the extended zero ideal, pulled
  family, and inverse image open. This asserts the full universal property
  of the base-changed locus, not just a pointwise inclusion.
- Field-valued criterion: the third conjunct quantifies `(K : Type u)
  [Field K] (h : Spec (.of K) ⟶ T)` and identifies factorization with support
  containment, `J.IsInvertible`, `IsFinite` of its structure map, and
  `.finrankΓ = d`. The first is effective Cartier, and the last is
  dim_K Γ(Z_h,O), with the canonical K-algebra structure induced by h.
  Finiteness makes this the usual length, including residue-field degrees.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and the canonical `Scheme.Opens` subschemes.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smooth implication).
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`:
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`.
- `WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` and `finrankΓ`.

The statement imports above are public, including those supplied transitively
by their recorded dependency module. The existing modules of proof dependencies
are imported privately: FibreCartierLocal, FinitePushforwardLocallyFree,
FiniteLocallyFreeDegreeLocallyConstant, AffinePushforwardBaseChange,
ZariskisMainTheorem, Dimension.Constructions, and FaithfullyFlat.Algebra.
RelativeEffectiveCartier also supplies the Cartier criterion and relative
Cartier pullback. The theorem docstring contains all seven proof steps of the
node and names their inputs. No proof is attempted.

Sources opened: divisors.tex:4191-4212 (062Y, lemma-fibre-Cartier (3));
pic.tex:407-425 (0B9D, lemma-divisors-on-curves, the implication (2)→(3)
without a Noetherian assumption); more-morphisms.tex:12544 onwards (02LS,
lemma-characterize-finite); morphisms.tex:12345-12400 (finite locally free
and lemma-finite-flat, 02KB). The item is an agent-formulated consequence,
not a literal statement of any single tag, as its source record explains.

Edge cases checked before writing:

- Empty base or empty ambient scheme: all pointwise clauses are vacuous and
  the universal property still includes the empty test scheme.
- U empty: the condition forces the zero scheme empty; positive degree is
  possible only over an empty test base. This gives the empty locus for d>0.
- d=0: the zero fibre algebra has dimension zero and the finite scheme is
  empty; no `Nonempty`, `0 < d`, or positive-rank hypothesis occurs.
- a an isomorphism: its zero scheme is empty, so the locus is all T for d=0
  and empty for d>0. a=0 on a nonempty smooth curve fibre fails the Cartier
  condition; no automatic zero-map case is accidentally accepted.
- Nonreduced base and nonflat h: no excluded cases; the extended ideal uses
  ordinary ideal comap and the field reflection is part of the source proof.
- Length over a non-algebraically-closed field counts residue degrees,
  since `finrankΓ` is vector-space dimension, not cardinality of the support.

Searches actually run using `msearch.py Q43 lem-sfb-section-finite-cartier-open-locus`:

- LeanFinder: "For a morphism of invertible sheaves on a proper flat finitely
  presented family the finite locally free Cartier zero scheme locus of fixed
  degree supported in a smooth open curve is represented by an open subscheme".
  Eight hits concerned zero loci and ideal-sheaf gluing, not this theorem.
- LeanFinder: "The zero scheme of a map of line bundles in a proper flat family
  is a finite locally free relative effective Cartier divisor on an open locus
  of the base". Eight hits concerned Scheme.zeroLocus, Hom.ker, IdealSheafData.map,
  affine limits, ideal-sheaf local constructions; none was this locus theorem.
- Loogle: `"Cartier", "locus"`: zero hits.
- LeanSearch: "The locus on the base where the zero scheme of a line bundle
  section is a finite flat relative effective Cartier divisor of fixed degree
  is open": eight hits, all topological RingedSpace/Scheme.zeroLocus results.
- Mathlib grep via msearch: `Cartier.*[Ll]ocus|[Ll]ocus.*Cartier|zeroLocus.*[Oo]pen|
  finiteCartier`, restricted to AlgebraicGeometry: eighteen hits concerning
  topological zero loci and gluing; none states the item.
- Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` using the item id and
  the same concept patterns: no item declaration; hits were unrelated zero
  loci, Cartier support loci, and an unrelated finiteCartierArrow. Also read
  the upstream name index around zeroLocus; no declaration of this open locus.

No new nodes, dependency repairs, statement correction or unresolved dispute.
Compilation through the prescribed scompile.py succeeded in both sandbox and
library module modes without diagnostics. No local or global build was run.

## Second reading by Q43

Written by the maintainer's independent second reader (cc review service,
2026-10-24) in place of the worker's own self-review, which was not an
independent reading (delivery-errors H11). The Lean module and node records
are unchanged.

Node statement, item by item, against the delivered Lean:

| Node | Lean | Verdict |
|---|---|---|
| T any scheme, Y → T | `{Y T : Scheme.{u}} (p : Y ⟶ T)` | exact; universe arbitrary, no nonemptiness |
| p proper, flat, finitely presented | `[IsProper p] [Flat p] [LocallyOfFinitePresentation p]` | exact (proper ⇒ qcqs, so lfp = fp) |
| U ⊆ Y open, smooth of rel. dim 1 over T | `(U : Y.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ p)]` | exact; only U, not Y |
| M, N invertible, a : M → N | `(M N : Y.Modules) [M.IsInvertible] [N.IsInvertible] (a : M ⟶ N)` | exact (recorded def-sc-invertible-module) |
| Z(a) locally (b) | `a.zeroLocus` = recorded `Hom.zeroLocus` (`ideal_zeroLocus` gives span{b} on trivializations) | exact |
| d ≥ 0 | `(d : ℕ)` | exact, d = 0 allowed |
| unique open T_d ⊆ T | `∃! V : T.Opens` | exact; uniqueness as opens |
| ∀ h : T' → T, factors through T_d ⟺ … | `IsFiniteCartierZeroLocusOpen`: `∀ T' h, (∃ j, j ≫ V.ι = h) ↔ …` | exact, no restriction on h |
| Z(a) ×_T T' | `a.zeroLocus.comap (pullback.fst p h)`; Mathlib `comap` = ker of `pullback.fst f I.subschemeι`, subscheme ≅ fibre product for every f (`comapIso`) | exact, nonflat h included |
| contained in U_{T'} | `∀ y, y ∈ J.support → y ∈ pullback.fst p h ⁻¹ᵁ U` (Mathlib `support` = vanishing set) | exact |
| relative effective Cartier on Y_{T'}/T' | `J.IsRelativeEffectiveCartier (pullback.snd p h)` = invertible ideal ∧ flat subscheme over T' | exact (recorded def-pc-relative-effective-cartier) |
| finite locally free of rank d | `(J.subschemeι ≫ pullback.snd p h).IsFiniteLocallyFreeOfDegree d` (finite, flat, lfp, all fibre degrees d) | exact (recorded def-pc-finite-locally-free; = locally O^d by 02KB) |
| commutes with arbitrary base change | second conjunct: h⁻¹ᵁ V has the same universal property for the pulled-back family, ideal and open | exact |
| field-valued points: fibre zero scheme Cartier, length d, in U | third conjunct, `K : Type u` field: support ⊆ U ∧ `IsInvertible` ∧ `IsFinite` ∧ `finrankΓ = d` | exact; `IsFinite` is automatic for a Cartier divisor of a proper scheme lying in a smooth curve, flatness automatic over K; `finrankΓ` is dim_K Γ (counts residue degrees) |

Helpers `FiniteCartierZeroSchemeCondition` and `IsFiniteCartierZeroLocusOpen`
are transparent conjunctions of recorded predicates, with real bodies and
source/blueprint docstrings, listed in `lean.declarations`; no hollow
definition and no new notion.

Edge cases: empty T or Y (vacuous, universal property still quantified over
the empty test scheme); U empty (forces Z empty: locus = locus of empty zero
scheme for d = 0, empty for d > 0 unless T' empty); d = 0 (degree-0 finite
locally free = empty); a isomorphism (Z empty, T_0 = T); a = 0 on a nonempty
fibre (not invertible, excluded); nonreduced base, nonflat h (comap is the
scheme-theoretic pullback); non-algebraically-closed K (length = dimension).

Checks: lean.statement verbatim equal to the file's signature; node
statement, source, stmt_deps, proof unchanged against live (only `lean`
added); no stmt_dep added or dropped; imports are the recorded dependency
modules (public) and proof-dependency modules (private); the theorem docstring
carries the node's seven proof steps; only `sorry`; no pro-étale substitute.
Searches: Mathlib `IdealSheaf/` and the project's `WeilConjectures/AlgebraicGeometry`
for Cartier/zero-locus open loci: none states this locus.
