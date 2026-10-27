## Worker report

Q66 states `CategoryTheory.SpectralSequence.noetherian_quadrant_abutment` in
`Sheaf.Algebra.Homology.NoetherianQuadrantAbutment`. This is stage 2: its only
proof is `sorry`. No definitions, auxiliary theorems, dependency modules or new
nodes are introduced. The node changes only in `lean`; its statement, dependencies
and stage-1 proof are unchanged.

The prior BLOCKED diagnosis conflated the existing Q73 stage-1 PASS with a
stage-2 landing. The live node has `reviewed` for that split, but no `lean` or
`reviewed_lean` record, and there is no repair note. The Q73 report lists a DAG
split and citations, and no Lean module. This packet supplies the missing stage-2
statement, without re-splitting or modifying that accepted work.

Source read: Stacks `perfect.tex`, `lemma-coherent-internal-hom` (Tag 0D0C),
lines 2682–2711, especially the two Ext spectral sequences and their final
finite-generation inference. The already accepted node expands precisely that
inference into support, finiteness, stabilization, finite filtration induction
and low-degree vanishing. All five proof steps are transcribed into the theorem's
docstring, including the reuse of the Noetherian submodule leaf. This result does
not assert existence of an abutment filtration: it assumes one as the node does.

Hypothesis and conclusion correspondence:

- A commutative Noetherian ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`. Its module universe is the separately bound `v`, with no
  extra universe equality. The quadrant offsets are `(a b : ℤ)`.
- `E : E₂CohomologicalSpectralSequence (ModuleCat.{v} A)` is the recorded
  `CategoryTheory.SpectralSequence`, specialized by Mathlib's abbreviation to
  pages starting at 2, indexed by `ℤ × ℤ`, with shape
  `ComplexShape.up' (s, 1-s)`. Thus it includes the square-zero differentials of
  bidegree `(s,1-s)` and the specified homology-to-next-page isomorphisms `E.iso`.
  Morphisms in ModuleCat, including those isomorphisms, are A-linear.
- `hfinite : ∀ p q : ℤ, Module.Finite A ((E.page 2).X (p,q))` gives finite
  generation of every second-page term.
- `hsupport : ∀ p q : ℤ, p<a ∨ q<b → IsZero ((E.page 2).X (p,q))` gives exactly
  the second-page vanishing outside the shifted quadrant. `IsZero` is the zero
  module condition on these categorical module objects.
- The first conjunction of the conclusion quantifies over every integer page
  `s` with `hs : 2 ≤ s` and every integer `(p,q)`, asserting both the same
  support vanishing and `Module.Finite A ((E.page s hs).X (p,q))`.
- The next conjunction quantifies over precisely the same pages and positions.
  Its condition `max (p-a) (q-b+1) < s` is the node's strict stabilization bound.
  It asserts separately that `.d (p-s,q+s-1) (p,q)` and
  `.d (p,q) (p+s,q-s+1)` equal zero: these are the incoming and outgoing
  differentials with the node's signs and indices.
- `∃ EInf : ℤ → ℤ → ModuleCat.{v} A` supplies the eventual stable terms, and
  `∀ p q, Module.Finite A (EInf p q)` asserts their finite generation. For each
  position, the existential family `e` identifies every page satisfying the
  exact stabilization bound with that stable term. It is not an unrelated
  family of abstract isomorphisms: the displayed equality
  `iCycles ≫ e_s.hom = homologyπ ≫ (E.iso s (s+1) ...).hom ≫ e_(s+1).hom`
  forces compatibility with the specified page identifications. When both
  differentials vanish, the canonical cycles inclusion and homology projection
  are isomorphisms; the equality says exactly that successive identifications
  are obtained by composing those canonical maps with E.iso. No equality of
  page objects is falsely required. The docstring constructs EInf at
  `max 2 (max (p-a+1) (q-b+2))` and composes transitions to the later pages.
- The final universally quantified implication ranges over all integer-graded
  A-module families `T` and all recorded `DecreasingFiltration (T n)` families
  `F`. Its first hypothesis is exactly `(F n).IsFinite ∧ (F n).IsExhaustive ∧
  (F n).IsSeparated` for every n. `IsFinite` allows arbitrary integer endpoints
  with one whole step and one zero step; it does not demand `F^0=T`.
- Its second hypothesis is `∀ p n, Nonempty ((F n).gr p ≅ EInf p (n-p))`.
  The recorded `.gr p` is the cokernel of the inclusion of consecutive steps,
  hence precisely `F^p T^n / F^(p+1) T^n`. The isomorphisms are in ModuleCat,
  so A-linear. `Nonempty` merely forgets the choice of these given isomorphisms;
  this theorem needs no compatibility between different graded-piece choices.
- The final two clauses assert `∀ n, Module.Finite A (T n)` and
  `∀ n, n<a+b → IsZero (T n)` with exactly the stated lower bound.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`; its full definition is Noetherianity of
  the self-module, equivalently every ideal is finitely generated.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence` and
  `CategoryTheory.E₂CohomologicalSpectralSequence` from
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`. I read the structure,
  the full `page` and `iso` signatures and the abbreviation's complex shape.
  This Mathlib leaf needs no project `lean` record or repair.
- `def-weil-finitely-generated-module`: `Module.Finite` from
  `Mathlib.RingTheory.Finiteness.Defs`, whose data is finite generation of top.
- `def-sp-filtration`: `CategoryTheory.DecreasingFiltration` and `.gr` from
  `WeilConjectures.CategoryTheory.Abelian.Filtration`; `.IsFinite` from
  `WeilConjectures.CategoryTheory.Filtration`; `.IsExhaustive` and `.IsSeparated`
  from `WeilConjectures.CategoryTheory.CanonicalFiltration`. The public import
  of CanonicalFiltration exposes these original recorded interfaces. I read
  all their signatures and definitions. No replacement filtration is defined.
- Proof-only leaf `lem-trf-noetherian-submodule-finitely-presented`:
  `Module.finitePresentation_of_finite` from
  `Mathlib.Algebra.Module.FinitePresentation` and `Module.IsNoetherian.finite`
  from `Mathlib.RingTheory.Noetherian.Basic`. Both modules are plain imports,
  following the node's recorded Mathlib match; their relevant signatures were
  read. Other proof dependencies are already public statement imports.
- `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the abelian-category
  instance needed to apply the spectral-sequence and filtration definitions.

Edge cases checked before writing:

- At the corner `(a,b)`, the threshold is `max 0 1 = 1`, so already every
  permitted page `s ≥ 2` has both differentials zero.
- The strict inequality matters: at `s=p-a` the incoming source can still lie
  on the boundary, and at `s=q-b+1` the outgoing target can still lie there.
  The statement does not claim either of these boundary differentials vanishes.
- Outside the quadrant, support propagates because a zero middle term has zero
  homology, even if one adjacent term is inside the quadrant.
- Negative offsets and negative total degrees remain covered by integer
  indexing; no reindexing to natural degrees excludes them.
- If `n<a+b`, any p has either p<a or n-p<b; hence every stable graded piece
  is zero, and the finite filtration forces zero abutment. At equality n=a+b
  the corner piece can survive, so the conclusion is strictly below the bound.
- The zero ring, the zero spectral sequence, zero abutments and a filtration
  whose whole and zero endpoints coincide cause no nontriviality assumption.
  The zero module has the empty finite generating set.
- The filtration's finite interval may start in any integer degree. Infinite
  filtrations with nonzero residual tail are excluded only by the node's own
  finiteness hypothesis, not by an extra boundedness convention.

Searches actually performed via `msearch.py Q66 <item>`:

1. LeanFinder: “A cohomological spectral sequence of modules over a Noetherian
   ring in a shifted first quadrant has finitely generated pages stable terms
   and finite filtered abutments”. Eight hits: complex lower/upper bounds and
   derived-category vanishing, including `CochainComplex.isGE_iff`,
   `CochainComplex.isLE_iff`, and `DerivedCategory.isZero_of_isGE`.
   None asserts module finite generation or this spectral-sequence result.
2. Loogle: `CategoryTheory.SpectralSequence, Module.Finite`: zero hits.
3. Mathlib grep: `Module.Finite|IsNoetherian|[Ff]inite` in
   `Algebra/Homology/SpectralSequence`: three hits, concerning finitely many
   rows or a finite filtration, not finitely generated module terms. Read both
   files, including Basic.lean:127–134.
4. LeanSearch: “A shifted first quadrant spectral sequence over a Noetherian ring
   with finitely generated second page has finitely generated abutment”. Eight
   hits include `isNoetherian_of_isNoetherianRing_of_finite`,
   `Module.IsNoetherian.finite`, FGModuleCat instances, and quasi-finite algebra
   facts. These do not give the page, stabilization and abutment assertions.

Local `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` used the item
id, `SpectralSequence.*ModuleCat`, `SpectralSequence.*cohomological`,
`finite.*[Aa]butment|[Aa]butment.*finite|[Qq]uadrant.*[Ff]inite|[Ff]inite.*[Qq]uadrant`,
and both proposed declaration spellings. No exact declaration or name collision
was found. I read the closest files:
`WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` defines
`pageInfinity` and `Abutment` for natural first-quadrant indices only and proves
page comparison for morphisms, with no Noetherian finite-generation statement;
`Sheaf.Algebra.Homology.SourceHyperExtModuleTarget` constructs a particular
hyper-Ext sequence with compatible stable terms and an abutment filtration;
`Sheaf.Algebra.Homology.BoundedAboveCoherentRHom` is the downstream geometric
application; `Sheaf.CategoryTheory.FilteredCohomologyDiagonalColimit` treats a
cohomology cocone, not this finiteness assertion. None states the item, and all
required notions already exist. No missing interface or mathematical fault was
found. No statement correction or dispute is required.

Validation: the prescribed `scompile.py` compiled the sole delivered file in both
sandbox and library mode against the live server build, cleanly (4.1 and 5.6 s).
All universes and variables are explicit and `autoImplicit` is disabled. There
are no scratch declarations or diagnostic commands in the module. Dry run and
delivery are performed with `deliver2.py`; the maintainer independently reviews
the delivered statement.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
