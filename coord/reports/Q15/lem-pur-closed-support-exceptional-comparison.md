## Worker report

The delivery states `AlgebraicGeometry.ProEtale.closedSupportExceptionalComparison`
in `Sheaf.AlgebraicGeometry.ClosedSupportExceptionalComparison`. Its proof is exactly
`sorry`. Its three helpers have real data: identity extension by zero, the canonical
compact-support/direct-image comparison, and the expanded comparison property.
No theorem is proved and no additional axiom is introduced.

The statement is read against the node, its four proof steps, and the first paragraph
of main-20261015 `sec-six-functors-basics/sk-prop-a1-kummer/lem-pur-gysin-structure.proof.md`.
The two underlying categorical inputs were also read at Stacks labels `lemma-yoneda`
(categories.tex, Tag 001P) and `lemma-closed-immersion-complement-retrocompact-exact`
(proetale.tex, Tag 09BM). Neither Stacks result alone asserts the site comparison.

Clause-by-clause correspondence:

- The finite-field/finite-coefficient datum is `P : WeilConjectures.PurityFiniteSetting.{u}`.
  Its fields retain the fixed finite-field datum, coefficient algebraic closure, finite
  intermediate extension, and positive level. `P.Ring` is the existing uniformizer-power
  quotient. `P.Coefficient = ULift P.Ring` is its published coefficient-size lift.
  The exact canonical `finiteCoefficientIntrinsicRealization`, rather than an arbitrary
  equivalence, reads intrinsic constructibility in the original constant-ring category.
- The finite-type k-schemes are `Z X : Scheme.{u}`, with explicit structure maps `aZ`,
  `aX` and `[LocallyOfFiniteType aZ] [QuasiCompact aZ]`, respectively for `aX`.
  The named closed immersion is `i` with `[IsClosedImmersion i]`, and `_hi : i ≫ aX = aZ`
  is its compatibility over k. There is no separatedness condition on X or Z beyond
  the node. The complementary open is `j` with `[IsOpenImmersion j] [QuasiCompact j]`
  and `hPair : IsCompl (Set.range i) (Set.range j)`.
- Ordinary module sheaves are `Sheaf (Scheme.ProEt.topology W)
  (ModuleCat.{u+1} P.Coefficient)`, on the actual small site. Site objects remain in
  universe u+1 and morphisms in u; no equality between those universes is imposed.
- `K : DerivedCategory.Plus ...` is precisely the arbitrary bounded-below input.
  There is no constructibility or etale-origin assumption on K.
- `R₀ = (finiteClosedUpperShriek P.Coefficient i j).rightDerivedFunctorPlus` is
  exactly the recorded right derived functor of closed inverse image of the open-unit
  kernel. `B₀ = (R₀.obj K).obj` is its ordinary derived value. No replacement support
  object is postulated. `S = supportClosedDerivedPlus ...` is exact termwise i_*.
- The intrinsic bounded constructibility assumption is the implication whose premise
  is `Scheme.intrinsicFiniteTorsionConstructible ... Z` applied to the canonical
  realization of B₀. This retains finite cohomology support and intrinsic constructibility
  of each cohomology sheaf, not an etale-origin substitute for constructibility.
- `c = Compactification.ofIsProper i` has ambient Z, open map id_Z, and proper map i.
  `B = sfFiniteExceptionalAt P.Coefficient c` is literally Rnu_*, then the ordinary
  etale compact-support right adjoint, then exact nu^*. The adjoint-existence proof
  is supplied from `Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`.
  Local compactness/Noetherian instances used there are derived from aZ and aX;
  none is a new hypothesis on the statement.
- `adj₀ : S ⊣ R₀` and the normalized `FixedComparisonClassAdjunction ...` are the
  adjunction data denoted in the node. They are quantified data, rather than freely
  specified Hom bijections or an assumed ambient pro-etale exceptional adjunction.
  Their existence is the cited support-localization and comparison-class input.
  The chosen etale right adjoint is the existing uniquely characterized right adjoint
  and its own adjunction; the node does not require a particular implementation of it.
- Both representing objects' bounded-below etale-origin conditions appear as the two
  premises `DerivedCategory.plusEtaleOrigin ... B₀` and `hB : ... (B.obj K.obj)`.
  This follows the node's setup paragraph and, unambiguously, proof step 3's words
  "explicitly assumed etale-origin hypotheses on both representing objects".
  It does not silently strengthen the node by turning these supplied conditions into
  additional conclusions. B₀ is already a D+ object; `hB.plus` types the other value.
- Every test object T is in D+ and has the retained pair
  `wT : Scheme.FixedEtaleOriginWitness Z P.Coefficient T`. Its etale complex and iso
  supply the origin proof to the existing witness-independent relative Hom bijection.
  Every `f : T.obj ⟶ B₀` is quantified; T need not be constructible.
- `a_T(f)` is `(adj₀.homEquiv T K).symm`, transported through the full inclusion
  `DerivedCategory.Plus.ι`. The inclusion's `preimage` lifts the same ordinary derived
  morphism; it imposes no condition on it.
- `e_T` is the inverse `adj.homEquiv` at c, precomposed with `q.inv.app T`.
  Here `q = closedSupportCompactIso ...` canonically identifies P_c with exact i_*.
  Its construction derives identity extension by zero from the existing adjunction,
  then uses `rightDerivedFunctorIsoMapDerivedCategory` and the canonical D+ inclusion
  compatibility. Thus the two Hom maps have exactly the same source, with no arbitrary
  isomorphism or mere Nonempty comparison supplied by a binder.
- The existential `φ : B₀ ≅ B.obj K.obj` and its first conjunct state
  `e_T(f ≫ φ.hom) = a_T(f)` for every retained origin witness and every f.
- The next conjunct quantifies every `ψ : B₀ ≅ B.obj K.obj` satisfying that SAME Hom
  condition and concludes `ψ = φ`. Uniqueness is therefore from the Hom condition
  alone, not only from the conjunction of Hom and counit equations.
- The final conjunct is `i_*(φ.hom) ≫ e_B(id_B) = epsilon₀`. The first factor is
  `DerivedCategory.Plus.ι.map (S.map (...preimage φ.hom))`; the second is `q.inv`
  followed by inverse relative `homEquiv` on the identity. The right-hand side is
  exactly the included `adj₀.counit.app K`. Composition order is Lean's left-to-right
  `≫`, corresponding to the node's epsilon composed with i_*phi.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, their ring structures and positive-level field data.
- Mathlib finite type, closed/open immersion and pro-etale site modules:
  `AlgebraicGeometry.LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`,
  `IsOpenImmersion`, and `Scheme.ProEt.topology`.
- `Sheaf.AlgebraicGeometry.SupportLocalizationTriangle`: `supportClosedDerivedPlus`,
  `supportLocalizationTriangle`; the imported pair-flasque module supplies
  `finiteClosedUpperShriek` and its kernel/closed comparison interface.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and its imported intrinsic
  module presentation: `finiteCoefficientIntrinsicRealization` and its exactness instances.
- `WeilConjectures.Compactification.Refinement` and its `Defs` import:
  `Compactification`, `Compactification.ofIsProper`.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`.
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `FixedComparisonClassAdjunction`, `.homEquiv`, its normalization and naturality fields,
  `exists_fixedComparisonClassAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and the imported finite-coefficient
  comparison framework: `comparisonUpperStar`, `comparisonLowerStar`,
  `DerivedCategory.plusEtaleOrigin`.
- The dependency module in this delivery supplies `Scheme.FixedEtaleOriginWitness`
  while reexporting the recorded `Scheme.EtaleOriginWitness` interface unchanged.
- Mathlib `DerivedCategory.Plus`, its full inclusion; upstream
  `Functor.rightDerivedFunctorIsoMapDerivedCategory`, exact descent and its D+
  compatibility; Mathlib adjunction uniqueness and Yoneda.
- The proof-only dimension input is imported from
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
  (`AlgebraicGeometry.exists_topologicalKrullDim_le`). The compact-support definition
  is the imported finite-coefficient `rightDerivedLowerShriekOfCompactification`.

Edge cases checked: Z empty; X empty (then Z and V empty); V empty/id closed immersion;
zero K; zero support value; arbitrary shifts and negative lower bounds; positive level
n=1; all test objects of etale origin, not only constructible ones. No nonemptiness,
positive-dimensionality, regularity, smoothness, or uniform bound is introduced.
The identity-extension and exact-derived comparisons apply to these cases as well.

Searches made before drafting:

- msearch leanfinder: "Canonical counit compatible isomorphism between closed support
  derived right adjoint and transported etale exceptional inverse image on bounded below
  etale origin complexes". Eight hits: generic derived-adjunction counit and unrelated
  restriction counit results; none states the node.
- msearch loogle: `CategoryTheory.Adjunction.rightAdjointUniq, CategoryTheory.yoneda`.
  Zero hits for that combined query.
- msearch grep: `support.*Exceptional|closed.*support.*comparison|rightAdjointUniq`.
  Nineteen hits, primarily generic `Adjunction/Unique.lean`; none supplies the
  site-specific comparison. Its generic identity-left-adjoint uniqueness is reused.
- rg in upstream WeilConjectures and side lean/Sheaf for the node id,
  `closedSupportExceptional`, `supportExceptional`, and intrinsic/fixed constructibility.
  No matching comparison declaration. Intrinsic constructibility and its canonical
  realization were found and reused; `purityCoprojectionConstructible` confirms the
  existing coordinate-transport pattern, and is not copied as another predicate.
- rg for `structure .*OriginWitness|def .*OriginWitness|abbrev .*OriginWitness`
  in upstream and both side roots found only the ringed/function-coefficient witnesses.
  Their full signatures and docstrings were opened. The fixed retained witness was absent.
- Missing/stale local upstream finite-coefficient source modules were read with
  `scompile.py --source` (Comparison, Constructible, UpperShriek, LowerShriek,
  LowerShriek.Defs and LowerShriek.Open.Defs), not replaced with guessed APIs.

No statement correction, new DAG node, or mathematical dispute is proposed. The
existing proof's explicit origin assumptions resolve the potentially ambiguous prose.

## Dependency modules

`def-weil-pbc-etale-origin-witness`: the recorded `Scheme.EtaleOriginWitness` accepts a
D+ object over a continuous-function coefficient ring sheaf. Its other recorded
`FiniteEtaleOriginWitness` also has ringed-module endpoints after restriction of scalars.
Neither can take an ordinary fixed-scalar D+ object used by the support and relative
adjunction interfaces. `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` reexports those
interfaces and adds exactly the displayed retained pair in fixed-scalar coordinates:
`complex : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat A))` and an
isomorphism from its actual derived comparison pullback to the given K. Arbitrary rings
are allowed; no finite, commutative, constructible, or discrete-topology condition is
added. The data are actual fields, not chosen from a sorry existence theorem. Only this
dependency node's lean field changes.

## Second reading by Q15

A separate pass by this worker reopened the node, the final Lean file and the recorded
support/relative-adjunction declarations. No other agent was started, as the dispatcher
brief explicitly forbids it; the maintainer supplies the independent delivery review.
The pass checked every item in the clause map above. It corrected the first draft's
stronger interpretation of the two origin sentences to match the explicit assumptions
in proof step 3, retained the full witness pair for test objects, and separated uniqueness
from the counit consequence. It checked the direction of q.inv, both inverse homEquivs,
and the map of phi in the counit equation. The coefficient realization is canonical,
the compactification is the identity one, and K is arbitrary in D+. All binders/universes
are explicit, no file-local notation or instances are used, every helper is listed in
lean.declarations, and the only postponed proof is the named main theorem.

Verification: final `scompile.py Q15 lem-pur-closed-support-exceptional-comparison`
compiled both delivered files separately in dependency order, with clean private-overlay,
sandbox and module-name checks. Final module-name checks took 10.1 s for the witness and
10.2 s for the comparison, each under the unchanged 60 s limit. No compiler warnings or
errors remain. A source/JSON check confirms that both node copies differ from the shared
base only in lean, both recorded signatures are verbatim, and every Lean line is at most
100 characters. No global build or direct Git command was run.

## Maintainer review fix (2026-10-18)

The delivered property took "DerivedCategory.plusEtaleOrigin ... B₀" and
"hB : DerivedCategory.plusEtaleOrigin ... (B.obj K.obj)" as hypotheses. The node's
statement asserts this ("Both $B_0$ and $B$ are bounded below of etale origin.",
not introduced by "Assume"). Its only role for $B_0$ is supplied by the stated
bounded intrinsic constructibility hypothesis. The citer lem-pur-gysin-structure
applies the item with only $B_0\in D^b_c$ and $K$ bounded below. Hypotheses would
leave that citer unable to apply the item (H3: conclusion weakened). The fix makes
both facts conclusions: `plusEtaleOrigin B₀ ∧ ∃ hB : plusEtaleOrigin B, ∃ φ, ...`.
The theorem signature and the node's `lean` record are unchanged. Node proof steps 2-3
call these facts "explicitly assumed", and the proof does not derive them. The
statement docstring now records this. For $B_0$ the fact follows from
lem-weil-pbc-finite-ring-constructible-derived-origin; for $B$ it follows from left
t-exactness of the right adjoint of the exact $F_c=i_*$. These are stage-3 proof inputs.
