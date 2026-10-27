## Worker report

The module `Sheaf.AlgebraicGeometry.ProperSpaceSquareZeroEffectivity` states
`AlgebraicGeometry.AlgebraicSpace.exists_properSpace_squareZero_effective`, with
`sorry` as its entire proof. Its four ancillary declarations merely package existing
constructions: the spectrum as a representable space over the terminal scheme,
the inherited commutative-ring instance on the compatible-sequence subring, that
subring bundled as a commutative ring, and its coordinate ring homomorphisms.
There are no new mathematical notions, new nodes, dependency repairs, or statement
corrections. The item gains the already landed `def-sfb-space-morphism-properties`
and `def-trf-scheme-algebraic-space` as statement dependencies, to cite the exact
existing definitions used. All original fields besides `lean` and these additions
to `stmt_deps` remain unchanged.

Source read: `literature/stacks-project/quot.tex`, Tag 0D3X,
`lemma-spaces-defo-thy`, lines 3646-3730, especially the strong-effectivity proof
beginning with the inverse system of rings. This is the supporting effectivity
claim inside the proof, not the lemma's separate openness-of-versality conclusion.
The source assumes square-zero kernels for every ordered pair of indices and
imposes no Noetherian, dimension, or projectivity condition on this claim.
The theorem docstring carries all eight proof steps, including the derived-Hom
test (not an ordinary tensor/limit isomorphism), realization, and transition
compatibility.

Clause-by-clause translation:

- The inverse sequence with compatible ring homomorphisms is
  `R : ℕᵒᵖ ⥤ CommRingCat.{u}`. Index `n` denotes the source's `n+1`, so the
  source's first ring is `R.obj (op 0)`. Functor identity/composition are exactly
  the transition identity and compatibility equations, with no missing initial term.
- Every transition is surjective: `hSurj`, quantified over every arrow `i ⟶ j`.
  Every kernel has square zero: `hSq`, using `RingHom.ker (R.map b).hom ^ 2 = ⊥`.
  This is not merely an adjacent-kernel hypothesis.
- The concrete ring R of compatible sequences is `effectivityRing R`, exactly
  `RingCat.sectionsSubring (R ⋙ forget₂ CommRingCat RingCat)`, bundled with `.of`.
  Its carrier consists of sequences satisfying every transition equation, and
  addition, multiplication, negation, zero, and one are coordinatewise.
  `effectivitySectionsCommRing` reuses `Subring.toCommRing` on the ambient product
  of commutative rings. `effectivityRingProjection` is evaluation composed with
  the subring inclusion; its underlying function is `s ↦ s.val (op n)`.
- Algebraic spaces and actual morphisms are retained by
  `X : ℕ ⥤ AlgebraicSpace (⊤_ Scheme.{u})`. Every scheme has its unique map to
  this terminal scheme, equivalently Spec Z (Mathlib's terminal-object result).
  Thus use of a common ambient base adds no geometric hypothesis. Conversely,
  a space mapping to Spec R_n is a space over Spec R_n, by restriction to its
  slice; this is the standard base-change equivalence of Spaces 03I4/03I5/04SG
  (also stated in the existing `SpaceChangeBase` module).
- The structural morphisms are `f n`. Their targets
  `(R.rightOp ⋙ effectivitySpectrum).obj n` are exactly the existing
  `schemeSpace` of Spec(R_n), expressed as `ObjectProperty.lift` of the existing
  fppf Yoneda functor. `effectivitySpectrum` uses `Scheme.Spec` and the inverse
  of `Over.equivalenceOfIsTerminal`; its arrows are the actual `Spec.map` maps.
- Flatness is `hFlat : ∀ n, MapIsFlat (f n)`, which tests the exact recorded
  scheme property `AlgebraicGeometry.Flat` on compatible etale scheme charts.
- Properness is `hProper : ∀ n, MapIsProper (f n)`: separated diagonal,
  quasi-compact and chart-locally finite type, and closed on point spaces after
  every algebraic-space base change. This uses the existing space property and
  does not replace proper by projective or by a scheme-only representability test.
- Finite presentation has its three explicit parts: `hQC` is quasi-compactness,
  `hQS` is quasi-compactness of the relative diagonal (quasi-separatedness), and
  `hLFP` is the existing chart test of `LocallyOfFinitePresentation`. Their
  inclusion spells out exactly the node's finite-presentation convention,
  even though properness also entails some of these conditions.
- The specified isomorphisms and their compatibility are `hCart` together with
  the functor `X`. In detail, an isomorphism X_m times_(R_m) R_n to X_n over
  Spec R_n determines the arrow X_n to X_m. The identity and cocycle conditions
  say exactly that these arrows form a functor on ℕ. Conversely, `hCart` recovers
  the unique such isomorphism respecting the structural projections by the
  fibre-product universal property. The squares are in actual fppf sheaves,
  whose full subcategory is algebraic spaces; the existing fibre-product theorem
  gives its algebraicity. Hence this is an equivalent encoding of the specified
  isomorphisms, with their full data retained through their cartesian arrows.
- The conclusion's `Y` and `g` give an algebraic space over Spec(effectivityRing R).
  The next five conjuncts give flatness, properness, quasi-compactness,
  quasi-separatedness, and local finite presentation, in the same order and with
  the same predicates as for the stages.
- `a : X ⟶ (Functor.const ℕ).obj Y` gives maps X_n to Y compatible with every
  specified transition. Its naturality equation is
  `X.map b ≫ a.app m = a.app n` (after the constant-functor identity).
  The final `∀ n, IsPullback ...` uses exactly the coordinate projection on the
  base. The inverse of its unique comparison isomorphism is the required
  Y times_R R_n to X_n. Naturality of `a`, the original cartesian squares,
  and uniqueness of pullback arrows give compatibility of these isomorphisms
  with every specified transition, not just existence separately for each n.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`, and `Scheme.Spec` (actual schemes and spectra).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` (actual chosen
  fibre products and projections); `IsPullback` is their universal-square form.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `IsSurjective`, including their full signatures and docstrings.
- `def-weil-size-convention` has a convention-only record. The module binds
  universe `u` explicitly, with `CommRingCat.{u}`, `Scheme.{u}` and the existing
  `AlgebraicSpace` sheaf convention, and binds every variable explicitly.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  `IsSeparated`, `UniversallyClosed`; the space counterpart is the already
  landed extension of these same conventions.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact` (the node's finite
  type is their conjunction).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `MapIsSeparated`,
  `MapIsFiniteType`, `MapIsUniversallyClosed`, `MapIsProper`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, using the
  existing algebraic-space point topology; no curve/dimension condition is used.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` and its named
  property proof `schemeSheaf_isAlgebraicSpace`.
- `Mathlib.Algebra.Category.Ring.Limits`: `RingCat.sectionsSubring`.
  `Mathlib.AlgebraicGeometry.Limits` and
  `Mathlib.CategoryTheory.Comma.Over.Basic`: terminal scheme and
  `Over.equivalenceOfIsTerminal`, respectively. The canonical maps have real data.

The already stated proof dependencies are imported without `public`:
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`, and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`.
The other six proof dependencies have no Lean record yet, so supply no import;
this statement does not require their theorem interfaces. Their proof roles are
retained in the theorem docstring and the unchanged DAG proof.

Edge cases checked before writing: constant towers have zero kernels and are
allowed; identities are included in the square-zero condition and have kernel
zero; the zero ring and empty spaces are allowed (no Nontrivial/Nonempty/field
assumption); arbitrary dimensions and nonprojective proper spaces are allowed;
non-Noetherian rings are allowed; ℕ is nonempty and is just a reindexing of the
positive integers, with no finite or truncated tower; every pair of indices is
covered; no chart, atlas, representability-by-scheme, or extra equality of
universe levels is imposed. The compatible-sequence ring remains in universe u.

Searches for existing declarations (msearch.py, group Q58, this item):

- LeanFinder: `Compatible flat proper finitely presented algebraic spaces over
  square zero inverse sequence of rings are effective over the inverse limit`:
  eight results, including scheme affine-limit lemmas and Flat; none is space
  effectivity.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, RingHom.ker`: zero hits, unknown
  AlgebraicGeometry.AlgebraicSpace in Mathlib.
- msearch grep: `AlgebraicSpace|square.zero.*effectiv` in AlgebraicGeometry:
  zero Mathlib hits.
- LeanSearch: `inverse limit commutative rings compatible sequences`: eight
  results including RingCat.limitRing and CommRingCat.limitCommRing, whose
  implementations use the existing compatible-sequence subring.
- Loogle: `RingCat.sectionsSubring`: one exact hit, used unchanged.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for space properness,
  finite presentation, square-zero effectivity, and inverse sequence/limit
  constructions: found the existing `AlgebraicSpaceMorphismProperties`,
  `ProperCurveModuli`, `SpaceChangeBase`, and `RingCat.sectionsSubring` usages;
  no existing effectivity statement. Exact item-id search in WeilConjectures
  had no hit. Full sources/docstrings of the used interfaces were opened.
- Local DAG search identified the already landed `def-sfb-space-morphism-properties`
  and `def-trf-scheme-algebraic-space`, so these are cited instead of duplicated.

Validation: prescribed `scompile.py Q58 lem-sfb-proper-space-square-zero-effectivity`
compiled the only delivered file individually, first as sandbox module and then
as `Sheaf.AlgebraicGeometry.ProperSpaceSquareZeroEffectivity`, in 2.3 seconds
for each, with no errors or warnings. The first attempt exposed a missing
commutative-ring instance for the RingCat subring; the final named instance
reuses the ambient commutative product and `Subring.toCommRing`, and the
unchanged concrete subring then compiled. There are no `#check` probes left,
no lines over 100 characters, no auto-bound implicits, and no postponed data.
No STATEMENT-DISPUTED or node fault remains.

## Second reading by Q58

This is a separate self-review, not a claim of independent-agent review: the
worker brief forbids starting other agents; the maintainer independently reviews
the delivered statement. I reopened the node and final module and matched every
clause as above. Specifically I checked the direction n to m of the space maps
against the opposite direction of ring maps, and checked that hCart is the
square X_n to X_m over Spec R_n to Spec R_m. I checked all ordered pairs occur
in both hSurj and hSq, and that cocycles are the X functor laws. I checked that
the conclusion uses a natural transformation, retaining compatibility rather
than asserting unrelated stage isomorphisms. I unfolded MapIsProper and
MapIsLocallyOfFinitePresentation in the existing module and checked the explicit
qc and diagonal-qc clauses. I checked the ambient terminal-base formulation
adds no S-linearity requirement over an arbitrary fixed nonterminal S. Finally
I checked effectivityRing is the existing actual sequence subring and its
projections are actual evaluations. No mathematical mismatch or statement change
was found. The only implementation correction was the inherited commutative-ring
instance noted above; it does not change the statement.
