## Worker report

The delivery states `AlgebraicGeometry.Etale.compactSupport_unbounded_amplitude` in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportUnboundedAmplitude`. Its only proof is `sorry`.
It introduces no definitions, new nodes or dependency replacements. The item is unchanged
outside `lean`. This is the ordinary unbounded etale module-sheaf encoding used by the
recorded derived-category dependency.

Hypothesis and clause correspondence:

- An algebraically closed field of characteristic p > 0 is `k : Type u`, `[Field k]`,
  `[IsAlgClosed k]`, `p : ℕ`, `[CharP k p]`, and `hp : 0 < p`.
- A prime l different from p is `l : ℕ`, `[Fact l.Prime]`, and `hlp : l ≠ p`.
- Finite-type k-schemes are `X Y : Scheme.{u}` with `X.Over (Spec (.of k))` and
  `Y.Over (Spec (.of k))`; each structure morphism has both `LocallyOfFiniteType`
  and `QuasiCompact`. This is the recorded convention's exact meaning of finite type.
- The k-morphism is `f : X ⟶ Y` with `[f.IsOver (Spec (.of k))]`. Its separated
  finite-type hypotheses are `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
  `[QuasiCompact f]`. There is no separatedness hypothesis on either k-structure morphism.
- The fixed compactification is `c : Compactification f`: its fields `c.i`, `c.g`,
  `c.Z`, `c.comm`, `c.isOpenImmersion`, and `c.isProper` give j, r, the ambient
  scheme, the factorization, open immersion and properness. This is the compactification
  structure publicly imported by the recorded refinement-category module.
- Each of X, Y and the ambient scheme has its own explicit conjunction
  `IsNoetherian T ∧ CompactSpace T ∧ QuasiSeparatedSpace T` in the conclusion.
  These are conclusions, not extra assumptions.
- The coefficient-independent geometric bound is the next conjunct `∃ d : ℕ, ∀ y : Y, ...`.
  The coefficient type has not yet been quantified there. The expression in that conjunct
  is `topologicalKrullDim` of `pullback f` along
  `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
  (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y`.
  This is precisely the recorded geometric-fibre dependency, including its chosen closure.
  The comparison is with `(d : WithBot ℕ∞)`, so empty fibres are included.
- Every finite commutative coefficient ring is quantified by
  `∀ (C : Type (u + 1)) [CommRing C] [Finite C]`.
  Annihilation by a power of l is `(∃ s : ℕ, (l ^ s : ℕ) • (1 : C) = 0)`.
  Killing 1 is equivalent to killing the entire ring by that integer; it does not
  restrict C to residue rings, fields, or a particular positive exponent.
- F is always the existing `rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} C) c`. Its definition is exactly the functor on the unbounded
  derived category induced by exact j_!, followed by the total right derived r_*.
  No functor, comparison map or compactification is supplied as a free extra parameter.
- Exactness as a triangulated functor is `F.IsTriangulated`, with its existing
  canonical `CommShift ℤ` and additive structures supplied by the imported functor APIs.
- Preservation of arbitrary set-indexed coproducts is
  `∀ I : Type w, PreservesColimitsOfShape (Discrete I) F`; the index universe w is
  independent and the index type is not assumed nonempty or finite.
- For every integer b the lower bound is
  `∀ (b : ℤ) (K : DerivedCategoryModule C X), DerivedCategory.IsGE K b →
  DerivedCategory.IsGE (F.obj K) b`. There is no upper boundedness hypothesis on K.
- The remaining part quantifies over every `d : ℕ` satisfying the same geometric-fibre
  bound. Its first conjunct is `∀ (a : ℤ) (K : DerivedCategoryModule C X),
  DerivedCategory.IsLE K a → DerivedCategory.IsLE (F.obj K) (a + 2 * (d : ℤ))`.
  There is no lower boundedness hypothesis on K.
- For every a ≤ b, the last conjunct takes both `DerivedCategory.IsGE K a` and
  `DerivedCategory.IsLE K b`, and returns `DerivedCategory.IsGE (F.obj K) a` and
  `DerivedCategory.IsLE (F.obj K) (b + 2 * (d : ℤ))`. This states the interval assertion.
- Empty sources and targets and d=0 are allowed: no nonemptiness binder and no positive-d
  condition occurs. For an empty source all geometric fibres are empty and extension
  by zero is zero. An empty target forces the source and the compactification ambient
  scheme empty. Empty fibres have bottom topological Krull dimension, below 0.

Dependency declarations read and reused:

- `def-weil-scheme-morphism-properties` is explicitly a convention, not a declaration.
  The declarations selected from its constituent records are
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`/`QuasiCompact`, and
  `AlgebraicGeometry.IsSeparated` from `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-weil-compactifications-refinements` is recorded on
  `AlgebraicGeometry.Compactification.Refinement` and `.category` in
  `WeilConjectures.Compactification.RefinementCategory`. That module publicly imports
  `WeilConjectures.Compactification.Defs`, whose `AlgebraicGeometry.Compactification`
  signature and complete fields were read and used directly.
- `def-weil-pbc-derived-categories`: imported
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`; its public coefficient module
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` supplies
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the exact recorded category. No alternate
  SheafOfModules category, bounded subcategory, or pro-etale coefficient category is used.
- `def-weil-geometric-fibre`: `CategoryTheory.Limits.pullback` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, specialized along the
  algebraic-closure residue-field point exactly as its lean.note specifies.
- `def-weil-triangulated-category`: its Mathlib match supplies
  `CategoryTheory.Functor.IsTriangulated` and `Functor.CommShift ℤ`, read in
  `Mathlib.CategoryTheory.Triangulated.Functor`.
- `def-sbc-standard-tstructure-derived-category`: the Mathlib match is
  `DerivedCategory.TStructure.t` in `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
  Its `DerivedCategory.IsGE` and `DerivedCategory.IsLE` are used without copies;
  their definitions and cohomological characterizations `isGE_iff` and `isLE_iff` were read.
- The existing candidate is
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` in
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, already carried by
  `def-amb-etale-compact-support`. Its full signature and body were read; it is used directly.
  Triangulated right-derived instances are publicly imported from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.

Every recorded proof-dependency module, including the Mathlib matches, is imported for
stage 3; proof-only imports are not public. The six-step natural-language proof appears
in the theorem docstring, naming the contributing DAG nodes. No auxiliary theorem is
silently postponed. The source PDF was read at printed pp. 12–13: Corollary 2.19 gives
amplitude [0,2d], while Proposition 2.23 supplies the coproduct context.

Edge cases checked before writing: arbitrary unbounded-below inputs in IsLE, arbitrary
unbounded-above inputs in IsGE, arbitrary fixed compactifications with unused boundary
components, schemes not separated over k, d=0, a=b, empty fibres/source/target, the zero
coefficient ring (also allowing exponent s=0), non-field finite coefficient rings and empty
coproduct families. No constructibility, Tor amplitude, finite stalk, positive dimension,
or extra invertibility assumption is present. No statement fault or dispute was found.

Searches for existing statements (the prescribed wrapper logged full results in
`searches.jsonl`):

- `msearch.py ... leanfinder "Finite etale compact support preserves coproducts and sends
  unbounded derived objects bounded above by a to objects bounded above by a plus twice
  the geometric fibre dimension"`: eight hits about `DerivedCategory.IsGE`, `IsLE`,
  bounded representatives, and complex support; none states this compact-support result.
- `msearch.py ... loogle '"DerivedCategory", "IsLE"'`: twelve hits, including
  `DerivedCategory.IsLE`, `isLE_iff`, and bounded-representative lemmas; no match.
- `msearch.py ... grep 'compactSupport|rightDerivedLowerShriek|geometricFiberDimension'`:
  twenty-five displayed hits, concerning compact support of continuous functions,
  not ordinary etale derived compact support.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for compact-support functors, unbounded
  amplitude, `isLE.*LowerShriek`, and `preservesCoproducts` located the existing functor,
  `exists_isLE_rightDerivedLowerShriekOfCompactification_obj`,
  `isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`, and
  `proper_rightDerivedLowerStar_preservesCoproducts`. Their signatures/docstrings were read.
  The first amplitude result only bounds by compactification fibres; the heart result
  only covers sheaves placed in degree zero; the last concerns proper direct image.
  None states the present package or its upper bound for every original-fibre bound d.
- The required search for the item id in `lean/WeilConjectures` found no declaration;
  searching the proposed theorem name in Mathlib and both project roots found no collision.

Validation: server compilation and the delivery preflight are run using `scompile.py`
and `deliver2.py --no-push`; only the expected theorem-sorry warning is accepted.
The worker delivers directly; the maintainer performs the independent review.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
