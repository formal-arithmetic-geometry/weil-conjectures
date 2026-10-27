## Worker report

Stage 2 formalization of the current native tensor-closure statement. The released
stage-1 keep_plan re-split is separate work; the Q32 natural-language review does
not discharge this assignment. Read the maintenance handoff and repair note.
The node statement and proof are retained verbatim; only lean is recorded.

Module: Sheaf.Paper.NativeDerivedWeilTensorConstructible.
Declaration: AlgebraicGeometry.WeilComplex.nativeDerivedTensor_mem_weilComplex.
The sole theorem has proof sorry; no definitions or proved lemmas are added.

Hypothesis and conclusion correspondence:

- Finite field k₀: (k₀ : Type u) [Field k₀] [Finite k₀].
- Prime ℓ distinct from the characteristic: (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]. The inequality is symmetric to the prose convention.
- Separated finite-type k₀-scheme X₀: (X : Scheme.{u}),
  [X.Over (Spec (CommRingCat.of k₀))], and IsSeparated,
  LocallyOfFiniteType, QuasiCompact of its structure map. The latter two
  express finite type, with no additional geometric assumption.
- Ω and the algebraic closure k, geometric fiber and geometric Frobenius are
  exactly the existing framework constructions inside ProEtaleWeilSheaf.
  There is no replacement field or discrete coefficient sheaf.
- A,B in WC^der(X₀): (A B : WeilComplex k₀ l X). This is the full subcategory
  of the actual DerivedCategory (ProEtaleWeilSheaf k₀ l X).
- The specified ordered tensor B ⊗^L A is
  (ProEtaleWeilSheaf.nativeDerivedTensor k₀ l X).obj (B.obj, A.obj).
  DerivedWeilOperations selects precisely the native closed tensor and records
  its diagonal-action K-flat total-complex models.
- Membership of that ambient object in WC^der is
  WeilComplex.objectProperty k₀ l X applied to that tensor. The existing
  definition is DerivedCategory.TStructure.t.bounded intersected with
  DerivedCategory.homologyProperty (WeilSheaf.objectProperty k₀ l X).
  Thus the first conjunct is vanishing outside a finite cohomological interval,
  and the second requires every underlying cohomology module to be constructible.
  WeilSheaf.objectProperty pulls back the existing adic constructible predicate
  along IsoAlgebra.forget; its lisse definition allows a separate finite rank
  for each pro-etale covering member. No adjunction or internal-Hom conclusion
  is asserted.

Statement dependencies used, with full signatures and docstrings read:

- def-sf-native-weil-derived-framework: public import
  WeilConjectures.WeilSheaf.LowerShriek, the dependency's recorded entry module.
  Its declarations AlgebraicGeometry.ProEtaleWeilSheaf,
  AlgebraicGeometry.WeilComplex, AlgebraicGeometry.WeilComplex.objectProperty
  and AlgebraicGeometry.WeilSheaf.objectProperty are in the imported Category
  module. Also inspected AdicSheaf in ProEtale.Adic.Module, locallyFiniteFunctions
  and adicConstantSheaf in Adic.ConstantSheaf, and IsAdicLisseSheaf,
  IsAdicStratifiedLisseSheaf, IsAdicConstructibleSheaf in Adic.Constructible.
- def-sf-derived-weil-category-and-operations: public import
  Sheaf.Paper.DerivedWeilOperations; declaration
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor, with its
  nativeDerivedClosedComparison and nativeDerivedTensor_models. No dependency
  repair is needed.

The module docstring reproduces all eight current natural-language proof steps,
with their cited node ids. All recorded proof-dependency modules are imported
privately unless already publicly imported as a statement dependency. The two
Mathlib proof leaves are imported through AlgebraicGeometry.Noetherian and
CategoryTheory.Sites.LocallySurjective. No import was omitted for a cycle.

Searches actually run:

- msearch.py leanfinder: "Derived tensor product of two bounded constructible native
  pro-etale Weil complexes has bounded constructible cohomology". Eight hits,
  including Algebra.FormallyEtale.instTensorProduct and Kaehler differential
  base-change results. None concerns this native derived category.
- msearch.py loogle: "DerivedCategory, ObjectProperty, tensor". Zero hits;
  query rejected for unknown identifier ObjectProperty. This is not treated
  as evidence of absence.
- msearch.py grep: "constructible|Constructible" in Algebra/Homology: zero hits.
- rg over lean/WeilConjectures and lean/Sheaf for nativeDerivedTensor and the
  item id: the operations definition and normalization, no existing closure
  theorem for this tensor. Searches for constructible and tensor also returned
  finite-coefficient, completed integral, rationalized coefficient and WeilObject
  constructions. These are different categories; none is an exact attachment.
- rg for the new full declaration's short name in Mathlib, WeilConjectures and
  Sheaf found no collision. The wrapper logs are retained in searches.jsonl.

Edge cases: zero/acyclic A or B are allowed; membership adds no nonzero condition
and the interval property admits the zero object. Empty X is permitted: finite
type and separated do not exclude it, and constructibility has its usual
vacuous local quantifier. Rank zero and empty direct sums are included by the
framework's Fin n convention. Degree zero, negative degrees and arbitrary finite
cohomological ranges are all included; no common interval is imposed on A,B.
The universe u is explicit throughout and uses the existing framework's site and
coefficient size conventions without a new universe equality. No statement fault
or STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled the sandbox and final library module cleanly
(13.3 s and 17.8 s). deliver2.py --no-push returned OK: preflight passed and
the module compiled. Only the lean field differs from the live node; the
recorded signature matches the file verbatim; there is exactly one sorry.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
