## Worker report

States `CategoryTheory.Functor.leftDerived_ses_cohomology_normalization` in
`Sheaf.CategoryTheory.LeftDerivedSesCohomologyNormalization`. The theorem has
one `sorry`; the two helper definitions have concrete data. The natural-language
statement, dependencies and reviewed proof are unchanged. No missing notion or
unusable dependency was found, so there are no new nodes or dependency repairs.

Source read: Stacks `derived.tex`, Tag 015D, `lemma-F-acyclic-ses`, its proof,
and supporting `lemma-irrelevant` (05T5(3),(4)), `lemma-negative-vanishing`
(05TC) and `lemma-left-exact-higher-derived` (05TD). The result is the indicated
dual cohomology sequence and normalization, before any acyclicity assumption.
The current blueprint ancestor `lem-trf-local-term-locality` and its proof were
also read in `literature/blueprint/latest`; this generic homological tool leaves
that unit's statement and route unchanged.

Hypotheses and objects, one by one:

- The abelian categories are `{A : Type uA} [Category.{vA} A] [Abelian A]` and
  `{B : Type uB} [Category.{vB} B] [Abelian B]`. All six object, morphism and
  localization universes are explicit and independent; `autoImplicit` is false.
- Enough projectives is `[EnoughProjectives A]`. Mathlib's class supplies an
  epimorphism from a projective object to every object; `Projective.factors`
  is precisely the lifting property across every epimorphism.
- The additive right exact functor is `(V : A ⥤ B) [V.Additive]
  [PreservesFiniteColimits V]`. For additive functors between abelian categories,
  finite-colimit preservation is equivalently preservation of cokernels and
  finite sums. This is also exactly the interface of the recorded object-
  cohomology dependency, and Mathlib's stated right-exact convention.
- `HomotopyCategory A (ComplexShape.up ℤ)` and its analogue for B are integer
  cochain homotopy categories. `[HasDerivedCategory.{wA} A]` and its B analogue
  specify localization sizes, and `DerivedCategory.Qh` is the recorded
  localization from the homotopy category, with its quasi-isomorphism instance.
- `(LV : DerivedCategory A ⥤ DerivedCategory B)` and
  `ε : DerivedCategory.Qh ⋙ LV ⟶ V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
  DerivedCategory.Qh` are the specified total functor and actual comparison.
  `hLV : LV.IsRightKanExtension ε` is the universal total-left-derived
  condition (Mathlib `IsLeftDerivedFunctor` is equivalent to this condition
  for the localization). This uses the same interface as the recorded theorem.
- `hdefined` quantifies over EVERY object of the unbounded homotopy category,
  and asserts essential constancy with some value Y of the diagram
  `MorphismProperty.Over.forget (HomotopyCategory.quasiIso A (.up ℤ)) ⊤ X ⋙
  Over.forget X ⋙ V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh`.
  The category contains every commuting triangle between denominators;
  transitions are not restricted to quasi-isomorphisms. It uses the recorded
  `IsEssentiallyConstantProDiagram` directly, as does the dependency theorem.
- `DerivedCategory.singleFunctor A 0` is the canonical image of N[0]. The helper
  `leftDerivedObjectCohomologyFunctor LV q` is exactly its composite with LV
  and degree-q cohomology. Its object and map operations give the node's
  T^q(N) and T^q(f), with no independent or arbitrary data.
- `(S : ShortComplex A) (hS : S.ShortExact)` packages M'=S.X₁, M=S.X₂,
  M''=S.X₃, i=S.f and p=S.g, including p i=0, monicity, exactness and epimorphy.
- The final morphism w has exactly the required source and shifted target.
  `leftDerivedShortComplexTriangle LV S w` is the explicit `Triangle.mk`
  of LV applied to i[0], LV applied to p[0], and w. The hypothesis hT says
  this very triangle is distinguished. Neither arrows nor identifications
  are replaced by arbitrary maps.

Conclusions, clause by clause:

- The first conjunct quantifies over all q in ℤ. Its three image-kernel
  equalities express exactness at T^q(M), T^q(M''), and T^(q+1)(M'),
  respectively. The last position covers T^q(M') by shifting q down by one.
  Thus all positions in the node's long exact sequence are included.
  `DerivedCategory.HomologySequence.δ` of the stipulated triangle is the
  canonical ∂^q: cohomology of w followed by the standard shift identification.
  No independently chosen connecting maps are introduced.
- `∀ N, IsIso (leftDerivedObjectComparison V LV ε N)` asserts invertibility
  of the actual H⁰(ε), normalized by the canonical termwise-single and
  degree-zero single-complex identifications. The definition is imported
  unchanged from the recorded dependency, rather than choosing an isomorphism.
- The next conjunct is naturality for EVERY morphism f:N₁→N₂:
  `T⁰(f) ≫ c_N₂ = c_N₁ ≫ V.map f`. Lean's diagrammatic composition makes
  this exactly c_N₂ ∘ T⁰(f) = V(f) ∘ c_N₁.
- `∀ (N : A) (q : ℤ), 0 < q → IsZero (T^q(N))` gives all positive vanishing.
  It does not assert negative vanishing.
- The next equality asserts exactness at V(M') in the normalized tail.
  Its incoming arrow is explicitly `HomologySequence.δ ... (-1) 0 ≫
  leftDerivedObjectComparison V LV ε S.X₁`, namely c_M' ∘ ∂^(-1), and
  its outgoing arrow is exactly `V.map S.f`.
- `imageSubobject (V.map S.f) = kernelSubobject (V.map S.g)` asserts exactness
  at V(M), using exactly V(i) and V(p).
- `Epi (V.map S.g)` asserts exactness at V(M'') before zero. In an abelian
  category this is equivalently image(V(p))=V(M''), the kernel of the zero
  arrow. The node does not assert injectivity of the leading connecting map
  or monicity of V(i), and neither is added here.

Image-kernel equality uses Mathlib's standard `imageSubobject` and
`kernelSubobject`. Its equivalence with `ShortComplex.Exact` is
`CategoryTheory.ShortComplex.exact_iff_image_eq_kernel` in the imported
`Mathlib.CategoryTheory.Abelian.Exact`. Thus this is the usual categorical
exactness with all objects and arrows retained.

Dependency declarations and sources read:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, class and surrounding explanation.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, their localization and triangulation
  instances in `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and
  `DerivedCategory.homologyFunctor` in its `HomologySequence` module.
- `def-pur-saturated-triangulated-localization`:
  `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`,
  including `Functor.IsTriangulatedLeftDerivedValue` and
  `Functor.IsTriangulatedLeftDerivedDefinedAt`; these unfold to the same
  denominator diagram using `CategoryTheory.IsEssentiallyConstantProDiagram`
  from `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`.
  Both signatures and docstrings were read. These definitions are available
  through the public import of the object-cohomology module.
- Proof dependency `lem-sf-derived-homology-long-exact`:
  `DerivedCategory.HomologySequence.δ`, `exact₁`, `exact₂`, `exact₃` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, all signatures
  and the δ docstring read. This module is public since δ occurs in the statement.
- Proof dependency `lem-trf-left-derived-object-cohomology`:
  `CategoryTheory.Functor.leftDerivedObjectComparison` and
  `CategoryTheory.Functor.leftDerived_object_cohomology`, module
  `Sheaf.CategoryTheory.LeftDerivedObjectCohomology`. The full file, including
  both signatures and the seven-step proof docstring, was read. Its public
  import is required because the canonical comparison occurs in our statement.

Edge cases checked before writing:

- V=id: positive and negative derived cohomology vanish, c is the canonical
  identity identification, and the tail is the original short exact sequence.
- V=0, zero objects, and the zero short exact sequence: all displayed images
  and kernels agree and the final zero-object arrow is epi.
- V=(-)⊗ℤ ℤ/n, n>1, applied to 0→ℤ --n→ ℤ→ℤ/n→0: the negative-degree term
  T^(-1)(ℤ/n)=Tor₁(ℤ/n,ℤ/n)=ℤ/n can map nontrivially into V(ℤ).
  Hence retaining the leading connecting arrow and omitting any claim that
  V(i) is mono is essential. The statement does exactly that.
- q=0 and q=-1 use the exact canonical degree-zero identifications and the
  (-1,0) connecting map; arbitrary negative q remain covered by the universal
  long exact sequence. Positive vanishing includes q=1, giving the terminal
  epimorphism without an acyclicity assumption.
- The final map w is arbitrary subject to the given triangle being distinguished;
  its canonical δ is used throughout, without choosing a different triangle.
- There is no finite-generation, smallness equality, boundedness or acyclicity
  hypothesis. Independent category and localization universes are retained.

Searches actually run through msearch.py, group Q40 and this item:

- LeanFinder: "The long exact cohomology sequence of a total left derived
  functor of a right exact additive functor normalizes in degree zero to the
  original short exact sequence". Eight hits: `ShortExact.singleδ`,
  `Functor.homologySequence_exact₁/₂/₃`, exact-functor Ext maps and related
  constructions. None states this canonical total-derived normalization.
- Loogle: "DerivedCategory.HomologySequence.exact₁,
  DerivedCategory.HomologySequence.δ". One hit, `HomologySequence.exact₁`;
  it supplies one general long-exact position, not the normalization theorem.
- Mathlib grep: "leftDerived.*(exact|cohomology)|HomologySequence", restricted
  to CategoryTheory. Eleven hits, mainly general homological functors and
  `Functor.leftDerivedZeroIsoSelf`. Read the latter's module: it uses
  ℕ-indexed projective resolutions and does not identify the specified
  total-derived counit and the particular triangle's connecting morphisms.
- LeanSearch: "The total left derived functor of a right exact functor gives
  an exact sequence ending in the original functor applied to a short exact
  sequence". Eight hits including `Functor.totalLeftDerived`, `Functor.leftDerived`,
  `ProjectiveResolution.isoLeftDerivedObj`, and the general derived-functor
  interfaces. None gives the whole statement with its canonical comparison.
- `rg` of both project roots for
  `leftDerived.*(cohomology|[Ss]es|[Nn]ormal)|leftDerivedObjectComparison` and
  the exact item id found the existing object-cohomology module and unrelated
  geometric constructions, but no copy of this statement.
- `rg` of both roots and `dag/lean_names_upstream.json` for the proposed triangle
  helper and theorem names found no declarations. The exact item-id search
  of the upstream root and name index found none either.

No statement is disputed and no correction was necessary. All theorem proofs
remain `sorry`; no axiom, opaque data, or private copy of a dependency was added.
Initial scompile.py validation passed both sandbox and library checks in about
2 seconds each, with no errors or non-sorry warnings. Final dry-run results are
recorded below after preflight.

Dry run: `deliver2.py Q40 lem-trf-left-derived-ses-cohomology-normalization
--no-push` printed OK: preflight passed and the final module compiled cleanly.
A final local consistency read confirmed that only the node's `lean` field
changed, its statement is the signature verbatim, its Lean lines are at most
95 characters, and its sole postponed proof is the named main theorem.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
