## Worker report

The module `Sheaf.Paper.FiniteWindowBounded` states the bounded lower-tail lemma
in two declarations, `AlgebraicGeometry.ProEtale.finiteWindow_bounded` and
`AlgebraicGeometry.ProEtale.finiteWindow_bounded_padicAlgCl`. Both proofs are
`sorry`; no definition or additional theorem is introduced. The node's natural
statement, dependencies and proof remain unchanged.

### Clause-by-clause correspondence

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]` in both declarations.
- Lambda = E: the first declaration takes
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This is an actual intermediate
  subfield of the fixed algebraic closure with finite degree over Q_ell, carrying
  the restricted topology. Its condensed ring is
  `Profinite.continuousMapRingObj E`, continuous E-valued functions on profinite
  sets with pointwise operations.
- Lambda = Qbar_ell: the second declaration uses
  `Profinite.padicAlgClRingObj ℓ`, the abelian sheaf underlying
  `Profinite.padicAlgClCondensedRing ℓ`. Its sections have values in one finite
  subextension. It is not the larger ring of all continuous Qbar-valued functions.
- X is any scheme: `(X : Scheme.{u})`. No field, separation, finite-type or
  Noetherian hypothesis has been inserted.
- Lambda_X: `condensedRingObj Λ X`, the actual inverse image of the condensed
  coefficient ring along the map from the small pro-etale site to the point.
  The monoid object structure is supplied by the existing strong monoidal
  inverse-image functor. The category is
  `CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)`.
- C belongs to Cons: C is an object of that module category, with
  `hC : IsConstantModelConstructible Λ X C`. This is the recorded finite
  constant scalar-model predicate, with finite constructible locally closed
  stratifications and the affine-local convention on general schemes.
- A chosen integer d_C >= 0: `(d_C : ℕ)`. Natural numbers encode all and only
  nonnegative integers; the cutoff uses the explicit cast `(d_C : ℤ)`.
- The chosen uniform bound: `hExt` quantifies over every ambient module N with
  `IsConstantModelConstructible Λ X N`, every `r : ℕ`, and `d_C < r`, and asserts
  `Subsingleton (@Abelian.Ext _ _ _ (HasExt.standard _) C N r)`. Only
  nonnegative Ext degrees are needed because d_C is nonnegative. The standard
  size model is additively equivalent to the stated shifted ambient derived
  Hom by `Abelian.Ext.homAddEquiv`. The existential uniform-bound theorem is
  imported, but its particular witness is not fixed or assumed in place of hExt.
- L is in the ordinary ambient derived category: the binder has type
  `DerivedCategory (CategoryTheory.Mod ... (condensedRingObj Λ X))`.
  The existing module-object framework supplies its abelian/localization
  infrastructure; no abstract substitute category is used.
- L belongs to Dic: `hL` quantifies over every `q : ℤ` and says
  `ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
    ((DerivedCategory.homologyFunctor _ q).obj L)`.
  Mathlib's ind property is an actual small filtered colimit presentation,
  including its colimit universal property, and is closed under isomorphisms.
  Thus this expresses precisely the node's inline definition of Dic without
  defining another category or a copy of constructibility.
- Bounded: `hbounded` says the set
  `{q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ q).obj L)}` is finite,
  exactly the stated finite number of nonzero cohomology sheaves. No bounds,
  ordering of endpoints, or nonempty support are added.
- H^q(L)=0 for q > -d_C-1: `hvanish` quantifies over every integer q and uses
  `-(d_C : ℤ) - 1 < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj L)`.
  The strict inequality keeps the boundary degree -d_C-1.
- C is placed in degree zero and Hom is ambient: the conclusion is
  `Subsingleton ((DerivedCategory.singleFunctor _ 0).obj C ⟶ L)`.
  In the preadditive derived category every Hom has zero, so Subsingleton is
  equivalent to every morphism being zero, not merely the existence of a map.

### Dependency declarations read and used

All statement-dependency records and the full source signatures/docstrings were
read, using the shared published framework for its newer upstream files.

- `sk-def-sfb-qlbar-condensed`:
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`,
  `Profinite.padicAlgClCondensedRing` and `Profinite.padicAlgClRingObj`.
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`
  supplies the existing finite-intermediate-field encoding and its continuous
  ring object specialization. That module publicly imports EllAdic.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `upperStarFromPoint`, and `condensedRingObj`. The last is the recorded
  unbundled encoding of exactly the same transported ring object.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, with its action-compatible morphisms.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`, whose body uses
  `HasFiniteConstantLocalModel` and `IsFiniteConstantStratified`.
- `sk-lem-uniform-constructible-ext`: `Sheaf.Paper.UniformConstructibleExt`,
  `AlgebraicGeometry.ProEtale.uniformConstructibleExt`, imported publicly.
  Its first conjunct supplies a bound under its own standing finite-field
  hypotheses; this consumer instead takes exactly the chosen bound property
  specified in its node. It does not assert existence for an arbitrary scheme.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.singleFunctor`, and
  `DerivedCategory.homologyFunctor` from HomologySequence.
- `def-pc-ext`: `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`,
  `CategoryTheory.Abelian.Ext`, `HasExt.standard`, `Abelian.Ext.homAddEquiv`.
- The inline IndCons convention is Mathlib's
  `Mathlib.CategoryTheory.ObjectProperty.Ind`, `CategoryTheory.ObjectProperty.ind`,
  also used by the existing neighboring finite-window and ind-heart modules.

Already stated proof dependencies are imported without `public`:
`Sheaf.Algebra.Homology.LowerTruncationStepTriangle`
(`DerivedCategory.exists_lowerTruncationStepTriangle`),
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` (the shared composite
truncation definition), `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
(`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`), and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated` / `Triangulated`
(`CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`,
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`). The full natural
language proof appears in each theorem docstring. The proof-only nodes
`det-ind-heart-ii-vanishing` and `det-ambient-ind-derived-sums` have no recorded
Lean declarations in the read snapshot, so they contribute no import.

### Edge cases and source concern

Checked before writing: C=0, L=0, acyclic representatives with empty cohomology
support, the empty scheme, d_C=0, a single nonzero cohomology sheaf at exactly
q=-d_C-1, and support consisting entirely of degrees strictly lower than that
boundary. All are included. In the one-degree case -q >= d_C+1 is positive,
which matches the nonnegative Ext encoding and the stated shift convention.
Neither a lower support endpoint nor a nonempty support is required. Filtered
presentation indices live in the established site/sheaf universe u+1, and no
object/morphism universe equality has been imposed on the small pro-etale site.

STATEMENT-DISPUTED: The item explicitly allows an arbitrary scheme X, whereas
its proof-only dependency `det-ind-heart-ii-vanishing` explicitly assumes X
Noetherian. The supplied induction uses that result to extend the constructible
Ext bound to ind-constructible targets, and no such generalization to arbitrary
schemes was located. This is a gap in the supplied proof route, not a known
counterexample to the item. The node and source text agree, so the delivery
retains the exact statement rather than silently adding Noetherianity. The
maintainer should review this gap alongside the corresponding arbitrary-scheme
unbounded finite-window statement.

### Searches for an existing statement

- `msearch.py ... leanfinder`, query: "Ext bound for constructible sheaf implies
  Hom vanishing into bounded complex with ind constructible cohomology below
  minus d minus one". Eight results: derived cohomological bounds, the
  projective-source and injective-target vanishing theorems, and shifted-Hom
  size results. None states this lemma with a bound only on constructible targets.
- `msearch.py ... loogle`, query:
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`.
  One result in `Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives`.
  It assumes Projective and is not this statement.
- `msearch.py ... leansearch`, query: "Vanishing Hom from constructible sheaf
  into bounded complex below a uniform Ext bound". Eight results: projective
  and injective dimension vanishing, Ext.mk₀, and basic cohomology bounds.
  Dimension classes quantify over every ambient object, so none is an exact match.
- `msearch.py ... grep`, query:
  `from_singleFunctor_obj_eq_zero_of_projective|subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`,
  subdirectory `Algebra/Homology/DerivedCategory`. Five hits in TStructure,
  Fractions, Ext/EnoughProjectives and Ext/Basic. These are the same stronger
  projectivity or opposite t-structure orthogonality ingredients.
- `rg` over `WeilConjectures` and `lean/Sheaf`, query:
  `IndCons|indConstructible|IndConstructible|ind.*[Cc]onstructible|finiteWindow|finite_window`.
  No upstream exact lemma. Neighboring project modules already use
  `ObjectProperty.ind` of constant-model constructibility. FiniteWindowUnbounded
  states the unbounded variant and cites this bounded node in its proof; it
  cannot be used as a proof import without reversing the intended route.
- `grep -rn det-finite-window-bounded` over upstream `WeilConjectures`: no hits.
- `rg` over `dag/lean_names_upstream.json` for finiteWindow / IndCons / Hom bounds:
  no matching upstream declaration.

No new definition node or dependency repair is needed: the inline categories
and chosen bound property are expressible with the recorded interfaces.

### Validation

Compilation uses only the prescribed `scompile.py` wrapper. The first pass
found missing scoped ring-object instances in the explicit Mod specializations;
opening the existing `CategoryTheory.Obj` scope and qualifying `CategoryTheory.Mod`
repairs the elaboration without introducing an instance or changing a hypothesis.

The repaired module passed both wrapper checks cleanly: sandbox compilation
42.8 seconds and named-library compilation 46.7 seconds, each within the
unchanged 60-second limit. No warning was emitted. The file contains exactly
two named theorem sorries and has maximum line length 93 characters. JSON
comparison confirms that `lean` is the only changed node field.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
