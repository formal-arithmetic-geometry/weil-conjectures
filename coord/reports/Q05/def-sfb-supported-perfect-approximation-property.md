## Worker report

Defines `AlgebraicGeometry.Scheme.HasSupportedPerfectApproximation` in
`Sheaf.AlgebraicGeometry.SupportedPerfectApproximation`, with real propositional data
and no theorems or sorry. The node statement and its dependencies are unchanged.
Read the entire stage-2 brief, stage document, worker role, delivery-errors H,
and both the withdrawn CompactObject example and its recorded upstream replacement.
No repair note for this item is present.

Source checked directly: `literature/stacks-project/perfect.tex`,
`definition-approximation-holds` (08EM), `definition-approximation` (08EN), and
`definition-supported-on`. These are exactly the approximation and support conditions
of the node. In particular the input is quasi-coherent but the output is stated in
all of D(O_Y), and the integer is not required to be nonnegative.

Clause-by-clause correspondence:

- An arbitrary scheme Y is `(Y : Scheme.{u})`. There is no quasi-compactness,
  quasi-separatedness, Noetherian, affine, or nonempty assumption on Y.
- Every closed subset T is `∀ T : Set Y, IsClosed T →`.
- Retrocompactness of the open complement is
  `∀ W : Y.Opens, IsAffineOpen W → IsCompact (Tᶜ ∩ (W : Set Y))`.
  This is literally the node's affine-open test, in the ambient topological space;
  quasi-compactness is Mathlib's `IsCompact` without a Hausdorff assumption.
- The quantifier order is `∃ r : ℤ, ∀ (m : ℤ) (F : schemeDerivedCategory Y)`.
  Thus r may depend on Y and T, and is uniform in both m and F.
- Membership in D_QCoh is `schemeDerivedQCohProperty Y F` on an object of D(O_Y).
  This uses the recorded object property defining that full subcategory, rather
  than changing the underlying category or defining a second quasi-coherence notion.
- `(m-r)`-pseudo-coherence is precisely `IsMPseudoCoherent Y (m - r) F`.
- Input support in every degree i >= m-r is `∀ i : ℤ, m - r ≤ i → ∀ y : Y,
  y ∉ T → Subsingleton (...)`, where (...) is the underlying group of the stalk
  at y of `(DerivedCategory.homologyFunctor ... i).obj F`. On cochain complexes
  indexed by `ComplexShape.up ℤ`, Mathlib's homology functor is the cohomology
  sheaf H^i. A subsingleton abelian group is exactly a zero stalk.
- The output is `∃ (P : schemeDerivedCategory Y) (v : P ⟶ F), IsPerfect Y P ∧ ...`.
  It uses the recorded perfect predicate, and supplies an actual derived morphism.
- Output support is the same stalk condition with P, for every `(i : ℤ) (y : Y)`
  outside T, with no cohomological bound on i.
- For every i > m, `IsIso ((DerivedCategory.homologyFunctor ... i).map v)` is the
  requested isomorphism of cohomology sheaves induced by that very morphism v.
- In degree m, `Epi ((DerivedCategory.homologyFunctor ... m).map v)` is the
  surjective morphism of module sheaves. It means local/stalkwise surjectivity,
  as in the source, without requiring surjectivity on every open's sections.

Dependency declarations read in full and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphism
  structure; its `Opens` is Mathlib's type of open subsets.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`, and
  `schemeDerivedQCohCategory` (the first two are used directly).
- `Sheaf.AlgebraicGeometry.MPseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherent` (local strictly perfect maps with
  cohomology isomorphisms above the degree and an epimorphism at the degree).
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsStrictlyPerfect`, `IsPerfect`, and
  `perfectSubcategory` (the second is used directly).
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen`.
  Its signature and docstring identify affine open subschemes exactly.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` (already publicly
  imported by the recorded derived-category module): `DerivedCategory.homologyFunctor`.

The three `HasDerivedCategory.{w}` instance binders are the existing categorical
interfaces: on Y, on the open subschemes needed by IsMPseudoCoherent, and on the
over-sites needed by IsPerfect. They share the morphism universe w and the module
universe u, as those dependencies do. They impose no geometric condition on Y
and do not identify different sites or their category instances. All variables
and universes are explicitly bound; autoImplicit is disabled.

Edge cases checked before writing:

- Empty Y is permitted, and both support conditions quantify over an empty point
  type. No nonempty cover or fixed cover-index universe is introduced.
- T = Y: its complement is empty, so every affine test is compact and both stalk
  conditions impose no restriction. This is the global approximation case.
- T = empty: every affine open is quasi-compact, and P must have zero cohomology
  everywhere. With r = 0, the input is zero in all degrees >= m, so P = 0 has
  exactly the required approximation behavior. The definition does not assert a
  particular witness, and does not require r >= 0.
- F = 0 admits P = 0 for any admissible degree. No nonzero object is required.
- Arbitrarily negative m and r are allowed. The boundary input uses `≤`, the
  isomorphism output uses strict `<`, and the boundary epimorphism is separate.
- Non-quasi-separated Y is still included: the complement's retrocompactness is
  tested by the actual affine-open intersections, not inferred from openness.

Searches for an existing notion (all executed for Q05 and this item):

- `msearch.py leanfinder`, query "Uniform approximation by perfect complexes with
  closed support and a cohomological error bound": OK, 8 hits, beginning with
  `DerivedCategory.IsGE`, `exists_iso_Q_obj_of_isGE_of_isLE`,
  `exists_iso_Q_obj_of_isGE`, `exists_iso_Q_obj_of_isLE`; none is this definition.
- `msearch.py loogle`, query "HasSupportedPerfectApproximation, IsMPseudoCoherent":
  OK, 0 hits; unknown identifier HasSupportedPerfectApproximation.
- `msearch.py grep`, query `SupportedPerfect|supported.*perfect.*approx|approx.*perfect`:
  OK, 0 Mathlib hits.
- `msearch.py leansearch`, query "Uniform supported perfect approximation of pseudo
  coherent complexes on schemes": OK, 8 hits, principally uniform topology and
  `Scheme.quasiCompactCover_iff`; none is the supported approximation property.
- Direct `rg` of Mathlib, WeilConjectures and Sheaf for
  `HasSupportedPerfectApproximation|SupportedPerfectApproximation`, and broader
  `IsMPseudoCoherent|supportedPerfectApprox|SupportedPerfectApprox|perfect.*approximation|Perfect.*Approximation`:
  only the algebraic-space analogue `AlgebraicSpace.HasSupportedPerfectApproximation`
  in `Sheaf.AlgebraicGeometry.SpaceSupportedPerfectApproximation` and related results.
  Read that entire module: it concerns the small etale derived category of an
  algebraic space and cannot replace this scheme/Zariski dependency interface.
  Existing ring-level pseudo-coherence likewise does not define this property.
- `grep -rn` of the exact item id in WeilConjectures: no hits.
- `rg` of `dag/lean_names_upstream.json` for approximation / 08EM / 08EN:
  only unrelated approximation lemmas, no declaration for this notion.

Validation: the prescribed `scompile.py` compiled the sandbox file and its library
module separately against the live published library, both clean (9.8 s and 10.1 s).
No new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
