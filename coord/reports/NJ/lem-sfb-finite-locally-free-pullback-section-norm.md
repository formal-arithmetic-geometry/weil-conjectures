## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreePullbackSectionNorm` states
`AlgebraicGeometry.Scheme.Modules.exists_finiteLocallyFree_pullback_section_norm`,
with `sorry` as its only proof. The node statement and its dependencies are unchanged;
only the `lean` attachment is added. No new definition or dependency repair is needed.

Source read: `literature/stacks-project/divisors.tex`, Section 0BCX and the statements
and proofs of 0BD2 (lemma-finite-locally-free-has-norm), 0BCY
(lemma-norm-invertible), and 0BCZ (lemma-norm-map-invertible). Apply the section norm
to the nth tensor power, with the pullback identity giving degree d*n downstairs.
The declaration docstring records all four accepted DAG proof steps, including
explicit gluing of the degree comparison and the elementary complement identity.

Hypothesis and clause correspondence:

- Schemes and f:Y→X: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
- Constant finite locally free degree d: `[f.IsFiniteLocallyFreeOfDegree d]`.
  Its parent class includes finite, flat, and locally of finite presentation;
  its field gives fibreDegree=d at every point. `(d : ℕ) (hd : 1 ≤ d)` imposes
  exactly the required positive integer degree.
- Invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`, using the recorded
  Zariski locally free rank-one predicate, with no additional coherence condition.
- Positive integer n: `(n : ℕ) (hn : 1 ≤ n)`.
- Section of (f*L) tensor n: `(s : Γ(((tensorPullback f).obj L).tensorPow n, ⊤))`.
  This is the explicit tensor-formula pullback, not an unspecified functor.
- Existence of t in Γ(X,L tensor dn): `∃ t : Γ(L.tensorPow (d * n), ⊤)`.
- X_t equals the points with whole fibre in Y_s: the first equality is
  `nonvanishingLocus (L.tensorPow (d * n)) t =
  {x : X | f ⁻¹' {x} ⊆ nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s}`.
  The inverse image is the underlying point fibre, just as in the node.
- X_t equals X minus f(Y minus Y_s): the second equality uses
  `(f '' (nonvanishingLocus (((tensorPullback f).obj L).tensorPow n) s)ᶜ)ᶜ`.
  These two conjuncts express the displayed chain of equalities.
- No ampleness, properness, normality, Noetherianity, reducedness, separability,
  nonemptiness, or further assumptions appear.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree` and `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` and `Scheme.Modules.tensorPow` (0 is the tensor
  unit; successor is tensor with L).
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly exposes
  `Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; its object really is
  sheafified extension of scalars of the inverse image. The recorded adjunction
  and section normalization were also read; the theorem only needs the object.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `Scheme.Modules.nonvanishingLocus`, defined by the germ lying outside the
  maximal ideal times the stalk. `IsAmple` is not assumed.

All stated proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm`,
`WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`,
`WeilConjectures.Topology.GlueSheavesOfModules`, and
`WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`.
The invertible-pullback instance is already in the public Invertible import.
`lem-sfb-norm-frame-tensor-section-gluing` and
`lem-sfb-finite-function-norm-nonvanishing` have no recorded Lean declaration at
reading time, so there is no module to import for those proof-only inputs.
Neither is needed to type the statement.

Edge cases checked mathematically before writing:

- Empty X (and hence Y): both displayed sets are empty; no nonemptiness binder.
- d=1, f=id: the section transfers along the identity comparison and both loci
  are the original nonvanishing set.
- A disjoint union of d copies: locally the norm is the product of section
  coefficients, nonzero exactly when each fibre point is nonzero.
- A nonreduced finite free algebra, e.g. k[ε]/ε²: multiplication by ε has zero
  determinant and ε vanishes in the residue field, as the formula requires.
- Zero section: positive degree excludes empty fibres over existing points, so
  both loci are empty. A nowhere-vanishing section gives the whole base.
- d=0 and n=0 are explicitly excluded by the node itself. All allowed d,n are
  represented by naturals; u is explicit and arbitrary. No universe equality
  between otherwise independent objects is introduced by the statement.

Searches actually run:

- `msearch.py ... leanfinder`: "For a finite locally free morphism of degree d a
  section of the nth tensor power of a pulled back invertible module admits a
  norm section of tensor degree d times n whose nonvanishing locus consists of
  fibres contained in the original nonvanishing locus". Eight results included
  `Module.comap_freeLocus_le`, `Module.mem_freeLocus_iff_tensor`,
  `StructureSheaf.normalize_finite_fraction_representation`, and residue-fibre
  lemmas; none states this section-norm theorem.
- `msearch.py ... loogle '"norm", "pullback"'`: twelve hits about categorical
  normal monomorphisms, seminorms, and normalization pullbacks; no match.
- `msearch.py ... grep 'norm.*(section|invertible|tensorPow)|Norm.*(Section|Invertible)'
  AlgebraicGeometry`: three unrelated EllipticCurve/NormalForms hits.
- `rg` in the prescribed `lean/WeilConjectures` and `lean/Sheaf` trees for norm,
  section, invertible, tensorPow and the proposed name; exact item-id search in
  `lean/WeilConjectures`; name search in `dag/lean_names_upstream.json`.
  No existing exact theorem or name collision. The nearby
  `exists_invertible_norm_sections` was read in full: it assumes a norm family
  and produces an unspecified invertible norm module; it does not identify
  the target as the supplied L.tensorPow (d*n), so it is not this statement.

Validation: scompile.py NJ lem-sfb-finite-locally-free-pullback-section-norm
compiled the delivered file in both sandbox and library module modes, cleanly
(9.7 s and 5.8 s). No diagnostic commands remain. All binders and universes are
explicit; every line is at most 100 characters. No statement fault was found.

## Second reading by NJ

The dispatcher explicitly forbids starting other agents; this is a second pass by
this worker, not a claim of an independent reviewer. The maintainer's independent
review remains the next review of the delivery.

Reopened the node and the completed file and checked every binder and clause:
Y is the source of f, X is the base, L is on X, and the source section belongs to
the nth power after tensor pullback. The target exponent is exactly d*n. Both
positive hypotheses are present. The first set equality uses the inverse image
of the singleton x, and the second uses the image of the complement, with both
complements taken in the correct schemes. The same existential t occurs in both
clauses. The nonvanishing definition is the recorded germ/residue definition;
there is no support-of-section substitution. Checked the degree-class signature
and the tensorPow recursion against their source files. No mismatch was found,
and no statement or dependency correction was made.
