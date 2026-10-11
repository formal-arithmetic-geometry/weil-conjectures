## Worker report

Existing declaration: `AlgebraicGeometry.Smooth.exists_isStandardSmooth`, in
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, pinned source lines 99–102.
No module is written, no theorem is proved, and only the item's `lean` field is changed.

Hypotheses and conclusion, clause by clause:

- Schemes X and S: ambient `{X Y : Scheme.{u}}`, with Y representing S; arbitrary universe u.
- Morphism f: `(f : X ⟶ Y)`.
- Smoothness: `[Smooth f]`, exactly the current recorded declaration of
  `def-sbc-smooth-morphisms`. Its note invokes Stacks 02H6 to identify the formally smooth,
  locally finitely presented description with Mathlib's affine-local definition.
- Point x: `(x : X)`; no extra hypothesis on x.
- Affine open V in S: existential `(U : Y.Opens) (_ : IsAffineOpen U)`.
- Affine open W in X: existential `(V : X.Opens) (_ : IsAffineOpen V)`.
- x in W: existential proof `(_ : x ∈ V)`.
- f(W) contained in the base open: `(e : V ≤ f ⁻¹ᵁ U)`, which says exactly that every
  point of W maps into the base open. It also implies f(x) belongs to that open.
- R = O_S(V) and A = O_X(W): the domain and codomain of `f.appLE U V e` are
  `Γ(Y, U)` and `Γ(X, V)`, respectively.
- The specified ring map: `Scheme.Hom.appLE` is defined in Scheme.lean:196 as
  `f.app U ≫ X.presheaf.map (homOfLE e).op`. The first component is f-sharp on U
  (Scheme.Hom.app, line 179); the second is exactly restriction to V. `.hom` unbundles
  this CommRingCat morphism to its ring homomorphism.
- A standard smooth as an R-algebra via that map: `(f.appLE U V e).hom.IsStandardSmooth`.
  `RingHom.IsStandardSmooth` in RingHom/StandardSmooth.lean:47 is defined as
  `@Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra`, so its algebra structure is the one
  the node specifies, rather than an arbitrary additional algebra structure.

Dependency declarations read (full signatures and docstrings):

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme, lines 42 and 74. Scheme carries the local affine
  condition; Hom extends the morphism of locally ringed spaces.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, lines 62–65. The relative dimension and
  etale clauses of that definition node are unused by this item.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, lines 470 and 479. Affine opens in the conclusion
  use Mathlib's `IsAffineOpen`; no separately chosen isomorphism to a spectrum is required.
- `def-weil-pbc-standard-smooth-algebra` is a Mathlib leaf without a lean record:
  its mathlib_match is `Algebra.IsStandardSmooth`,
  Mathlib.RingTheory.Smooth.StandardSmooth, lines 57–64. This requires a finite
  submersive presentation. SubmersivePresentation's invertible Jacobian condition
  and finite index sets encode the node's n >= c presentation, after numbering the
  selected variables first. The ring-hom variant above is this same predicate.

Edge cases checked: the empty source has no point x, so the statement makes no
unjustified nonemptiness claim; a point excludes the empty target. No Noetherian,
separatedness, field, characteristic, dimension, or nontrivial ring hypothesis is
added. Zero relative dimension and presentations with no relations are allowed by
IsStandardSmooth (empty Jacobian determinant is one). Arbitrary scheme universes
are retained, and only existence of the base affine open is claimed, rather than
strengthening the statement to a prescribed base open.

Source checked: local literature/stacks-project/morphisms.tex is absent on this machine;
opened the official https://stacks.math.columbia.edu/tag/01V7 instead. Its implication
from smoothness at x to an affine standard smooth neighborhood gives the node's
existential conclusion for a smooth morphism. No statement correction is needed.
The node's old search-history objection to the Smooth hypothesis predates the
current dependency record and no longer applies. No STATEMENT-DISPUTED fault.

Searches (msearch.py E1 with this item, unless otherwise stated):

- leansearch: "smooth scheme morphism locally standard smooth affine neighborhoods";
  unavailable (Internal Server Error).
- leanfinder: "smooth scheme morphism admits affine neighborhoods at every point with
  standard smooth induced ring map"; eight hits, including the older indexed name
  AlgebraicGeometry.IsSmooth.exists_isStandardSmooth and its characterization.
- loogle: "AlgebraicGeometry.Smooth.exists_isStandardSmooth"; one exact hit with the
  affine-open binders and the induced appLE ring map.
- grep: "exists_isStandardSmooth|def appLE|IsStandardSmooth" in
  AlgebraicGeometry/Morphisms/Smooth.lean; characterization and its predicates found.
  Direct reading of the pinned file confirms the exact theorem at lines 99–102.
- rg of WeilConjectures and lean/Sheaf for "exists_isStandardSmooth|" followed by the
  item id: existing uses in DensePoints, Differentials, RegularImmersion, and the
  project's Mathlib-extension Smooth module; no separate declaration tagged with
  this item. The item-id grep is included in that rg query.
- rg of dag/lean_names_upstream.json for "exists_isStandardSmooth": no match;
  this is a Mathlib declaration, not an upstream project declaration.
- Direct Mathlib rg for Scheme, Spec, appLE and IsStandardSmooth located the
  definitions listed above; read the full defining declarations and docstrings.

Validation: no new Lean module to compile; the delivery dry run validates the
existing Mathlib declaration record. Independent second reading remains for the
second worker, as required by the brief.

## Second reading by E1

I reread the node statement, its Stacks source (Morphisms, Lemma 01V7 / tag 01V7),
and the recorded declaration. The objects and clauses match item by item:

- The schemes are the ambient `{X Y : Scheme.{u}}`; `Y` is the node's `S`.
- The morphism is `f : X ⟶ Y`, with the node's smoothness hypothesis rendered by
  `[Smooth f]`. The dependency record identifies this Mathlib affine-local
  predicate with the node's Stacks formally-smooth plus locally-finitely-presented
  notion via Tag 02H6.
- The point is `(x : X)`, with no additional point or nonemptiness hypothesis.
- The existential affine opens are `(U : Y.Opens) (_ : IsAffineOpen U)` and
  `(V : X.Opens) (_ : IsAffineOpen V)`, followed by `x ∈ V` and
  `e : V ≤ f ⁻¹ᵁ U`. Thus the Lean `U,V` are the source's `V,W`, respectively,
  and the inclusion gives `f(W) ⊆ V`.
- The induced ring map is exactly `(f.appLE U V e).hom`: `appLE` composes the
  map on sections with restriction, as required by the source's `f^sharp` map.
- The final clause is `(f.appLE U V e).hom.IsStandardSmooth`, the recorded
  `RingHom.IsStandardSmooth` form of the node's standard-smooth `R`-algebra.
  Quantifier order and all existential witnesses agree with the node.

No mismatch was found and no source or Lean file required changes. The dependency
declarations were reread: `Scheme`/`Scheme.Hom`, `AlgebraicGeometry.Smooth`,
`Spec`/`Spec.map`, and `Algebra.IsStandardSmooth`; each supplies the notion used
by the signature. Searches were repeated with `rg` in Mathlib, WeilConjectures,
and `lean/Sheaf`, plus the recorded LeanFinder/Loogle searches; only
`AlgebraicGeometry.Smooth.exists_isStandardSmooth` is an exact existing statement,
so the node correctly records it as `existing: true` and has no module.

Edge cases remain covered: an empty source has no `x`; the target is therefore not
silently required to be nonempty. No Noetherian, separated, field,
characteristic, or dimension assumptions occur. Universes are those of the
schemes, and `n = 0`, zero-dimensional fibres, and presentations with no
relations are allowed by `IsStandardSmooth`.
