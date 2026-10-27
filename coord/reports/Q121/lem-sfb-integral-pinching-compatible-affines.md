## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralPinchingCompatibleAffines` states
`AlgebraicGeometry.exists_affineOpens_preimage_eq_of_isIntegralHom`, with its whole
proof postponed by `sorry`. It introduces no definitions and changes only the
item node's `lean` field.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 19707–19756,
Situation `situation-pushout-along-closed-immersion-and-integral` and Lemma
`lemma-prepare-pushout-along-closed-immersion-and-integral` (Stacks Tag 0ECJ).
The source's arbitrary auxiliary base S is not used in this neighbourhood lemma;
its scheme-theoretic assertion is precisely the base-free statement of this node.
The source's last printed `i⁻¹(V')` is a typographical error for `i⁻¹(U')`, as
already recorded in the node's fifth proof step. No node correction is needed.

Clause correspondence:

- Schemes X, T, Z: `{X T Z : Scheme.{u}}`, with explicit universe `u`.
- The named scheme morphisms: `(i : Z ⟶ X) (j : Z ⟶ T)`.
- Closed immersion of i: `[IsClosedImmersion i]`.
- Integrality of j: `[IsIntegralHom j]`; there is no finiteness hypothesis.
- For every t, the image of its entire fibre lies in some affine open of X:
  `h : ∀ t : T, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = t → i z ∈ U`.
  The final pointwise condition is exactly `i '' (j ⁻¹' {t}) ⊆ U`.
- For every t, existence of open subschemes U and V: the conclusion begins
  `∀ t : T, ∃ (U : X.Opens) (V : T.Opens)`.
- Affineness of both: `IsAffineOpen U ∧ IsAffineOpen V`.
- V contains the specified point: `t ∈ V`.
- Equality as open subschemes of Z: `i ⁻¹ᵁ U = j ⁻¹ᵁ V` is equality in `Z.Opens`.
  These are the canonical open restrictions of the same scheme Z, so equality of
  opens identifies their restricted structure sheaves as well. This is not a
  statement about arbitrary isomorphic schemes or just an unspecified isomorphism.

Dependency declarations used, with signatures and docstrings read in the pinned
Mathlib sources:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, module
  `Mathlib.AlgebraicGeometry.Scheme` (lines 35–45 and 73–76). The same module
  defines `Scheme.Opens`, the inverse-image notation and `Scheme.Hom.mem_preimage`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, module
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (lines 42–46).
- `def-weil-finite-integral-morphism`: its recorded `AlgebraicGeometry.IsIntegralHom`
  declaration, defined in `Mathlib.AlgebraicGeometry.Morphisms.Integral`
  (lines 31–36); the recorded module `Mathlib.AlgebraicGeometry.Morphisms.Finite`
  is also publicly imported. The finite class is not imposed on j.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`, module
  `Mathlib.AlgebraicGeometry.OpenImmersion` (lines 35–39). Canonical opens of schemes
  use this existing interface; no replacement open-immersion predicate is defined.
- `AlgebraicGeometry.IsAffineOpen`, `Mathlib.AlgebraicGeometry.AffineScheme`
  (lines 250–252), says exactly that the associated open subscheme is affine.

The proof-only imports are `Mathlib.AlgebraicGeometry.Fiber` for
`Scheme.Hom.fiber` and its projections, and
`Sheaf.RingTheory.AlgebraicFieldImagePrincipalNeighbourhood` for
`PrimeSpectrum.exists_basicOpen_image_subset_of_integral_field_algebra`.
The remaining recorded proof dependencies are in the public Mathlib imports:
integrality versus universal closedness, stability under base change, the affine
open basis, Spec and its maps, and principal-localization open immersions.
The theorem docstring retains all five steps and the dependencies used by each.

Edge cases checked before writing:

- Empty T: the outer conclusion is vacuous and no point is demanded.
- Empty Z or an empty fibre: the fibre-containment clause is vacuous pointwise;
  the statement does not require a nonempty U or a nonempty common inverse image.
  The empty open is affine, including when X is empty.
- Identity maps: the conclusion permits the same affine neighbourhood on both sides.
- Arbitrary integral maps are permitted; no finite, finite-type, Noetherian,
  separated, reduced or characteristic assumption has been introduced.
- All schemes are in the standard arbitrary common `Scheme.{u}` universe.
  Every variable and universe is explicitly bound; there is no test-object
  quantification that could become vacuous through a smaller universe.

Searches actually run:

- `msearch.py ... leanfinder "Closed immersion Z into X integral morphism Z to T
  compatible affine neighborhoods with equal inverse images"`: eight hits,
  including `IsIntegralHom`, `IsIntegralHom.hasAffineProperty` and the affine
  property of closed immersions; no compatible-neighbourhood theorem.
- `msearch.py ... loogle '"AlgebraicGeometry", "affine", "integral"'`: ten hits,
  including the universal-closedness characterization of integral morphisms,
  `IsIntegralHom.toIsAffineHom`, and unrelated affine-space/integral-scheme facts;
  no compatible-neighbourhood theorem.
- `msearch.py ... grep
  'Ferrand|pinching|compatible.*affine|affine.*neighb.*integral' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for pinching, compatible affine
  phrases, integral affine-neighbourhood phrases and the node id found Ferrand
  pushout and line-patching modules and unrelated affine-chart statements.
  `FerrandSchemePushout.lean` cites this node in its proof plan; it does not state
  this intermediate lemma. No existing declaration has the statement.
- `rg` for the proposed declaration name in both library roots and
  `dag/lean_names_upstream.json`: no hits. The node-id search found only the
  Ferrand pushout proof-plan citation.

No missing notions, unusable dependency interfaces, new nodes, statement changes,
or disputed statements were found. Validation uses only the prescribed server
single-file compilation and delivery preflight tools.

## Second reading by Q121

Author's clause check for direct delivery; independent review belongs to the
maintainer. Re-read the node, source and module together: the fibre hypothesis
quantifies over every t and every z with j(z)=t, rather than a selected lift;
both output opens have their affineness asserted; membership uses the same t;
and inverse-image equality is typed in the same `Z.Opens`. The conclusion adds
no containment in the initially chosen U and no nonemptiness of its inverse
image. The signature uses the existing dependency declarations and keeps only
the closed-immersion, integrality and fibre-neighbourhood hypotheses. No mismatch
was found and no mathematical statement was changed.
