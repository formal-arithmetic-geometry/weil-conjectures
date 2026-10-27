## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralOrbitAffineDescent` states
`AlgebraicGeometry.integral_orbit_affine_descent`, with its only proof `by sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
I read the full source statement and proof of Stacks 0ABE in
`literature/stacks-project/more-groupoids.tex`, lines 2670–2698. The module docstring
and theorem docstring identify the source; the latter gives all six accepted proof
steps, including point lifting and the closed-complement proof of openness.

The statement is rendered hypothesis by hypothesis as follows:

- The schemes are `{U R T : Scheme.{u}}`, with arbitrary explicit universe `u`.
  The morphisms `s t`, `e`, `i`, and `c : pullback s t ⟶ R` are the node's
  source, target, identity, inverse, and composition. `hG : IsGroupoidScheme
  s t e i c` supplies exactly the recorded absolute groupoid laws.
- Integrality of the source and target is `[IsIntegralHom s] [IsIntegralHom t]`.
- The node's integral morphism is `(a : T ⟶ U) [IsIntegralHom a]`.
- Meeting every R-orbit is `horbit : ∀ u : U, ∃ y : T, ∃ r : R,
  s r = u ∧ t r = a y`. This is precisely membership of an image point `a y`
  in `t(s⁻¹({u}))`; it does not require `a` itself to be surjective.
- The given point and affine neighborhood are `(x : T) (V : T.Opens)`,
  `(hxV : x ∈ V)` and `(hV : IsAffineOpen V)`.
- The restricted arrow scheme is the existing categorical iterated pullback
  `pullback (pullback.snd a s ≫ t) a`: a test-point is a triple `(y,r,z)`
  with `a y = s r` and `t r = a z`. The canonical source is
  `pullback.fst (pullback.snd a s ≫ t) a ≫ pullback.fst a s`;
  the canonical target is `pullback.snd (pullback.snd a s ≫ t) a`.
  `hVinvar` equates their inverse-image opens of V, exactly the stated
  equality of open subschemes. The induced operations are determined by the
  original operations and these pullbacks; they are contextual definitions,
  not additional hypotheses or conclusions of the invariant-affine assertion.
  Only the endpoint projections occur in that assertion, so their existing
  pullback expressions suffice without introducing another definition.
- The conclusion is `∃ W : U.Opens, IsAffineOpen W ∧ a x ∈ W ∧
  s ⁻¹ᵁ W = t ⁻¹ᵁ W`. These are respectively the open, its affineness,
  the requested image-point membership, and invariance as open subschemes.

I read the full signatures and docstrings of the statement dependencies:

- `Sheaf.AlgebraicGeometry.GroupoidScheme`,
  `AlgebraicGeometry.IsGroupoidScheme`; the twelve fields encode precisely
  the node's laws on all test schemes. This module is publicly imported.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`,
  `AlgebraicGeometry.IsIntegralHom`; its affine-preimage and integral-section-map
  fields render the integral part of `def-weil-finite-integral-morphism`.
  The finite-morphism part of that bundled node is not assumed here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`;
  these render `def-pc-fibre-product`, using the Scheme pullback instance
  already imported by GroupoidScheme. The canonical iterated pullback is used
  directly, not replaced by a scheme with arbitrary endpoint morphisms.

`Mathlib.AlgebraicGeometry.AffineScheme` supplies `IsAffineOpen`; `Scheme.Opens`
always carries the canonical open subscheme structure, so equality of opens
expresses the specified equality of open subschemes. All already-stated proof
dependencies' source modules are imported privately, including
`WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget`
(`AlgebraicGeometry.isAffine_of_surjective_of_universallyClosed`).
No proof import creates a new statement dependency or any extra hypothesis.

Edge cases checked: the empty T admits no supplied x, so no nonemptiness
assumption is added; an empty U is also compatible with the formulation.
The identity map a gives the original invariant neighborhood case.
For the trivial groupoid, the orbit-meeting condition specializes to surjectivity
of a, as it should. For a general groupoid a need not be surjective.
No finiteness, flatness, separatedness, Noetherianity, reducedness, field,
characteristic, or rational-point assumption occurs. Opens need not be nonempty
except for the particular V containing x. There is no independent smaller
universe for tests that could make a quantifier vacuous.

Searches made through the prescribed `msearch.py Q132
lem-sfb-integral-orbit-affine-descent` wrapper:

- `leanfinder`, query `scheme groupoid integral orbit affine descent`: 8 hits,
  concerning integral affine-local criteria and affine transition limits;
  none gives groupoid invariant-affine descent.
- `loogle`, query `IsGroupoidScheme IsIntegralHom IsAffineOpen`: no hits;
  the remote index does not know the project's `IsGroupoidScheme`.
- Repeated `loogle` with qualified indexed names
  `AlgebraicGeometry.IsIntegralHom, AlgebraicGeometry.IsAffineOpen`: 4 hits,
  `IsIntegralHom.isIntegral_app`, its alias, the class constructor, and
  `isIntegralHom_iff`; none is the required statement.
- `grep`, query `find-affine-integral|orbit.*affine` with subdirectory
  `Sheaf/AlgebraicGeometry`: no indexed Mathlib hits.
- `grep`, query `groupoid.*integral|integral.*groupoid`, subdirectory
  `AlgebraicGeometry`: 0 hits.
- `leansearch`, query `Invariant affine open neighbourhood descends along
  integral morphism meeting each scheme groupoid orbit`: 8 hits about affine
  opens, integrality of section maps, universal closedness, and local criteria;
  none states the required lemma.

Direct `rg` searches in both live `lean/WeilConjectures` and `lean/Sheaf` for
`IsGroupoidScheme`, `orbit.*affine|affine.*orbit|invariant.*affine|integral.*orbit`,
and `0ABE|find-affine-integral`, and the exact item id/name, found no exact
existing statement. Related orbit-fibre, finite-action, Sumihiro, and affine
invariant-ring statements have different hypotheses and conclusions. The
existing groupoid structure and pullback notions were reused throughout.
The exact proposed declaration name was also absent from `dag/lean_names_upstream.json`.

Compilation: prescribed `scompile.py Q132 lem-sfb-integral-orbit-affine-descent
<module file>` succeeded in both sandbox and library contexts, 1.3 seconds each,
with no errors or warnings. `autoImplicit` is explicitly false; every scheme,
map, point, open, and universe in the signature is bound.

No statement dispute or node fault was found.

## Second reading by Q132

Clause audit by the assigned worker: the original node and final Lean file were
read together. All seven hypothesis groups and all four conclusion components
are matched above. The restricted source uses the first T coordinate and its
target the last T coordinate, with the original r between them. Their defining
pullback equations have the correct s/t order. In particular the invariant-open
hypothesis has the full iterated scheme pullback, rather than a Cartesian product
of underlying point sets, and the orbit condition permits a nonsurjective a.
There are no extra existential operations in the conclusion. No final mismatch
was found and no node statement was changed. This is a worker self-audit;
the dispatcher's brief assigns independent review to the maintainer and forbids
starting another agent.
