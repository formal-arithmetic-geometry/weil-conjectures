## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition` states
`AlgebraicGeometry.IsHProjective.comp` with proof `by sorry`. It adds no definition.
The module and declaration are the canonical statement already present in the current
base; this packet records the item for group NA with the exact same signature.

The node says: if `g : X → Y` and `h : Y → S` are H-projective, then `h ∘ g` is
H-projective. The Lean rendering is clause by clause:

- The arbitrary schemes and common universe are `{X Y S : Scheme.{u}}` with an
  explicit `universe u`.
- The first morphism is `(g : X ⟶ Y)` and the second is `(h : Y ⟶ S)`.
- The two hypotheses are the typeclass binders `[IsHProjective g]` and
  `[IsHProjective h]`.
- The composite `h ∘ g` is categorical composition `g ≫ h`.
- The conclusion is `IsHProjective (g ≫ h)`.

No field, finiteness, separatedness, Noetherian, characteristic, nonemptiness, or
other hypothesis is added. The only proof is `sorry`, as required for stage 2.

The statement dependency is `AlgebraicGeometry.IsHProjective` from
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, recorded by
`def-kun-projective`. I read its full class declaration: it supplies a finite
coordinate type `n`, a morphism into `ℙ(n; S)`, a closed-immersion instance, and the
factorization through the structural projection.

The proof plan's recorded declarations were checked as follows. The projective-space
base-change dependency uses `AlgebraicGeometry.ProjectiveSpace.isPullback_map` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`; its signature gives the
cartesian square for every coordinate type and every `g : X ⟶ S`. The two closed
immersion dependencies use Mathlib's
`AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange` and the composition
instance `AlgebraicGeometry.IsClosedImmersion.comp` in
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`. The Segre dependency uses
`AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_segre` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre` and the finite-product
interface `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_pi` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product`. These are proof
imports or recorded Mathlib matches; they do not alter the item's statement.

The four proof clauses in the node are represented in the declaration docstring:
choose the two finite projective-space closed immersions; base-change the second
along the projective-space cartesian square; identify the iterated projective space
with the fibre product and compose the closed immersions; then compose with the
Segre closed immersion into one finite projective space. This is Stacks Project,
`morphisms.tex`, Tag 01WE, `lemma-H-projective-composition`.

Edge cases checked before writing include zero projective dimensions on either side,
empty source/intermediate/base schemes, arbitrary base schemes, and the empty finite
coordinate type allowed by the canonical H-projective class. The common scheme
universe is arbitrary and no extra size equality is imposed.

Searches for another declaration were made with the required tools:

- `msearch.py ... leanfinder "The composite of two H-projective morphisms of schemes is H-projective"` returned eight hits, all about proper, finite, universally closed, or universally open composition; no H-projective theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsHProjective.comp"` returned zero hits (`IsHProjective` unknown to Loogle).
- `msearch.py ... grep "IsHProjective|H-projective-composition" AlgebraicGeometry` returned zero hits.
- `rg` over the upstream `WeilConjectures` and project `lean/Sheaf`, plus
  `grep -rn "lem-trf-h-projective-composition"`, found the canonical class and
  related uses but no declaration of this composition statement. The source
  Projective module was read with `scompile.py --source`; it contains no such
  theorem.

No statement correction, new node, dependency repair, or `STATEMENT-DISPUTED` flag
is needed.

## Second reading by NA

I independently reread the target node, the copied module, and every recorded
statement dependency. The scheme binders, morphism directions, two H-projective
hypotheses, categorical composite order, and conclusion match the node exactly.
The docstring's four proof steps match the node's proof list and cite the same
base-change, closed-immersion, and Segre interfaces. The canonical dependency class
uses finite coordinate types as required. No mismatch or edge case omission was
found.
