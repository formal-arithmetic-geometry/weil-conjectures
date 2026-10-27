## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleDiagonalComplementDegree` states
`AlgebraicGeometry.Scheme.Hom.affine_etale_diagonal_complement_degree`, with its
whole proof `sorry`. It introduces no definitions or auxiliary theorems. The item
node changes only in `lean`; no statement correction or new/dependency node is needed.

Source checked: `literature/stacks-project/spaces-morphisms.tex`, Tag 03XW,
`lemma-neighbourhood-scheme`, especially lines 10512–10545: bound one gives an
open immersion; the diagonal is open by unramifiedness, closed by separatedness,
and its affine complement has fibre bound n-1. The node's six proof steps are
included in the theorem docstring, including the additional explicit affine
coordinate calculation and arbitrary-field clauses.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`. The affine S-schemes are `{T T' :
  Scheme.{u}}`, `[IsAffine T]`, `[IsAffine T']`, with structure maps `t`, `t'`.
  `a : Over.mk t' ⟶ Over.mk t` is precisely an S-morphism; its underlying scheme
  morphism is `a.left`. Bundling supplies the compatibility with the structure
  maps without an extra hypothesis or a forgotten S-structure.
- Étaleness is `[Etale a.left]`, the recorded dependency's Mathlib class.
- The integer n≥1 is `(n : ℕ) (hn : 1 ≤ n)`; the fibre-degree hypothesis is
  `ha : BoundsFiberDegrees a.left n`. The actual recorded definition includes
  finiteness and the dimension bound on every residue-field fibre, not merely
  cardinality of its point set.
- T'' is Mathlib's chosen `pullback a.left a.left`; the projections are
  `pullback.fst` and `pullback.snd`; δ is `pullback.diagonal a.left`.
- The first two conjuncts state `IsOpenImmersion` and `IsClosedImmersion` for δ.
  An open immersion identifies its source with the open subscheme of its image,
  so no separate noncanonical diagonal subscheme is introduced.
- The existential `U : (pullback a.left a.left).Opens` is the complementary open
  subscheme. Its carrier equals `(Set.range (pullback.diagonal a.left))ᶜ`.
  Its inclusion `U.ι` is automatically an open immersion, and the conclusion
  explicitly gives `IsClosedImmersion U.ι` and `IsAffine U.toScheme`.
- The restricted map b is literally `U.ι ≫ pullback.snd a.left a.left`.
  The next conjuncts give `Etale b` and `BoundsFiberDegrees b (n - 1)`.
- The quantified `(K : Type u) [Field K]` and `g : Spec (CommRingCat.of K) ⟶ T'`
  cover arbitrary field-valued points in the scheme universe, not just closed,
  geometric, or residue-field points. There is no independent smaller field
  universe that could make these tests vacuous. The whole declaration is
  universe-polymorphic.
- The complementary fibre is exactly `pullback b g`; its coordinate ring C is
  `Γ(pullback b g, ⊤)`. `IsFinite (pullback.snd b g)` gives finiteness over K;
  `(pullback.snd b g).finrankΓ ≤ n - 1` is dim_K C≤n-1 with precisely the
  structure induced by the second projection. The existing `finrankΓ` uses
  the existing `Scheme.Hom.ΓAlgebra` definition internally.
- The full fibre is `pullback (pullback.snd a.left a.left) g`. The existential
  maps s and j are characterized by both their projections: s has first
  projection `g ≫ δ` and second projection the identity; j has first projection
  the complementary fibre's first projection followed by `U.ι`, and second
  projection its structure map. Pullback uniqueness therefore specifies the
  canonical diagonal section and canonical complementary-fibre inclusion.
  `IsIso (coprod.desc s j)` says exactly that these pieces give the disjoint
  union Spec K ⨿ fibre(b), including their specified embeddings.
- The ring equivalence e has source the full fibre's global sections and target
  `K × Γ(pullback b g, ⊤)`. Its equation on EVERY section specifies it as the
  restriction map: the first restriction is s.appTop followed by ΓSpecIso.hom,
  and the second is j.appTop. This is an explicit presentation of the claimed
  K-algebra equivalence: the projection equations for s and j imply that the
  scalar k maps to `(k, algebraMap K C k)`. Thus the statement specifies the
  algebra structure and the correct restriction map without choosing a new
  Algebra instance, leaving an action unspecified, or asserting only an
  unrelated abstract ring equivalence. The projection equations and ring-map
  equation are the expanded algebra-compatibility condition.
- Finally `n = 1 → IsEmpty U.toScheme ∧ IsOpenImmersion a.left` gives both
  assertions in the node's last sentence for this very complement U.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Spec`/`Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.FiberDegreeBound`:
  `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegrees`. Its upstream dependency
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` supplies `ΓAlgebra`
  and `finrankΓ`; both definitions and their induced scalar map were read.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and the
  scheme pullbacks supplied by Mathlib's algebraic-geometry imports.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Limits` supplies the scheme coproduct and its
  disjoint-union interpretation. `Scheme.ΓSpecIso` is the canonical spectrum
  global-sections identification. These are existing Mathlib notions.

The statement-dependency modules are public imports. Proof-only imports follow
all already stated proof dependencies: UnramifiedMorphism (`IsUnramified`),
FiniteFiberDegreeBaseChange (`finite_fiber_degree_pullback` and
`boundsFiberDegrees_pullback_snd`), BoundsFiberDegreesFieldPoints
(`boundsFiberDegrees_iff_fieldPoints`), Gluing
(`IsOpenImmersion.of_etale_of_universallyInjective`), Proper (`IsProper`, with
`IsSeparated`), Limits.MorphismProperty (finite-limit preservation under étale
base change), and Prime.Topology (the clopen/idempotent correspondence).
Mathlib's affine pullback, finite morphism, separatedness, universally injective,
open restriction and localization declarations are available through these
imports. No dependency with a usable recorded declaration is restated.

Edge cases checked mathematically:

- T' empty: the diagonal and complement are empty; there are no maps from a
  field spectrum to T', and the bound-one conclusion remains valid.
- An open immersion that is not finite: the self-product is the diagonal,
  U is empty, C is the zero ring, and K×C≅K. No finiteness of a is assumed.
- Spec(k×k)→Spec k at n=2: the off-diagonal complement has degree one;
  the field fibre is K ⨿ Spec K and its ring is K×K.
- n=1: zero-dimensional finite K-algebra C is the zero ring, with empty
  spectrum, so the concluding emptiness clause is correct. n=0 is excluded
  explicitly, just as the item requires; n need not be the minimal bound.
- Positive characteristic, non-algebraically-closed fields, and inseparable
  test extensions are allowed. No connectedness or surjectivity is assumed.

Searches made before writing:

- `msearch.py Q42 lem-a1-affine-etale-diagonal-complement-degree leanfinder
  "For an affine etale morphism with fibre degrees bounded by n the complement
  of its diagonal is affine etale and has fibre degrees bounded by n minus one"`:
  eight hits, chiefly AffineTargetMorphismProperty/HasAffineProperty diagonal
  facts and `FormallyUnramified.isOpenImmersion_diagonal`; no complete match.
- `msearch.py ... loogle '"IsEtale", "diagonal"'`: successful search, zero hits.
- `msearch.py ... grep 'diagonal.*[Cc]ompl|[Cc]ompl.*diagonal|BoundsFiberDegrees'
  AlgebraicGeometry`: successful search, zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for diagonal/complement names
  and for the proposed declaration, plus `grep -rn` for the item's blueprint
  id under WeilConjectures: no existing statement of this node. The space-level
  `SpaceSeparatedEtaleDiagonalComplement` has different objects and conclusions;
  the upstream `fiberDegree_of_isCompl` supplies additivity, not this complete
  affine-complement theorem. Its signature was read and it is not duplicated.
- `rg` on `dag/lean_names_upstream.json` for the proposed module/declaration:
  no collision. No independent new notion was needed, so no new-node searches
  or definition nodes were necessary.

Validation: scompile.py compiled the sandbox module and the intended library
module cleanly; an initial scheme/type coercion ambiguity in the carrier-set
annotation was fixed by writing `(pullback a.left a.left : Scheme.{u})`.
All variables and universes are explicitly bound, with `autoImplicit false`.
There are no diagnostic commands, extra axioms, or proved auxiliary lemmas.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q42

Worker self-check with the node and completed module open (no separate agent was
started, as required by the dispatcher; independent review belongs to the
maintainer). Rechecked the six statement dependencies, the Over direction
T'→T, the second rather than first projection in b, the carrier complement,
the same complement in the n=1 clause, and both universal properties fixing
s and j. Rechecked the direction of ΓSpecIso.hom: global sections of Spec K
map to K. The ring equivalence is explicitly the two restriction maps, so it
cannot silently use a wrong field action. No mathematical mismatch found;
the only elaboration repair was the explicit Scheme annotation described above.
