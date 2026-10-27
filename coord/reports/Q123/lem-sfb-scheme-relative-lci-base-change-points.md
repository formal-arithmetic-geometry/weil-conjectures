## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeRelativeLciBaseChangePoints` states
`AlgebraicGeometry.scheme_relative_lci_base_change_points`, with its entire proof
postponed by `sorry`. It defines no new notion. Source read in full: Stacks Project,
more-morphisms.tex, `definition-lci` (Tag 069F) and
`lemma-base-change-lci-fibres` (Tag 06B8), including the complete proof.

Clause-by-clause correspondence:

- Schemes B, X, Y: `{B X Y : Scheme.{u}}`; arbitrary scheme T:
  `{T : Scheme.{u}}`. The universe is arbitrary, with the standard common scheme
  universe; no finiteness or nonemptiness of any underlying space is imposed.
- Structural maps and relative map: `p : X ⟶ B`, `q : Y ⟶ B`, `f : X ⟶ Y`.
  The equality q composed with f equals p is `h : p = f ≫ q`.
- Flatness of the two families: `[Flat p] [Flat q]`.
- Local finite presentation of the two families:
  `[LocallyOfFinitePresentation p] [LocallyOfFinitePresentation q]`.
- The node's local complete intersection convention is exactly the existing
  `RelativeFiniteHilbert.SchemeLci`: for every source point an open neighbourhood
  factors as `i ≫ q`, with `IsClosedImmersion i`, `Smooth q`, and
  `CotangentPresentation.IsKoszulImmersion i`. The latter asks for local finite
  generators `a : Fin r → Γ(P,W)` of `i.ker.ideal W` satisfying
  `RingTheory.Sequence.IsKoszulRegular a`; `r = 0` is permitted.
- Koszul at a source point is the node's stated open-neighbourhood condition:
  `∃ U, x ∈ U ∧ RelativeFiniteHilbert.SchemeLci (U.ι ≫ f)`.
  It is expanded in the theorem, rather than given another definition.
- Arbitrary parameter change: `g : T ⟶ B`, without extra hypotheses.
- X_T and Y_T are the canonical `pullback p g` and `pullback q g`.
  Their induced arrow is `pullback.map p g q g f (𝟙 T) (𝟙 B) ... ...`.
  Its two proof arguments are precisely the given structural equality and the
  identity compatibility; they do not introduce assumptions or arbitrary maps.
- The universal source point is `xT : (pullback p g : Scheme.{u})`.
- Projection to X is `(pullback.fst p g) xT`.
- The conclusion is the requested `↔`: existence of an lci open neighbourhood
  of xT upstairs if and only if existence of one around its projection downstairs.
- No hypothesis is made on f being flat or on g being flat; there is no separation,
  quasi-compactness, Noetherian or nonemptiness binder.

Dependency declarations, with their signatures and docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (equivalent to stalk flatness by `Flat.iff_flat_stalkMap`).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegularOn`, `IsH1RegularOn`, `IsKoszulRegular`,
  `IsH1Regular`; the third is used by the existing closed-chart predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`;
  schemes have the required pullbacks through `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids`:
  `AlgebraicGeometry.RelativeFiniteHilbert.SchemeLci`; its owner
  `def-sfb-relative-finite-hilbert-groupoids` is already landed and was added to
  stmt_deps under the explicit landed-node rule. Its defining closed-chart notion
  is `AlgebraicGeometry.CotangentPresentation.IsKoszulImmersion` from
  `Sheaf.AlgebraicGeometry.LciCotangentPresentation`, read in full.

The private imports include all currently available proof-dependency modules,
including the finite-presentation cancellation, affine-space smoothness, relative
H1-regularity base change, pointwise flatness, field-extension reflection, flat
quotient fibre lifting, and regular-to-Koszul comparison modules. The two newly
split proof dependencies `lem-sfb-koszul-immersion-smooth-ambient-independence` and
`lem-sfb-koszul-closed-immersion-affine-criterion` currently have no recorded
module, so no import can yet be added for them. The recorded module for
`lem-per-noetherian-local-koszul-criterion` was withdrawn: its lean.note says it was
deleted as unreachable on 2026-10-20, and `scompile.py --source
Sheaf.RingTheory.NoetherianLocalKoszulCriterion` confirms source unavailable. This
is only a future proof dependency, not needed for the statement; its node is
cited in the complete six-step proof docstring. No dependency statement is copied.

Edge cases checked before writing:

- Empty X_T: there is no xT, so no nonempty condition is needed.
- Empty X or empty T implies the same vacuous case. Empty Y admits a map from X
  only when X is empty, again correctly covered.
- Empty Koszul generators: the existing `Fin r` predicate permits r = 0 and
  the zero ideal, so smooth maps are included.
- Identity parameter change and identity relative map are both covered, with
  canonical induced arrows and the expected point neighbourhoods.
- Nonflat parameter changes are allowed. For example the nonflat relative map
  `Spec ℤ → 𝔸¹_ℤ` given by the zero section is allowed while both families are flat
  and finitely presented over `Spec ℤ`; reduction modulo a prime is an allowed g.
- Inseparable field extensions, non-Noetherian base rings, and non-separated or
  non-quasi-compact schemes are not excluded by any binder.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "For a morphism between flat locally finitely
  presented schemes over a base, its local complete intersection locus commutes
  with arbitrary base change". Eight hits: flat/smooth/lfp stability, universal
  openness, and related results; none is this pointwise lci equivalence.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsKoszulAt,
  AlgebraicGeometry.IsLocalCompleteIntersection`. Zero hits; the first identifier
  is unknown.
- `msearch.py ... grep`: `IsKoszul|[Ll]ocalCompleteIntersection|[Ll]ciLocus`,
  restricted to Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch`: "The Koszul locus of a map between flat locally
  finitely presented schemes commutes with arbitrary base change". Eight hits
  concern flatness, smoothness and differentials; none is the statement.
- `rg` in `lean/WeilConjectures` for `Koszul at a point|SchemeLci|[Kk]oszul[Aa]t|
  [Ll]ciAt|relative.*lci.*base.*change`, and the exact item id: no hits.
- `rg` in `lean/Sheaf` for the Koszul/lci names finds the exact reusable
  `RelativeFiniteHilbert.SchemeLci` and its applications, but no base-change
  equivalence for source points. `IsKoszulRegularImmersionNear` is about immersions,
  not an arbitrary map to a smooth ambient, so it is not the requested predicate.
- `rg` of `dag/nodes` for SchemeLci and Koszul-at-a-point text finds the existing
  owning definition node and the consumer source-locus node. A parsed dependency
  traversal finds no path from the SchemeLci owner back to this item, so adding
  the owning definition is acyclic.

No statement correction, new node, disputed statement, or dependency repair is
needed. The expected single `sorry` is the only postponed declaration in this file.

## Second reading by Q123

I reread the node and the final theorem together, separately from drafting; no
additional agent was started, as explicitly required by the dispatcher brief.
The maintainer supplies the independent review. The structural equality has the
correct direction after reversing qf=p into p=f≫q. Both and only the structural
maps have Flat and LocallyOfFinitePresentation assumptions. In `pullback.map` the
first arrow is f, the second is the identity of T, and the base arrow is the
identity of B; its codomain is therefore Y_T, as required. The left neighbourhood
contains xT and the right contains its first-projection image. Both restrictions
use the same existing SchemeLci predicate. Its closed-chart generators generate
the actual kernel ideal and use Koszul homology vanishing, rather than the
stronger ordinary regular-sequence condition. Length zero is allowed. Neither
direction of the equivalence nor any edge case was lost. No mismatch was found
and no statement was changed during this rereading.
