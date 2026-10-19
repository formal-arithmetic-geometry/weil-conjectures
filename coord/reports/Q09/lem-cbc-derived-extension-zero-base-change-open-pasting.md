## Worker report

The module `Sheaf.AlgebraicGeometry.Etale.OpenImmersionBaseChangeOpenPasting` states
`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange_open_pasting`, with one
`sorry` and no auxiliary declaration or definition. The node changes only in `lean`.
The earlier Q02 delivery was the stage-1 proof split, not an existing Lean theorem:
the current node has no Lean record, and its report explicitly says no Lean was written.
This delivery uses that reviewed six-step split and does not restore the superseded split.

Source read: Stacks `etale-cohomology.tex`, Tag 03S6, label
`lemma-shriek-base-change`, statement and adjunction proof; current main-20261015
blueprint `sec-six-functors-basics/sk-prop-sf-cbc/` file
`cor-cbc-derived-extension-zero-base-change.proof.md`, final pasting clause.
The item is the underived open-immersion direction of that clause; its historical
identifier containing “derived” does not change its explicit underived statement.

Hypotheses and objects, clause by clause:

- The six schemes are `{V' V U' U X' X : Scheme.{u}}`; `k`, `j`, `k'`, `j'`
  have exactly the domains and codomains of the nested open immersions.
- The two pulled-back squares, their commuting maps `gV`, `gU`, `g`, and the
  chosen Cartesian identifications are exactly
  `sqk : OpenImmersionSquare gV k' k gU` and
  `sqj : OpenImmersionSquare gU j' j g`. All four open-immersion proofs are taken
  from these records, using explicit arguments. No additional instance hypothesis
  is imposed, in particular none on `g`, `gU`, or `gV`.
- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]`. This is the project's established small-etale module coefficient size.
  There is no nonzero-ring or nonempty-scheme restriction.
- The sheaf is `F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, so the
  actual category is constant-coefficient module sheaves on the small etale site.
- Every `b` is `(@asIso ... openImmersionLowerShriekBaseChangeMap ...
  isIso_openImmersionLowerShriekBaseChangeMap ...).inv.app` at the stated sheaf.
  The explicit isomorphism proof is the dependency's theorem on the actual square,
  reconstructed by `IsPullback.of_iso_pullback` from its chosen pullback data.
  This is the inverse of the upstream transformation, exactly the orientation
  fixed by the dependency node's Lean note. Its transpose is the existing
  `unit_map_openImmersionLowerShriekBaseChangeMap_app` formula; no arbitrary map
  replaces it.
- On the left, the first factor is `b^j` evaluated at `k_! F`. The second is
  the genuine functor `j'_!` applied to `b^k` at `F`. The third is
  `openImmersionLowerShriekComp ... k' j'` with `.inv.app` at `gV^* F`.
  Thus Lean's left-to-right `≫` is exactly the node's right-to-left written
  composite `c' ∘ j'_!(b^k) ∘ b^j`.
- On the right, `upperStar ... g` maps
  `(openImmersionLowerShriekComp ... k j).inv.app F`, giving `g^{-1}(c_F)`.
  The next factor is the inverse exchange for the composite square with
  vertical maps `k' ≫ j'` and `k ≫ j`. Its Cartesian proof is
  `(IsPullback.of_iso_pullback ... sqk ...).paste_vert
  (IsPullback.of_iso_pullback ... sqj ...)`; the open proofs are
  `IsOpenImmersion.comp` of the respective square fields.
  This is exactly `b^{j∘k} ∘ g^{-1}(c_F)`.
- Both sides are morphisms from `g^*(j_!(k_! F))` to
  `(k' ≫ j')_!(gV^* F)`. The existing exchange maps already include the square
  inverse-image composition identifications. No further identity, naturality,
  derived, or isomorphism clause was appended to the node's single equation.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`:
  `AlgebraicGeometry.OpenImmersionSquare`, including its inherited
  `ChosenCartesianSquare` data and all open-immersion fields.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`,
  `isIso_openImmersionLowerShriekBaseChangeMap`, and its unit equation
  `unit_map_openImmersionLowerShriekBaseChangeMap_app`. Read the full signatures
  and docstrings, and checked their elaborated types through scompile.py.
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekComp_coherence`; this imports
  the recorded canonical `openImmersionLowerShriekComp` from upstream
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp`.
  Its `.inv` is the node's comparison; the same comparison is used on both sides.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`:
  `AlgebraicGeometry.etaleInverseImageCompositionModuleLinear`. Its coefficient
  comparisons are the module-linear lifts used by the proof plan. The statement
  itself uses the canonical coefficient-valued `upperStar` API directly.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriekUpperStarAdjunction`, publicly
  imported through the existing composition/base-change modules; this is the
  recorded adjunction used to define both canonical maps, not a replacement.

The already-stated proof dependencies are imported through the above modules,
`Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`, and
`Mathlib.CategoryTheory.Adjunction.Mates`. The latter supplies `mateEquiv`,
`conjugateEquiv`, `Adjunction.comp`, `unit_conjugateEquiv_symm`,
`mateEquiv_hcomp`, and the conjugation/pasting laws of the Mathlib-match nodes.
The proof-only dependency `lem-cbc-open-inverse-image-restriction-composition`
has no Lean record or Mathlib match on the current base, so it has no module to
import yet. It is named explicitly in step 3 of the proof docstring; the current
stage-2 statement does not need a new declaration for it. No parent corollary is
imported, and no circular proof prerequisite is used.

Edge cases checked before writing: zero sheaf; zero coefficient ring; empty V;
empty U (hence V); empty X' (hence U' and V'); identity k, identity j, and identity
g. Every term is a functorial morphism and uses no chosen point, nonzero section,
or nonempty hypothesis. The equation becomes the unique zero comparison in the
zero cases and the canonical unit/naturality comparison in the identity cases.
For nontrivial nested opens, arbitrary g is still admitted. The finite-ring binder
is retained even though the categorical argument also works without finiteness.

Searches actually run (msearch.py, with stage-2 sandbox search log):

- LeanSearch: “extension by zero base change commutes with composition of open
  immersions”. Eight results include `LinearMap.baseChange_zero` and
  `Scheme.Modules.restrictFunctorComp_hom_app_app`; none states the small-etale
  extension-by-zero equation.
- Loogle: valid quoted `"mateEquiv_hcomp"`. Two results, the category and
  bicategory generic mate-pasting laws. These are reused through the existing
  Mathlib-match dependency, not treated as an exact geometric theorem.
- Mathlib grep: `openImmersionLowerShriek.*[Pp]ast|extension.?[Zz]ero.*[Cc]omp`.
  No matches.
- LeanFinder: “extension by zero base change compatible with composition of two
  open immersions”. Eight hits concern structural-module restriction or
  open-immersion section maps, not this theorem (initial tool-default log).
- Read-only rg of the source and side Lean trees for open/shriek pasting and
  base-change composition, and the exact blueprint identifier: no existing exact
  statement. `BaseChangeSquare` supplies exchange and its unit formula;
  `Comp` supplies the natural composition isomorphism, but neither states this
  compatibility. The similarly named ambient-map base-change composition theorem
  concerns successive base maps rather than composition of the open immersions.
- Exact proposed declaration-name search in Mathlib, upstream, and side Lean:
  no collision.

Validation: scompile.py compiled the final single module in both sandbox and
library modes without errors or warnings (1.8 s and 1.9 s reported). The initial
`#check` probes were removed. Every variable and universe is explicitly bound;
there are no local instances, private definitions, local notation, or statement
`let` binders. One named theorem, with the complete six-step natural-language
proof plan in its docstring, is postponed with `sorry` as required by stage 2.
No statement dispute, correction, new nodes, or dependency repairs are needed.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
