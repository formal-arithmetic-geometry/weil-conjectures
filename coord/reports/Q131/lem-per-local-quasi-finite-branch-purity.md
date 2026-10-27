## Worker report

The module `Sheaf.AlgebraicGeometry.LocalQuasiFiniteBranchPurity` states
`AlgebraicGeometry.exists_etale_neighborhood_of_unramified_codimension_one`.
Its only proof is `by sorry`. No definitions, new nodes, dependency repairs, or
statement corrections are supplied. The original node agrees with the five
hypotheses and conclusion of `literature/stacks-project/pione.tex`, Tag 0BMB,
Lemma `purity`, read directly at lines 5144–5164. The theorem docstring gives
all thirteen steps of the node's proof, including the dimension-one base case,
the generic point in the induction, localization identifications, and descent.

Clause-by-clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`.
- Both schemes locally Noetherian: `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian Y]`, with no global Noetherianity assumption.
- Specified point and its image: `(x : X)` and the literal point `f x`.
- The local source ring is a normal domain: `[IsDomain (X.presheaf.stalk x)]`
  and `[IsIntegrallyClosed (X.presheaf.stalk x)]`. These are exactly the normal
  domain conjunction prescribed by the dependency record, supplied as instances.
- The target local ring is regular local:
  `[IsRegularLocalRing (Y.presheaf.stalk (f x))]`; this includes the Noetherian
  local ring requirements. No regularity assumption elsewhere on Y is added.
- Quasi-finiteness at x: `hqf : f.IsQuasiFiniteAtPoint x`, using the recorded
  upstream Stacks predicate, including its local finite-type condition.
- Equal local dimensions: `hdim` is the literal equality of the two
  `ringKrullDim` values; these take values in `WithBot ℕ∞`.
- Their common dimension is at least one: `hpos` compares one with the source
  dimension; by `hdim` this is exactly the same comparison on the target.
- The codimension-one hypothesis ranges over every `x' : X` such that
  `x ∈ closure ({x'} : Set X)` and `ringKrullDim (X.presheaf.stalk x') = 1`.
  The closure condition is precisely that x' specializes to x. It then gives
  `∃ U : X.Opens, x' ∈ U ∧ IsUnramified (U.ι ≫ f)`.
- The conclusion is exactly `∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)`;
  the neighbourhood restricts the source and retains the original target.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, and `Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` from Mathlib's ring definitions, as the normal-domain
  conjunction prescribed by `def-weil-pbc-normal-ring`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: imports the shared regular-ring
  API; the ring clause of `def-weil-regular-scheme` is the recorded Mathlib
  `IsRegularLocalRing`, whose full definition in
  `Mathlib.RingTheory.RegularLocalRing.Defs` was read. `IsRegularScheme` itself
  is not imposed, since the node assumes only one regular stalk.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, with its full affine
  neighbourhood definition and docstring read.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  defined as locally finite type and open-immersion diagonal.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.

Statement dependencies have public imports. Stated proof dependencies have
plain imports, including their Mathlib matches; these imports record the
stage-3 proof plan. `lem-sfb-etale-stalk-invariants` has no Lean declaration,
Mathlib match or closed upstream audit, so it has no module to import yet.
It is used only by the future proof and supplies no part of this signature.

Edge cases checked before writing:

- Empty X admits no x, so the statement imposes nothing there. Empty Y admits
  no morphism from a source with the specified point; no nonempty scheme
  hypotheses are added.
- A zero source stalk is excluded by normal-domain `IsDomain`, exactly as
  in the node. Dimension zero is explicitly excluded by the stated `hpos`.
- When the common dimension is one, x itself is among the x' in `hunram`
  because x lies in its own singleton closure. Thus the dimension-one case
  requires unramifiedness at x and is not vacuous.
- In dimension at least two the quantified points are generalizations of x,
  not its specializations. The conclusion need not hold globally on X.
- All scheme universes are the single explicit `u`; all point and open types
  are the actual types attached to those schemes. `autoImplicit` is false.
- No separatedness, finite global morphism, regularity of all Y, normality of
  all X, characteristic condition, or extra finite-presentation assumption is
  added. No statement fault or unresolved dispute was found.

Searches performed for an existing statement:

- `msearch.py ... leanfinder` with query “Purity of the branch locus: a
  quasi-finite morphism from a normal local ring to a regular local ring with
  equal positive dimension, unramified in codimension one, is etale at the
  point”: eight hits, including `Algebra.IsEtaleAt`, `Algebra.etaleLocus` and
  `Algebra.unramifiedLocus`; none states branch-locus purity.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`:
  no hits; the endpoint does not index the project predicate.
- `msearch.py ... leansearch` with query “purity branch locus normal regular
  quasi finite unramified etale”: eight hits for etale/unramified definitions
  and elementary equivalences, none stating the result.
- `msearch.py ... grep 'purity|branch.?locus' AlgebraicGeometry`: zero Mathlib hits.
- `rg` over both project Lean roots for `purity|branch.?[Ll]ocus` found
  unrelated purity constructions and the punctured-spectrum input, but no
  instance of the desired local branch-locus theorem. A focused full-root
  search for `0BMB|[Pp]urity of branch|branch[Ll]ocus|branch_locus|etaleAt_of|etale_at_of`
  found no hits. Searching the item ID in `lean/WeilConjectures` also found none.
- The proposed theorem names were checked against Mathlib, both project roots,
  and `dag/lean_names_upstream.json`: no conflicting declaration.

Validation: `scompile.py Q131 lem-per-local-quasi-finite-branch-purity` on the
single delivered module succeeded in sandbox mode (12.2 s) and its real module
mode (2.3 s), with no errors or unexpected warnings. The stage-2 dry run and
push are run after this report is written.

## Second reading by Q131

The dispatcher explicitly forbids starting other agents, so this section records
a second pass by the same worker; it does not claim an independent reviewer.
The maintainer's independent delivery review remains required. Re-read the
source lemma, original JSON statement and delivered signature together. All
five source assumptions match as detailed above: both local-Noetherian classes,
normal source stalk, regular target stalk, local quasi-finiteness, equal positive
Krull dimension, and all height-one generalizations with their unramified
neighbourhoods. The conclusion uses the original f on an open containing x.
Checked in particular that the closure direction is x in closure of {x'}, that
`hunram` does not require x' distinct from x, that the normal-domain conjunction
is complete, and that no global morphism condition replaces the at-point
hypothesis. No mismatch was found or changed on this pass. There are no new
nodes or dependency modules to review.
