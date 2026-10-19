## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness` states
`AlgebraicGeometry.Etale.proper_directImage_finiteness`, with its sole proof `sorry`.
The statement is unchanged. No new definition nodes or dependency modules are needed.

Hypothesis-by-hypothesis and clause-by-clause reading:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Noetherian, meaning finite affine covers by Noetherian spectra:
  `[IsNoetherian X] [IsNoetherian Y]`. Mathlib's
  `isNoetherian_iff_of_finite_affine_openCover` identifies this class with precisely the
  node's description. It does not merely assert that the underlying space is Noetherian.
- Finite dimensionality of each underlying space: `hXdim` and `hYdim` assert
  `∃ d : ℕ, topologicalKrullDim ... ≤ (d : WithBot ℕ∞)` independently for X and Y.
- Proper morphism: `(f : X ⟶ Y) [IsProper f]`, the Mathlib properness class collected by
  the scheme-conventions dependency.
- Nonnegative fibre-dimension bound: `(e : ℕ)` and `hfib` for every point `y : Y`.
  `pullback f (Y.algClosurePoint y)` is the geometric fibre over the algebraic closure of
  the residue field at y, exactly the geometric-fibre convention in the dependency.
  The explicit `↥` makes the topological underlying type of the scheme unambiguous.
- Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- Element orders invertible in every local ring of Y: `hΛ` is
  `∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y)`.
  Orders are additive orders, as appropriate for torsion coefficients. No algebra
  structure relating Λ to a stalk ring is imposed.
- F a constructible sheaf of Λ-modules on the small etale site of X:
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
  `hF : Scheme.IsConstructibleEtaleModuleSheaf F`.
- Constructibility for every integer q ≥ 0: the first conjunct is
  `∀ q : ℤ, 0 ≤ q → Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f q F)`.
- Vanishing for every q > 2e: the second conjunct is
  `∀ q : ℤ, (2 * e : ℤ) < q → IsZero (higherDirectImage Λ f q F)`.
  The integer expression casts e before multiplication. Since e is nonnegative, this
  range already consists of positive degrees. `IsZero` says that the module SHEAF is
  zero, not that an unstructured type is zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the Noetherian-ring notion
  underlying Mathlib's `AlgebraicGeometry.IsNoetherian` in
  `Mathlib.AlgebraicGeometry.Noetherian`. Its finite-affine-cover equivalence was read.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, the supremum of irreducible
  closed chain lengths, with values in `WithBot ℕ∞`.
- The conventions dependency has no declaration of its own. Properness uses
  `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`;
  geometric fibres use `CategoryTheory.Limits.pullback` and
  `Scheme.algClosurePoint` from `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, with its actual finite
  stratification, constructible parts and finite locally constant module restrictions.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`. The dependency also records
  `rightDerivedLowerStarPlus`, whose actual source is
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
  No replacement definition was introduced: the existing `Etale.higherDirectImage`
  in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` is exactly homology
  of this bounded-below derived direct image at F placed in degree zero. Its full
  definition and docstring were read.

The stated proof dependencies are imported, including the newly available geometric-fibre
formula and torsion cohomological-dimension modules. Two proof dependencies currently have
no declaration to import: `lem-weil-pbc-etale-compactification-constructibility` and
`thm-sc-finite-type-torsion-cd`. Neither is needed to state the theorem. The declaration
docstring includes all six proof steps and names their inputs, including these two nodes.

Source check: read the local Stacks source `etale-cohomology.tex`, label
`lemma-cohomological-dimension-proper` (Tag 095U), and `more-etale.tex`, label
`theorem-constructible-shriek` (Tag 0GL0). The first proves the vanishing bound even
for arbitrary torsion abelian sheaves; the second gives constructibility using identity
compactification for a proper map. The node retains its specified extra hypotheses.

Edge cases checked: X or Y empty are permitted; dimensions use bottom for the empty
space, and `hfib` is vacuous on empty Y. Empty fibres also satisfy the bound. e = 0
asserts vanishing exactly in positive degrees. q = 0 is included in constructibility;
q = 2e is not forced to vanish. There is no Nontrivial assumption on Λ: in the zero
ring every additive element has order one, so the invertibility condition is valid and
all module sheaves are zero. Finite Λ excludes elements of infinite additive order;
zero itself has additive order one. Dimension infinity is correctly excluded by the
finite-dimensional hypotheses. Schemes use arbitrary universe u; coefficient modules
use the existing dependency's Type (u + 1) convention, with no extra smallness condition.

Searches performed:

- `msearch.py ... leanfinder "Proper pushforward of a constructible torsion etale sheaf
  has constructible higher direct images and vanishes above twice the dimension of
  geometric fibers"`: eight hits on constructible subset images, ordinary pushforward,
  affine limits and etale morphism properties; no matching theorem.
- `msearch.py ... loogle '"constructible", "sheaf"'`: zero hits.
- `msearch.py ... grep 'higherDirectImage|directImage.*constructib|constructib.*directImage'`
  at the correctly rooted Mathlib source: zero hits.
- `msearch.py ... leansearch "Higher direct images of constructible finite coefficient
  etale sheaves under proper morphisms are constructible and vanish in high degrees"`:
  unavailable, Internal Server Error; this is not treated as evidence of absence.
- `rg` on upstream `WeilConjectures` and project `lean/Sheaf` for
  `rightDerivedLowerStarPlus`, `higherDirectImage`, proper/constructible combinations,
  dimension-of-fibre expressions and the proposed declaration name: found the existing
  higher-direct-image construction, the geometric-fibre formula, and general finiteness
  statements over fields. Read `SixFunctors/Etale/Derived/Finiteness/DirectImage.lean`:
  its declarations assume finite type over a field and use compact support or bounded
  derived constructibility, so none has this node's hypotheses and two conclusions.
  Read the project's `ConstructibleHigherDirectImage.lean`: this only DEFINES a property,
  has no vanishing assertion, and is not a theorem proving this node.
- Searched upstream by the exact node id: no hits. Checked the upstream names inventory
  and both source roots for `proper_directImage_finiteness`: no clash.

Validation: `scompile.py NB lem-weil-pbc-etale-proper-direct-image-finiteness` compiles
this delivered file cleanly on the server, nice 19, two threads, 60 seconds per file.
The corrected elaboration explicitly coerces the geometric-fibre scheme to its point type.
No mathematical statement correction or disputed assertion is needed.


## Second reading by NB

Independently read the sandbox node and theorem, all six statement dependency records,
and the actual source declarations. No mathematical or Lean repair was needed; the
second reading changes only this report. There are no new definition nodes, dependency
modules, or statement corrections in this delivery.

The statement inventory and its Lean rendering, in the order of the node:

1. Two arbitrary schemes X and Y: `{X Y : Scheme.{u}}`. PASS: the Mathlib scheme and
   morphism category recorded by `def-pc-scheme`, with arbitrary universe u.
2. Each admits a finite affine cover by Noetherian rings: `[IsNoetherian X]
   [IsNoetherian Y]`. PASS: read Mathlib's class (locally Noetherian and compact) and
   `isNoetherian_iff_of_finite_affine_openCover`, whose ring condition is the recorded
   `IsNoetherianRing`, not merely a Noetherian topological space.
3. Each underlying space has dimension bounded by some nonnegative integer:
   `hXdim : ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)` and the corresponding
   `hYdim`. PASS: separate bounds, not a common preselected dimension or dimension
   equality. Read `topologicalKrullDim`, defined by chains of irreducible closed sets.
4. A proper morphism: `(f : X ⟶ Y) [IsProper f]`. PASS: read the Mathlib class,
   extending separatedness, universal closedness and locally finite type; universal
   closedness supplies quasi-compactness. This is the convention node's properness.
5. A nonnegative integer fibre bound: `(e : ℕ)`, with `hfib : ∀ y : Y,
   topologicalKrullDim ↥(pullback f (Y.algClosurePoint y)) ≤ (e : WithBot ℕ∞)`.
   PASS: read `Scheme.algClosurePoint`, the morphism from Spec of the algebraic
   closure of the residue field at y. The pullback is exactly the convention node's
   geometric fibre. This quantifies over all points, not only closed points, and
   measures the underlying fibre scheme, not the set of geometric lifts.
6. A finite commutative ring: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. PASS:
   finite underlying set, without a field, domain, or nontriviality assumption.
7. Its element orders are invertible in every local ring of Y:
   `hΛ : ∀ (a : Λ) (y : Y), IsUnit (addOrderOf a : Y.presheaf.stalk y)`.
   PASS: additive orders mapped from natural numbers to the actual local rings;
   no coefficient-algebra structure or restriction to a fixed characteristic.
8. Any constructible module sheaf F on the small etale site of X:
   `(F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
   `(hF : Scheme.IsConstructibleEtaleModuleSheaf F)`. PASS: opened the dependency
   module. Its real definition chooses a finite locally closed stratification with
   constructible parts, pulls back by `Etale.upperStar`, and requires etale
   trivializations by finite constant module values. It is the node's precise
   constructibility notion, not globally locally constant or the alternate upstream
   constructibility class. Module-valued sheaves give constant-ring module sheaves.
9. Every nonnegative integer higher direct image is constructible: the first
   conjunct quantifies `∀ q : ℤ, 0 ≤ q →` and applies the same constructibility
   definition to `higherDirectImage Λ f q F`. PASS: opened the upstream definition
   in SmoothBaseChange.Defs; it is homology in degree q of the bounded below right
   derived `Etale.lowerStar` of F in degree zero. Read lowerStar's objectwise
   base-change formula and rightDerivedLowerStarPlus's definition as
   `rightDerivedFunctorPlus`. No substitute pushforward is introduced.
10. Every degree above 2e vanishes: the second conjunct is
    `∀ q : ℤ, (2 * e : ℤ) < q → IsZero (higherDirectImage Λ f q F)`.
    PASS: the same higher direct image, zero in its module-sheaf category; no
    sectionwise finiteness conclusion substituted, no boundary degree added.

Source comparison: opened etale-cohomology.tex at
`lemma-cohomological-dimension-proper` (095U). It states properness, a fibre dimension
bound, and vanishing above twice that bound for torsion abelian sheaves, with no
hidden field or Noetherian hypothesis on the base. Opened more-etale.tex at
`theorem-constructible-shriek` (0GL0): separated finite presentation between qcqs
schemes, Noetherian coefficients, and bounded below torsion constructible input.
The node's finite Noetherian covers and properness provide these hypotheses;
finite coefficients supply Noetherianity and torsion. For the proper map use the
identity compactification. The Lean retains exactly the node's stated additional
finite-dimensionality and coefficient-invertibility assumptions. The six numbered
docstring proof steps follow the six node steps and cite their inputs.

Edge cases: empty X and empty Y remain allowed (no Nonempty instances); dimension
of the empty space is bottom, and the fibre condition is vacuous for empty Y.
Empty geometric fibres satisfy hfib. For e = 0 only positive degrees must vanish.
Degree zero is included in constructibility; degree 2e is not forced to vanish.
Negative degrees are not separately claimed. The zero ring and zero sheaf are
allowed; additive order of zero is one, which is invertible. No characteristic is
excluded beyond the explicit invertibility hypothesis. The arbitrary scheme
universe u and coefficient/module universe u+1 are exactly the dependency's site
encoding; finite coefficients introduce no further size restriction. Every variable
and universe appearing in the signature is bound.

Independent searches (2026-10-15): ran msearch LeanFinder with
“For proper morphisms higher direct images of finite locally constant stratified
module sheaves are constructible, with cohomological dimension bounded by twice
fibre dimension”. Eight hits concerned condensed modules and constructible images
of subsets; none states this theorem. Ran Loogle with `"higherDirectImage"`: zero
hits. Ran rg on Mathlib's AlgebraicGeometry and CategoryTheory, upstream
WeilConjectures, and project lean/Sheaf, using proper/constructible combinations,
`higherDirectImage`, and cohomological-dimension/proper terms. Opened upstream
SixFunctors/Etale/Derived/Finiteness/DirectImage.lean: its finiteness/vanishing
statements require finite-type schemes over a field and/or compact-support derived
images, so do not match this general-base statement. Opened project
ConstructibleHigherDirectImage.lean: it defines a property and proves neither the
constructibility nor the vanishing conclusion. The exact proposed declaration
name has no occurrence in either source library or the upstream names inventory.
The existing higher-direct-image construction is reused. No duplicate statement
or missing notion was found.

H5/H6/H8/H9 check: no new definitions, no hollow data, and the only theorem proof
is `sorry`. Source and blueprint docstrings are present, with the node proof in
six steps. No private definitions, local notation/instances, hidden let/show
binders, or unbound names occur in the signature. The node's lean.statement was
checked programmatically to be verbatim the file signature. The server-only
scompile.py run compiled the delivered file cleanly (2.9 seconds), with its three
side-import overlay modules also clean; nice 19, two threads, 60 seconds per file.
An initial invocation from the repository used an absent relative sandbox path;
rerunning from the sandbox succeeded, without any local compiler invocation.
