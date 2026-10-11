## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve` defines
`AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`. Its parameter `f : X ⟶
Spec (.of k)` is the structure morphism of the `k`-scheme `X`, with `k` a field.
The class extends `f.IsCurveOverField`, rendering the node's curve hypothesis
(integral, separated and of finite type over `k`, dimension exactly one),
`Smooth f`, rendering smoothness of the structure morphism, and `IsProjective f`,
rendering projectivity in the H-projective plus quasi-compact convention. Thus
all three clauses of the node statement are represented directly, with no extra
hypotheses or conclusions.

Dependencies used:

* `def-pc-curve`: `AlgebraicGeometry.Scheme.Hom.IsCurveOverField` from
  `Sheaf.AlgebraicGeometry.Variety`.
* `def-pc-projective-morphism`: `AlgebraicGeometry.IsProjective` from
  `Sheaf.AlgebraicGeometry.Morphisms.Projective`.
* `def-sbc-smooth-morphisms`: Mathlib's `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

Edge cases checked: the field is arbitrary (including positive characteristic),
`k` and `X` share an explicit universe, and the class formulation imposes no
nonemptiness condition, so the stated structure is represented without adding
an assumption beyond the node. The relative-dimension and etale clauses of the
smooth-morphism dependency are not imported into this definition because the
node asks only for smoothness.

Searches made: `msearch.py ... leanfinder "smooth projective curve over a field,
scheme morphism"` returned only Weierstrass-curve declarations, which are not
scheme morphisms; `msearch.py ... loogle "Smooth, IsProjective, IsCurveOverField"`
returned no hit; `msearch.py ... grep "SmoothProjectiveCurve|IsSmoothProjectiveCurve"
AlgebraicGeometry` returned no hit. Repository and Mathlib searches likewise found
no declaration of this combined notion. The dependency declarations were read in
`Sheaf.AlgebraicGeometry.Variety` and
`Sheaf.AlgebraicGeometry.Morphisms.Projective`; the smooth declaration is the
Mathlib class documented as the affine-local smooth morphism notion.

## Earlier second reading (a previous round; superseded)

The declaration signature was checked against the node clause by clause. The
three inherited classes are exactly the three recorded dependencies, and the
explicit structure morphism parameter prevents an unrelated morphism from being
used. No statement correction or extra dependency is required.

## Second reading by H1

Read the delivered node and all three dependency nodes and declarations. Source:
Stacks `varieties.tex`, `definition-variety` (020D), lines 53–59, and
`definition-curve` (0A23), lines 9168–9172; `pic.tex`, section
`section-picard-curve` and `lemma-check-conditions` (0B9U), lines 920–951.
The local literature copies are `/home/ubuntu/c1-stacks-review/varieties.tex`
and `/home/ubuntu/c1-stacks-review/pic.tex`; the paths recorded in the node
are not installed in this clone. Also read the official Stacks pages
https://stacks.math.columbia.edu/tag/01W8,
https://stacks.math.columbia.edu/tag/01V5, and
https://stacks.math.columbia.edu/tag/02H6 for the dependency conventions.

Object and clause inventory, matched with the actual Lean:

* An arbitrary field k: `{k : Type u} [Field k]`. PASS: no algebraic
  closedness, perfection or characteristic assumption.
* A k-scheme X and its structure morphism: `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of k))`. PASS: the same morphism is used in all
  three parent classes, with no separately chosen k-structure.
* X integral: `f.IsCurveOverField` extends `f.IsVariety`, whose field
  `isIntegral : IsIntegral X` is Mathlib integrality. PASS: read
  `Variety.lean` and Mathlib `Properties.lean`; this includes nonemptiness
  and integral domains on nonempty opens, not merely an integral morphism.
* f separated: the `IsSeparated f` parent of `f.IsVariety`. PASS.
* f of finite type: the `LocallyOfFiniteType f` and `QuasiCompact f`
  parents of `f.IsVariety`. PASS: both clauses, not only local finite type.
* Dimension exactly one: `Scheme.Hom.IsCurveOverField.dim_eq_one :
  X.dim = 1`. PASS: also read `Dimension.lean`; `Scheme.dim` is the
  supremum of local-ring Krull dimensions. The source's `IsCurve` instead
  uses dimension at most one and omits integrality, so it cannot replace it.
* The structure morphism smooth: `Smooth f`. PASS: read its affine-open
  ring-map field in Mathlib `Morphisms/Smooth.lean`. Stacks 01V5 and 02H6
  identify this with the smoothness dependency's infinitesimal formulation.
  The dependency's additional relative-dimension and etale definitions
  are not extra clauses of this item's definition.
* The structure morphism projective: `IsProjective f`. PASS: read
  `Morphisms/Projective.lean`; it includes `IsHProjective f` and
  `QuasiCompact f`. H-projectivity quantifies over `n : ℕ` and a closed
  immersion into `ℙ(ULift (Fin (n + 1)); Spec k)` with composition equal
  to f. This is precisely the node's recorded blueprint convention.
  Over a field, the finite-type quasi-coherent module in Stacks 01W8
  is a finite-dimensional vector space, so its projective bundle is a
  finite projective space; no different curve notion is introduced.
* These conditions define the notion, with no further conclusion:
  `class ... : Prop extends f.IsCurveOverField, Smooth f, IsProjective f`.
  PASS: construction requires exactly these parents and exposes each.

Standing source hypotheses: the introductory representability discussion in
`pic.tex` assumes k algebraically closed, but `lemma-check-conditions` explicitly
resets k to an arbitrary field and separately assumes a rational point. Neither
algebraic closedness nor a rational point is part of the curve definition.
Geometric integrality is not imposed either; varieties may cease to be integral
under extension of the ground field, as the source explicitly observes.

Edge cases: the empty scheme fails integrality and has `Scheme.dim = ⊥`, so
it cannot satisfy this definition. `Spec k` has dimension zero and is excluded.
This corrects the worker report's misleading nonemptiness wording: no separate
nonemptiness binder is added, but nonemptiness is already required by the curve
parent. Projective ambient n = 0 remains allowed by the existential; dimension
one excludes curves embedding into a point. No index family or zero-object
parameter occurs. All characteristics are covered. The single arbitrary universe
u agrees with the recorded scheme-morphism dependencies and Mathlib's Scheme
category; fields and schemes can be placed together in a common larger universe.
There is no test-object quantifier whose smaller universe could make a condition
vacuous. Every universe and variable is explicitly bound.

Independent searches (recorded in searches.jsonl): LeanFinder query
"integral one dimensional scheme smooth and projective over arbitrary field"
found integrality and affine-space facts, no combined notion. Loogle query
`"projective", "curve"` found only Weierstrass-coordinate constructions.
LeanSearch query "smooth projective integral curve over a field" was unavailable
(Internal Server Error), not treated as a negative result. msearch grep
`class.*Curve|def.*Curve|smooth.*projective` in AlgebraicGeometry returned
Weierstrass notions. Direct rg across Mathlib AlgebraicGeometry, all
WeilConjectures, and repository lean/Sheaf for curve predicates and smooth
projective curves found only hypothesis bundles and the curve dependency.
Read source `Curve.lean` IsCurve/IsConnectedCurve, `Picard/Scheme.lean`
`smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd`,
and `AbelianVariety/Jacobian.lean` IsJacobian: none defines this conjunction;
properness or geometric integrality and differing dimension conditions prevent
an exact match. rg of dag/lean_names_upstream.json and the source for this node
id and IsSmoothProjectiveCurve returned no declaration. No private copy,
new node, or dependency repair is needed.

Changes: added the exact Stacks source place to the module and declaration
docstrings and removed a stray leading space. The Lean signature and node record
remain correct and unchanged. No statement correction is needed. This definition
has no proof steps, theorem, sorry, or postponed data. All imports are used, the
namespace is AlgebraicGeometry, and all Lean lines are at most 100 characters.
The first server single-file compile passed cleanly; the final compile and
preflight are run after these documentation changes before delivery.
