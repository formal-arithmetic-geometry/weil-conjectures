## Worker report

The delivery states all three clauses of
`lem-pur-proetale-inverse-image-tensor-comparison` in
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`, namespace
`AlgebraicGeometry.ProEtaleTensorComparison`. The primary declaration is
`inverseImage_tensor_comparison`; the unique existence and normalized construction
parts are exposed as the other declarations listed in `lean.declarations`.
Every theorem has proof `sorry`. Every definition has actual data. In particular,
`Classical.choose` is used only on a unique-existence theorem that determines the
chosen morphism or isomorphism by equality, never on a bare `Nonempty` assertion.
There is no statement correction, new independent notion, or dependency replacement.

### Hypotheses and objects

- Arbitrary schemes and composable scheme morphisms are
  `{X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)`. No smoothness, weak-etaleness,
  finite-type, finiteness, nonemptiness or coefficient-topology hypothesis is imposed.
  `X`, `Y`, `Z` represent the node's T'', T', T.
- `R : Rings Z` is exactly a commutative ring sheaf on `ProEt.topology Z`.
  `Rings` is a transparent abbreviation for that existing sheaf category.
- `M N : Modules R` are the node's F and G. `Modules` abbreviates the recorded
  `CategoryTheory.ringedSiteModules` over the underlying RingCat sheaf.
- `inverseRing h R` and `inverse h R` use the recorded
  `proEtaleSheafInverseImage` and `proEtaleModuleInverseImage`, respectively.
  The latter internally transports the module construction to `AsSmall` and back;
  it retains the original pro-etale site, with object universe u+1 and Hom universe u.
  Rings and module sections live in the standard larger sheaf universe u+1.
- `tensor M N` is the recorded `siteSheafTensorRight` object. `pure M N V s t`
  is exactly `siteSheafTensorTmul`, the presheaf pure tensor followed by the
  module-sheafification unit. No tensor product is constructed a second time.
- `inverseSection h M V s` is evaluated from the module adjunction unit in the
  dependency's actual small-model construction. Its result is a section at
  `(proEtaleBaseChange h).obj V`, canonically T' times_T V. The dependency chooses
  the variable factor first, so this is written V times_T T' in the underlying
  fibre-product presentation. This is the same base-change object.
  `moduleSetsIdentification_exists` identifies this unit with the set adjunction
  unit, including its normalization at every V and every s.

### Clause 1

`comparison_exists h R M N` says **there exists exactly one morphism**
from `(inverse h R).obj (tensor M N)` to
`tensor ((inverse h R).obj M) ((inverse h R).obj N)` with the node's formula for
all original objects V and all section pairs s,t. Uniqueness ranges over all
module morphisms, not just invertible ones. The data definition `comparison`
selects that uniquely determined morphism. The first two conjuncts of
`inverseImage_tensor_comparison` state `IsIso (comparison h R M N)` and its
local pure-tensor formula for the selected morphism. Its third conjunct states
joint naturality, for all morphisms `a : M ⟶ M'`, `b : N ⟶ N'`, using the
existing first-factor and second-factor tensor maps in `tensorMap`.

### Clause 2

`restrict a` is Mathlib restriction of scalars for the ring-sheaf map a.
`coefficientQuotient_exists` gives the unique module map from the tensor of
restricted modules over R to the restriction of their tensor over S whose value
on s tensor t is s tensor t. `coefficientQuotient` selects precisely that map.
This renders the node's pi and pi', for any ring-sheaf morphism, without a
surjectivity, flatness, finiteness or nonzero-ring assumption.

`inverseRingMap h a` is the recorded commutative-ring inverse-image functor's
map on a. `scalarIdentification_exists` and `scalarIdentification` give the
unit-normalized canonical identification between inverse image of the restricted
module and restriction of its inverse image along this ring map. This makes
explicit the node's phrase "regarded also as" modules over the smaller ring;
its uniqueness characterization prevents substitution of an arbitrary iso.

The fourth conjunct of the primary theorem quantifies over **all**
`S : Rings Z`, `a : R ⟶ S`, and `F G : Modules S`. Its left composite is
inverse image of pi, the scalar identification for F tensor_S G, and sigma over S
viewed over inverseRing h R. Its right composite is sigma over R, tensor of the
two scalar identifications, and pi' over the inverse-image ring map. The two
composites have exactly the same source and target. Thus it is the node's
coefficient-change square with the scalar identifications made explicit.

### Clause 3

`setComp_unique g h e` characterizes the natural isomorphism e by exactly its
adjunction-unit equation. Equality of sheaf maps here is equality of their
values on every section at every original V. Evaluating the equation at a
section is the formula e((h composed with g)^-1 s) = g^-1(h^-1 s), with
`lowerStarComp` inserting the canonical fibre-product associator. The equivalence
with `e = ProEtale.setPullbackComp g h` both proves that the specified compositor
has the formula and proves uniqueness among all natural isomorphisms. It uses
exactly the compositor recorded by `det-pe-topos-functoriality-inverse-image`.

`ringComp g h R` is the adjoint conjugate of the canonical direct-image
composition comparison, computed in commutative ring sheaves. It is an actual
ring isomorphism. `moduleComp_exists` gives the unique module isomorphism,
semilinear through `ringComp.hom`, with the section formula, explicitly including
the restriction along `MorphismProperty.Over.pullbackComp`. `moduleComp` selects
that uniquely determined isomorphism. These are the ring and module lifts of
gamma. Their underlying-set identification is part of the primary theorem:

- Its fifth conjunct identifies the ring compositor with `setPullbackComp` via
  the unit-normalized `ringSetsIdentification` for each inverse image.
- Its sixth conjunct does the same for every `P : Modules R`, with
  `moduleSetsIdentification`. Since `moduleComp.hom` is a morphism into the
  scalar restriction along `ringComp.hom`, this asserts precisely that the
  set compositor carries the given module operations and action to those of
  the iterated inverse image, rather than asserting mere bijectivity of sets.

The seventh conjunct is the **entire morphism equation**, not merely equality on
original pure tensors. Its left route is module gamma for M tensor N, followed
by inverse image under g of sigma under h and then sigma under g. Its right
route is sigma under g composed with h, then tensor of the two module gammas.
The final coefficient quotient through the ring isomorphism explicitly identifies
the target tensor along gamma_R, as the node requests.

The eighth conjunct states that the actual adjunction unit at the identity
morphism is an isomorphism on every set-valued sheaf H. `ringId` is the canonical
ring identity comparison obtained by conjugating `lowerStarId`.
`moduleId_exists` uniquely normalizes the corresponding module comparison by
this unit, with the canonical fibre-product identity comparison explicit.
The ninth conjunct says sigma at the identity, followed by the factor identity
identifications and the ring-identified tensor comparison, is the identity
identification for M tensor N. This is precisely "under the unit, sigma is the
identity" and covers arbitrary ring sheaves and modules.

### Dependencies and source reading

Read every statement-dependency record and the full declaration/docstring used:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, the small-model ring unit,
  module-to/from-model functors and `proEtaleModuleInverseImage`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorTmul`, `siteSheafTensorRight`, `siteSheafTensorSecondMap`,
  including the imported `TensorProductOfUniverses` construction.
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`:
  `ProEtale.setPullback`, `setPullbackAdjunction`, `setPullbackComp` and its
  unit-compatible `toposFunctorialityInverseImage` statement.
- `def-weil-scheme-morphism-properties` is a convention node with no declaration;
  schemes and their morphisms use Mathlib directly, as that record instructs.

The published proof dependencies are imported non-publicly, preserving the plan:
`AlgebraicInverseImageOfUniverses`, `RingedTopoiTensorComparisonData`,
`RingedTopoiTensorComparisonConstruction`, `TensorBilinearUniversal`,
`RingedTopoiModuleAdjunctionRepair`, and Mathlib `Sites.Sheafification`.
Read the missing local sources through `scompile.py --source`; these are live
published declarations. The proof-only node
`lem-trf-site-inverse-image-composition-generators` currently has no Lean module,
so there is no import to add for it. It is not a missing statement prerequisite:
the compositor and its unit-compatible adjunction are already constructed by the
recorded statement dependency. No waiting or downstream dependency was introduced.

Read the local Stacks source `sites-modules.tex`, Section 03EK through Tag 03EL,
including its bilinear universal property and pullback comparison. Also read
`coord/pefw-upstream-framework.md` and the full module inverse-image presentation.
The theorem docstrings carry the natural-language proof of the node's steps,
including adjunct uniqueness (rather than the incorrect claim that original
pulled-back pure tensors locally generate), operation transport, and the initial
comma object being terminal in the **opposite** colimit index for the identity.

### Edge cases and checks

The statement permits empty schemes, zero sheaves, the zero coefficient ring,
non-finite rings, arbitrary ring morphisms (including identity and maps to the
zero ring), identity morphisms and arbitrary composable scheme morphisms. There
is no extra topology on a coefficient ring, no characteristic restriction,
no weak-etaleness assumption on h or g, and no site object/Hom universe equality.
The identity case is stated explicitly. Existence/uniqueness does not require a
nonzero pure tensor. A ring isomorphism in the target composition square is
handled by actual scalar restriction and its normalized tensor quotient.

Checked that all variables and universes are explicit (`autoImplicit false`),
all lines are at most 100 characters, all local maps use the recorded tensor and
inverse image, and all data chosen from postponed theorems are uniquely determined.
There are no known node faults and no STATEMENT-DISPUTED flag.

### Searches

- `msearch.py leanfinder`: "inverse image sheaves modules tensor product comparison
  natural pure tensors" returned pullback/free-module interfaces and sectionwise
  tensor naturality, with no theorem giving all three clauses.
- `msearch.py loogle`: "SheafOfModules.pullback, SheafOfModules" returned the
  pullback adjunction, pullbackId, pullbackComp and associativity. Their signatures
  provide no pure-tensor-normalized tensor comparison with the coefficient and
  composition clauses of this node.
- `msearch.py grep`: "pullback.*tensor|tensor.*pullback" in
  `Algebra/Category/ModuleCat/Sheaf` returned zero hits.
- `msearch.py leansearch`: "inverse image sheaves modules tensor product canonical
  natural isomorphism" returned tensor/limit, pullback/free and pushforward naturality
  results, with no exact match.
- `rg` in the upstream `WeilConjectures` source found scheme-module and constant
  coefficient/derived tensor comparisons, not this arbitrary ring-sheaf normalized
  pro-etale statement. Searching the exact item id found no declaration.
- `rg` in project `lean/Sheaf` and the 51-module pro-etale framework found the
  dependency constructions used here, as well as specialized coefficient/derived
  comparisons. None states this node's three clauses together. The proof's generic
  normalized comparison exists and is imported; it does not by itself state the
  present uniqueness, coefficient square, composition and identity assertions.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
