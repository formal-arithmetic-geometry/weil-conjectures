## Reviewer fix (R-fce1115, 2026-10-11)

The delivered statement replaced the node's complex K_• of presheaves of O-modules, built from the
fibre products U_{i0} x_U ... x_U U_{ip} and the projections, by a private evaluated model in
fibre-product coordinates (new node def-weil-pbc-free-cech-differential: a sigma type of compatible
lifts and a hand-written deletion differential). That model already performs steps (1)-(2) of the
proof and is a second construction of the Čech nerve that Mathlib has (FormalCoproduct.cech, under the
recorded cechComplexFunctor leaf of def-weil-pbc-cech-complex) and of the free presheaf O_V
(PresheafOfModules.free O (yoneda V)). Fixed: the theorem now states ExactAt (p + 1), after
evaluation at W, of alternatingFaceMapComplex of the Čech nerve of i ↦ Over.mk (f i) in Over U₀,
sent to PresheafOfModules O by FormalCoproduct.eval of Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O.
The new node def-weil-pbc-free-cech-differential and its module Sheaf.Paper.FreeCechDifferential
are dropped. Universes: ι and O are in the universe u of X (PresheafOfModules.free and the
coproducts of PresheafOfModules.{u} need it); no hypothesis quantifies over test objects.

## Worker report

The module `Sheaf.Paper.FreeCechDifferential` defines `freeCechBasis` and the
alternating deletion map `freeCechDifferential`.  A basis element consists of a
map `φ : W ⟶ U₀` and a tuple of lifts `(i,g)` with `g ≫ f i = φ`; the map sends a
basis tuple in degree `p+1` to the signed sum of tuples obtained by deleting one
coordinate.  The module `Sheaf.Paper.FreeCechComplexExact` states
`AlgebraicGeometry.freeCechComplex_exact`.  Its binders render the scheme `X`,
the index type `ι`, target `U₀`, family `U`, maps `f`, presheaf of rings `O`,
object `W`, and positive integer `p` exactly.  The conclusion
`LinearMap.range (freeCechDifferential f O W (p + 1)) =
LinearMap.ker (freeCechDifferential f O W p)` is exactness in positive degree;
`hp : 0 < p` excludes degree zero as in Lemma 03F5.  The empty family and an
object with no lifts have empty bases (hence zero free modules); no nonemptiness
hypothesis was added.  Zero coefficient rings are allowed by `RingCat`.

Dependencies used: `AlgebraicGeometry.Scheme.smallEtaleTopology` and
`AlgebraicGeometry.Scheme.Etale` from `Mathlib.AlgebraicGeometry.Sites.Etale`
(the recorded `def-weil-pbc-etale-site` Mathlib leaf), and the recorded
presheaf-module notion from `def-weil-presheaf-modules-sheafification`.  The
new definition node `def-weil-pbc-free-cech-differential` supplies the explicit
evaluated basis and differential.  The proof is `sorry` as required; its
docstring gives the four source proof steps and cites
`lem-weil-pbc-power-set-complex-contractible` for the contracting homotopy.

Searches: `msearch.py leanfinder` for a free presheaf Čech complex found only
unrelated Mayer–Vietoris and injective-resolution declarations; `msearch.py
loogle` for `Finsupp.linearCombination` and alternating deletion found no exact
match; `msearch.py leansearch` was unavailable.  Grep of Mathlib found
`Finsupp.linearCombination` but no free Čech differential, and grep of the
source repository and `lean/Sheaf` found no matching declaration.  The existing
DAG search found no node defining this evaluated differential.

## New nodes

`def-weil-pbc-free-cech-differential` defines the evaluated free Čech basis and
alternating deletion differential used by the item.  Its source is Stacks Lemmas
03AS/03AT.  The searches above found no existing DAG, Mathlib, or project
notion, so it is included as a new definition node and cited by the item.

## Earlier second reading (a previous round; superseded)

The item node was read against `FreeCechComplexExact.lean`.  `X`, `ι`, `U₀`,
`U`, and `f` render the scheme, indexed family, fixed target, and target maps;
`O` is the presheaf of rings and `W` is the evaluated object.  The added
hypothesis `hp : 0 < p` and the range-equals-kernel conclusion render exactly
positive-degree exactness.  The differential node was read independently:
its sigma type records a common map to `U₀` and each lift, and `succAbove`
deletes one coordinate with the alternating sign.  No hypothesis or edge case
was added or omitted.


## Second reading by M1

Read the item and both delivered modules against Stacks sites-cohomology.tex,
labels lemma-cech-map-into (03AS), lemma-homology-complex (03AT), and
lemma-complex-tensored-still-exact (03F5), from the local source copy
`/home/ubuntu/c1-stacks-review/sites-cohomology.tex`, lines 971–1188. The source
assumes only a category with the specified fibre products, an arbitrary family
with fixed target, and a presheaf of rings. The item specializes that category
to the small etale site; no covering condition is assumed.

Object, hypothesis, and conclusion checklist:

- Scheme X: `X : Scheme.{u₁}`. Correct; no separatedness, Noetherian,
  characteristic, field, or finiteness condition.
- Small etale site: `X.Etale`. Opened the dependency node
  `def-weil-pbc-etale-site`, Mathlib Sites/Etale.lean and
  Morphisms/Etale.lean: `Scheme.Etale` is `MorphismProperty.Over @Etale ⊤ X`,
  deriving Category, HasPullbacks and HasFiniteLimits; `smallEtaleTopology`
  is the recorded topology. Thus these objects and morphisms are precisely
  etale X-schemes and X-morphisms. Exactness here needs no topology hypothesis.
- Index set I: `ι : Type v₁`. Correct; arbitrary size, empty or infinite.
- Fixed target U: `U₀ : X.Etale`. Correct.
- Family U_i and target morphisms: `U : ι → X.Etale` and
  `f : ∀ i : ι, U i ⟶ U₀`. Correct; no surjectivity or covering hypothesis.
- Ring presheaf: `O : X.Etaleᵒᵖ ⥤ RingCat.{w₁}`. Correct; arbitrary rings,
  including noncommutative rings and zero rings, and no sheaf condition.
- Evaluating object: `W : X.Etale`. Correct; universal quantification.
- Free presheaves O_V and their maps: at W their values are the Mathlib
  `Finsupp` free modules on morphisms into V; composition of morphisms sends
  basis elements to basis elements. Opened the dependency node
  `def-weil-presheaf-modules-sheafification` and Mathlib's `PresheafOfModules`
  structure: its restriction maps are semilinear for an arbitrary RingCat
  presheaf. No sheafification instance is needed by this evaluated statement.
  Also opened Presheaf/Free.lean: `freeObj` supplies this general free
  presheaf construction; it does not supply the tuple differential here.
- K_q(W): `freeCechBasis f W q →₀ O.obj (op W)`. Its sigma records a
  common map φ and q+1 lifts `(i,g)` satisfying `g ≫ f i = φ`. These are
  exactly maps to the node's iterated fibre products by their universal
  property, retaining repeated indices and all morphisms. No notion is replaced
  by a special case. The node's zero negative degrees do not enter positive
  exactness, and its restriction data are not additional asserted conclusions.
- Differential K_(q+1) to K_q: `freeCechDifferential f O W q`.
  `Finsupp.linearCombination` extends the prescribed values on basis elements;
  `j.succAbove` deletes coordinate j and `(-1 : ℤ) ^ j.val` gives its sign.
  Correct; coefficients act on the left, valid also for noncommutative rings.
- Every positive degree: this was WRONG. The original `hp : 0 < p`, together
  with `range (d (p+1)) = ker (d p)`, asserted exactness at K_(p+1) and
  excluded degree 1. Removed hp. Now `p : ℕ` enumerates all positive degrees
  q=p+1, and the conclusion is exactly image(K_(q+1) → K_q) =
  kernel(K_q → K_(q-1)). This is equivalent to H_q=0 for every q>0,
  with no assertion about H_0. The unit/node statement was right and is unchanged.

Edge cases: an empty index type or a common map with no lifts gives an empty
basis in every nonnegative degree and the zero free module. Zero coefficient
rings give zero modules. The empty scheme is permitted. At Lean p=0 the
conclusion is exactness at K_1 (the case previously omitted); no degree-zero
acyclicity is claimed. For a singleton lift set the boundary is alternately
zero and identity, verifying the indexing. All characteristics are allowed.
Universes of schemes, index types and rings are independently quantified;
added explicit `universe u₁ v₁ w₁` to the theorem module, with distinct names
from the sibling module so both standalone and combined compilation bind them.

Independent searches (logged by msearch.py): LeanFinder query “Exactness of the
alternating boundary on free modules on powers of sets of morphism lifts”;
Loogle `Finsupp, LinearMap.range, LinearMap.ker`; Mathlib grep
`cech.*(exact|differential)|alternating.*(deletion|boundary)`; and LeanSearch
query “The boundary of the free module on tuples deletes each entry with
alternating signs, and its homology vanishes in positive degrees” (service
unavailable). LeanFinder returned alternatingConst_exactAt and alternating
face-map/group-homology ingredients, not this statement. Opened AlternatingConst:
it is a periodic constant complex, not the variable free tuple modules.
Loogle returned general Finsupp and group-homology results, not an exact match.
Grep of the source WeilConjectures and project lean/Sheaf found topological
cochain Cech criteria and projective-space complexes, not this free chain
complex. Searched dag/lean_names_upstream.json and DAG node statements;
`blueprint_refs.py search 'free Cech differential'` found no blueprint definition.
The general-site free-Cech statement and set-Cech resolution nodes are related
statements, not existing definitions of this differential, and have no recorded
usable declaration replacing this item.

New node independent reading: `def-weil-pbc-free-cech-differential` genuinely
supplies the evaluated tuple basis and differential absent from the DAG and
libraries; general `PresheafOfModules.freeObj` and `Finsupp.linearCombination`
are reused ingredients, not duplicate definitions of that differential.
Expanded its previously underspecified TeX to state B_p, K_p, the domain,
codomain, lift equations, alternating formula and fibre-product identification.
Added the two definition dependencies for the etale site and module notion,
explicitly cited in its statement; included 03F5 in its source for ring
coefficients; listed the auxiliary basis declaration in lean.declarations.
Its kind/status, chapter/unit, created fields, ancestor and via, empty proof,
null mathlib_match and none lean_audit satisfy the new-node contract. Replaced
its search records by the actual independent logged queries. No dependency
module is needed; there is no statement_change and no corrected-node citer audit.

The two definitions contain actual data and no sorry. The sole theorem remains
`by sorry`, with the source and blueprint id and all four node proof steps in
its docstring. Both modules follow namespace/import/header conventions;
explicit universes leave no unbound names. Refreshed both lean.statement records
from the signatures parsed from their modules. The earlier worker/reading claim
that hp was correct is superseded by this review.

Validation: both modules compiled together on the server in dependency order
with no errors or warnings. The first dry-run preflight required a verdict
field even for the unavailable LeanSearch; recorded its unavailability without
a mathematical search verdict and reran the dry run.
