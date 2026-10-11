## Worker report

The module `Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex` states the item as two
named theorems with `sorry` proofs. It introduces no definitions and changes no statement.
Both docstrings contain the natural-language proof, including the extension of a compatible
face tuple, uniqueness of the comparison, and the restriction-to-matching-map calculation.

Hypotheses and clauses:

- `X : Scheme.{u}` is the arbitrary scheme, and
  `K : SimplicialObject (FormalCoproduct.{w} X.Etale)` is precisely a simplicial
  semi-representable étale object. The universes `u`, `w`, `t` are explicit; no nonemptiness
  condition is imposed on the scheme, its families, or their terms.
- Mathlib `Δ[n]` has order-preserving maps as simplices via `SSet.stdSimplex.objEquiv`,
  and its operators precompose. `SSet.boundary n` consists of the nonsurjective maps,
  including the empty boundary at zero. `SSet.boundary.ι i` applied to the identity simplex
  gives exactly the codimension-one boundary simplex `δ_i`.
- Part (a), `simplicial_hom_standard_simplex`: the first conjunct asserts finite and
  nonempty degrees for every `m`; the second is `SSet.Finite`, meaning finitely many
  nondegenerate simplices. The third identifies nondegenerate simplices with injective
  underlying maps. The fourth gives the compatible family on `K_n`, explicitly requiring
  its components to equal `K.map (objEquiv s).op`, and says it represents
  `simplicialHomFamilyFunctor K Δ[n]`. The final conjunct gives, over every `W` and every
  family `f`, the unique map `g`, requires `g` to be the identity-simplex component of `f`,
  and requires every component of `f` to equal `g ≫ K.map φ.op`.
- Part (b), `simplicial_hom_boundary_matching`: the actual positive degree is `n + 1`,
  with unrestricted `n : ℕ`, covering exactly the node's degrees at least one. The first
  two conjuncts assert finite nonempty degrees and finitely many nondegenerate simplices.
  For every chosen representing pair `H, u`, the `IsRepresentedBy u` hypothesis renders
  exactly the node's fixed Hom object and universal family. `∃! θ` renders the unique
  isomorphism with the stated projection equations. The projections are the existing
  `Pi.π` when the degree is one, and `Multiequalizer.ι` for degree `r + 2`, using the
  very same `matchingBoundaryIndex K r` as `semiRepresentableMatchingObject`.
- Part (c) is the remaining portion of that same theorem, under the same representing
  hypothesis. `∃! ρ` states existence and uniqueness of the map with every prescribed
  operator component, and the last clause, for every projection-preserving `θ` and every
  `ρ` satisfying those equations, says `ρ ≫ θ.hom = semiRepresentableMatchingMap K (n+1)`.
  Lean composes left-to-right, giving precisely the paper's `θ ∘ ρ = μ`.

Dependencies used:

- `Sheaf.AlgebraicGeometry.SimplicialHomObject`:
  `AlgebraicGeometry.Scheme.SimplicialHomFamily` and
  `AlgebraicGeometry.Scheme.simplicialHomFamilyFunctor`, with Mathlib's
  `CategoryTheory.Functor.IsRepresentedBy`. These are the recorded family notion and
  universal property, not a copy of them. The restriction map is characterized directly
  by its universal component equations, as in the node.
- Its imported `Sheaf.AlgebraicGeometry.SemiRepresentableObject`:
  `AlgebraicGeometry.Scheme.semiRepresentableMatchingObject` and
  `AlgebraicGeometry.Scheme.semiRepresentableMatchingMap`; the instance
  `semiRepresentableHasMultiequalizer` supplies the matching limit. The imported
  `CategoryTheory.SimplicialObject.matchingBoundaryIndex` is its recorded diagram.
- `Mathlib.AlgebraicTopology.SimplicialSet.Boundary`: `SSet.boundary`, `SSet.boundary.ι`,
  and the imported standard simplex, `SSet.stdSimplex.objEquiv`, `SSet.Finite`, and
  nondegenerate-simplex notion.

Edge cases checked before writing: at degree zero, the standard simplex has just the
constant map in each degree and one nondegenerate vertex; (a) remains valid. Boundary
zero is empty and excluded only from the positive-degree conclusions. At degree one
its two vertices give the product matching object, with no face-pair relations. At degree
two its three edges satisfy the three vertex-agreement equations of the multiequalizer.
Constant maps witness nonempty boundary degrees for every positive degree. Empty schemes
and empty formal families are allowed; representing properties quantify over all formal
families and use no extra geometric assumption.

Searches (the mandated `msearch.py M1` calls):

- LeanFinder query: "Hom from standard simplex into simplicial object is degree n and
  boundary Hom is matching object". Eight hits, including DoldKan.MorphComponents,
  simplicial face/degeneracy maps and standard augmented extra degeneracy; no theorem
  giving this semi-representable Hom/matching comparison.
- Loogle query: "SSet.stdSimplex, SSet.boundary". Twelve hits, including `SSet.boundary`,
  `SSet.boundary.ι`, boundary dimension bounds and boundary hom extensionality; these
  provide definitions and uniqueness for simplicial sets, not this whole statement.
- Mathlib grep query: "matchingObject|simplicialHom|yonedaEquiv", restricted to
  `AlgebraicTopology/SimplicialSet`. Twenty-five hits including `SSet.yonedaEquiv` and
  boundary lemmas; no SR(X) matching-object comparison. Source inspection also read
  StdSimplex.lean, Boundary.lean, and Finite.lean, including their signatures/docstrings.
- `rg` over `WeilConjectures` and `lean/Sheaf` for
  "simplicialHom|standardSimplex.*matching|hom_object_standard" finds only the landed
  Hom-family definitions in Sheaf. The prescribed node-id grep in `WeilConjectures`
  finds no declaration. No reusable declaration with the item's whole statement exists.

Read the source places [Stacks 0177](https://stacks.math.columbia.edu/tag/0177) and
[Stacks 018V](https://stacks.math.columbia.edu/tag/018V); the local literature copy is absent.
The node's explicit five-step proof supplies the matching-face presentation and component
calculation, in agreement with those source places.

Validation: local compilation reports the recently landed `SimplicialHomObject.olean`
missing from the cache. The specified server fallback compiles the final module cleanly
in 2.1 seconds with no warnings. All theorem proofs remain `sorry`. No new nodes or
dependency modules are needed; no statement dispute or correction.

## Second reading by M1

I reread the node and the module independently against Stacks 0177 and 018V.
The node introduces a scheme `X`, a simplicial object `K` in `FormalCoproduct X.Etale`,
its matching objects and matching maps, the standard simplex and its non-surjective
boundary, and the codimension-one injections. The Lean binder
`{X : Scheme.{u}} (K : SimplicialObject (FormalCoproduct.{w} X.Etale)) (n : ℕ)`
renders the first two objects and all three universes without extra hypotheses.
`SSet.stdSimplex`/`SSet.boundary` render the two simplicial sets, and
`SSet.boundary.ι i` applied to the identity simplex renders the stated codimension-one
boundary simplex.

For (a), `∀ m, Finite ... ∧ Nonempty ...` gives finite nonempty degrees, `SSet.Finite`
gives finitely many nondegenerate simplices, and the following biconditional identifies
nondegenerate simplices with injective monotone maps. The existential `f` has exactly the
components `K.map (SSet.stdSimplex.objEquiv s).op` and the
`IsRepresentedBy` universal family required by the node. The final `∀ W f, ∃! g`
uses the identity component
`f.val n (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))` and states every component as
`g ≫ K.map ...`, with the same quantifier order and uniqueness clause.

For (b), the Lean parameter `n : ℕ` is shifted to the node's positive degree `n+1`.
The first two conjuncts give finite nonempty degrees and finitely many nondegenerate
simplices of the boundary. The universally quantified `H,u` plus
`IsRepresentedBy` is the dependency's chosen representing pair
`Hom(∂Δ[n+1],K)_0` and universal family. The `∃! θ : H ≅
semiRepresentableMatchingObject K (n+1)` clause gives the unique comparison, and its
projection equation uses `Pi.π` at matching degree one and `Multiequalizer.ι` at all
higher degrees, exactly the dependency's matching object and the node's `pr_i`.

For (c), the `∃! ρ` clause gives the unique restriction map whose every boundary
component is `K.map (...)`; the final universal clause states that every projection-
preserving `θ` and every `ρ` satisfying those component equations obey
`ρ ≫ θ.hom = semiRepresentableMatchingMap K (n+1)`. Lean composition is left-to-right,
so this is precisely the node's `θ ∘ ρ = μ_n` after the degree shift.

Edge cases checked: `n=0` in (a) has the constant vertex as the sole nondegenerate
simplex; `n=0` in (b) is the boundary of `Δ[1]`, with the product of two copies of
`K_0`; positive boundary degrees are nonempty by constant maps, while the excluded
`∂Δ[0]` is empty exactly as the node says. Empty schemes and empty formal families
are not excluded, and no characteristic, finiteness, Noetherian, or universe restriction
is added. All index universes are explicit and the test object universe is
`Type (max u w t)` through the recorded family functor.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or `lean/Sheaf`
for this semi-representable Hom/matching comparison; the worker's LeanFinder, Loogle,
and grep searches record the relevant negative results in `searches.jsonl` and the
worker report. The recorded dependency declarations are used directly, with no private
copies. I found no mismatch and made no Lean or node statement change.
