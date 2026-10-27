## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.finite_pinching_invertible_patching`
in `Sheaf.AlgebraicGeometry.FinitePinchingInvertiblePatching`. Its only proof is `sorry`.
`Sheaf.AlgebraicGeometry.PinchingLineData` provides real data and predicates needed to
write the statement. It introduces no replacement for schemes, invertibility, tensor
products, module pullback, or the category of individual invertible modules.

The item's TeX statement, seven reviewed proof steps, proof dependencies, source,
status, and review are unchanged. Only its `lean` record and the additional statement
dependency `def-sfb-pinching-line-data` are delivered. The earlier BLOCKED ending
concerned stage-1 re-splitting. The maintenance handoff at the beginning of
`coord/brief-stage2.md` explicitly permits recording this stage-2 statement.
There is no released repair note for this item.

Clause-by-clause rendering:

- The schemes `S, X, X', Z` are the explicit binders `S X A B : Scheme.{u}`.
  The named structural map is `p : X ⟶ S`. The structural maps on `A` and `B`
  are `v ≫ p` and `j ≫ p`. Giving `S`-morphisms is equivalently giving these
  composites; no independent structure map or extra equation is assumed.
- Finiteness of `v` is `[IsFinite v]`; closed immersion of `j` is
  `[IsClosedImmersion j]`. Both are exactly the recorded Mathlib notions.
- `Z'` and its two projections are `Limits.pullback v j`, `pullback.fst v j`
  and `pullback.snd v j`. The actual equality of the composite maps supplies
  all the canonical overlap comparisons.
- The affine cover is `h : HasAffinePinchingCover v j`. Its `∀ x, ∃ U, x ∈ U`
  is equivalent to an affine open cover, including the empty cover of an empty
  scheme. The four `IsAffineOpen` conditions are the chart and its three
  inverse images. Their section rings provide the node's `R,A,B,F`; choosing
  them rather than arbitrary isomorphic coordinate rings changes no condition.
- Surjectivity of `A → F` is the `Function.Surjective` condition on
  `(pullback.fst v j).app (v ⁻¹ᵁ U)`. The section-ring `IsPullback` is exactly
  the assertion that the canonical `R → A ×_F B` is an isomorphism. The
  pullback in commutative rings is Mathlib's matching-pairs subring with
  coordinatewise operations (`CommRingCat.pullbackCone` and its limit proof).
  `appLE` only transports the closed-branch section map along the equality
  of inverse images induced by `pullback.condition`.
- A triple is `PinchingLineTriple v j`: `left` and `right` are modules on
  the two specified schemes, their two `IsInvertible` proofs assert exactly
  rank-one local freeness, and `overlap` is an actual isomorphism from the
  pullback of `left` to the pullback of `right`. Invertibility already gives
  quasi-coherence through the project's established API.
- `pinchingOverlap v j L` is the canonical comparison between the two
  restrictions of a single module `L`. It uses the recorded adjunction
  comparison `tensorPullbackCompositionIso`; it is not a chosen arbitrary
  isomorphism of the underlying modules.
- The first conjunct `PinchingLineEquivalence v j` states essential
  surjectivity as `∀ D, Nonempty (PinchingLineLift D)` and full faithfulness
  as unique lifting of every compatible pair of module maps. A lift includes
  its invertible module and both specified restriction isomorphisms, with
  the required overlap equation. These two conditions are the usual
  criterion for the specified pullback functor to be an equivalence. It is
  not merely an equivalence of isomorphism classes.
- Triple morphisms are exactly the arbitrary module maps satisfying
  `PinchingLineTriple.Compatible`, the same equation used in the Hom-lifting
  conjunct. No map is assumed invertible. Identities and composition are
  inherited componentwise. Consequently the unique lifts of an inverse pair
  are inverse: this identifies automorphisms as well as all Hom sets.
- The second conjunct says that the structure module realizes
  `pinchingUnitTriple` with the adjunction-normalized `pinchingUnitIso` on
  both branches. The third says that the tensor of any two lifts realizes
  the componentwise tensor triple, using the canonical tensor comparisons
  followed by `P.left ⊗ᵢ Q.left` and `P.right ⊗ᵢ Q.right`. This specifies the
  comparison on the overlap, not merely an existence of isomorphic lines.
- The fourth conjunct quantifies over every `T : Scheme.{u}` and every
  `t : T ⟶ S`. Its sole extra premise is the affine-pinching predicate for
  the new square. It gives the new equivalence and the precise compatibility
  equation for pulling any lift to `X_T`. The projection maps are the
  explicitly constructed `pinchingBaseMap`, and the map from the new overlap
  to the old one is `pinchingBaseOverlap`. `D.baseChange p t` really pulls
  back both modules and the prescribed overlap isomorphism. The two lift
  projections are `pinchingBaseProjection` followed by pullback of the old
  specified projections.
- These specified base-change lift equations together with unique Hom
  lifting express naturality: between any selected reconstructions, the
  comparison is the unique lift of the displayed branch comparisons. For
  a triple morphism the two naturality composites have identical branch
  maps, hence agree. For two successive allowed base changes, the direct
  comparison and composite have the same branches by canonical pullback
  composition, hence agree as well. Identity base change works identically.
  Thus no arbitrary comparison or unnormalized reconstruction is substituted.
  The same uniqueness gives associativity, symmetry and unit coherence for
  the tensor comparisons. The componentwise canonical comparisons come from
  the existing tensor and composition APIs.
- The last conjunct asserts that every `[Flat t]` satisfies the affine
  predicate. Combined with the fourth, this is exactly the flat-base-change
  specialization; arbitrary base changes are allowed whenever their square
  satisfies the original affine hypothesis.
- Empty `Z` is permitted: there is no `Nonempty`, `Nontrivial`, nonzero-ring,
  dimension, quasi-compactness, or separatedness binder anywhere.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Hom`, `Spec`;
  schemes have the usual locally affine locally ringed space definition.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  its class extends `IsAffineHom` and asserts finite affine section maps.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, closed embedding with surjective stalk maps.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`; existence for schemes
  comes from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, the actual local rank-one
  condition, and the project's ordinary scheme tensor product.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public import of
  the actual `tensorPullback` and the normalized module-pullback API.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackCompositionIso`, whose
  adjunction-based construction was read in full and is used for every square.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.module_pullback_tensor`. Its witness is
  characterized on all local pure tensors and is natural in both modules.
  Choosing it selects the canonically determined comparison, not free data.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`, whose first
  conjunct supplies preservation of invertibility in the base-change data.
- `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorObj` supplies closure
  under tensor product in the data definition.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  `tensorPullbackObjUnitToUnit` and `tensorPullbackObjUnitToUnit_isIso`, which
  give the normalized structure-module comparison used for the unit triple.

The main file additionally imports the modules of all currently stated proof
prerequisites: affine line-section dictionary, affine pullback sections, tilde
adjunction and principal sections, finite projective local freeness, exact
localization, common principal refinements, module gluing, and flat tensor
exactness. The two ring-patching prerequisites
`lem-sfb-fibre-product-finite-projective-patching` and
`lem-sfb-patched-module-base-change` have no Lean record yet, so there is no
module to import for them. They remain named in the theorem's full proof
plan, unchanged from the accepted split; no unstated prerequisite is used in
elaborating this statement.

Sources checked: local `literature/stacks-project/more-algebra.tex`, labels
`lemma-module-over-fibre-product` (07RU) and
`lemma-finitely-presented-module-over-fibre-product` (0D2J), including their
proofs. The rank-one restriction and gluing are exactly the node's reviewed
seven-step proof, included in the theorem docstring. The new data definitions
assert none of that proof.

Edge cases checked mathematically and against the binders: `Z = ∅` gives
`B = F = 0` chartwise and `R = A`; the overlap and empty-scheme line are unique.
For `Z = X`, a triple is equivalent to its line on `X` with its prescribed
restriction. For the identity square, the overlap is the ordinary pullback
composition comparison. Empty `X` has a vacuous cover and the unique empty
module data. Non-affine intersections are never assumed affine. Flatness is
not imposed on the allowed-base-change quantifier. Identity base changes,
zero module maps, automorphisms and disconnected schemes are retained.

Searches made before writing and before adding the data node (full service
responses are in the new node's `mathlib_searches`):

- LeanFinder, “Invertible sheaves on a finite pinching square are equivalent
  to matching triples of line bundles, compatible with tensor and base change”:
  eight hits, including pullback point-triplet tensor congruences, scheme
  gluing, and Mayer-Vietoris sheaf conditions; no line-bundle pinching theorem.
- LeanSearch, “Line bundles glue across a finite pinching square of schemes”:
  eight scheme-gluing hits, none this statement.
- Loogle, `"pinching"`: zero hits. Mathlib grep, `pinching|patching|Milnor`
  in `AlgebraicGeometry`: zero hits.
- LeanSearch, “Pair of invertible sheaves on two schemes with identified
  pullbacks to their fibre product”: eight pullback/gluing hits, no triple API.
- LeanFinder, “Data of a pair of invertible sheaves with an isomorphism on a
  scheme fibre product and compatible morphisms, with affine pinching ring
  hypothesis”: eight scheme pullback/chart hits, no line-triple data.
- Loogle, `"IsPullback", "IsAffineOpen"`: zero hits.
- `rg` in Mathlib, `lean/WeilConjectures` and `lean/Sheaf` for all proposed
  names found no declaration. Concept searches located the existing
  `TrfInvertibleModules` full subcategory, which is not redefined here.
- DAG concept grep found the assigned theorem, finite-projective ring
  patching, scheme pushout patching and nodal Picard assemblies; no existing
  definition node owns these line-triple data. `tools/blueprint_refs.py search`
  for “pinching” and “invertible patching” found zero blueprint nodes.
  A search for the item id in `lean/WeilConjectures` found no existing theorem.

No statement fault or `STATEMENT-DISPUTED` flag remains. All writes are confined
to the dispatched sandbox; compiles use the prescribed server wrapper.

## New nodes

`def-sfb-pinching-line-data` packages the affine-cover predicate, triples, their
compatible maps, specified lifts and the full-faithfulness/essential-surjectivity
criterion, plus the actual componentwise tensor and base-change constructions.
It is a definition node, with no postponed theorems. Every module-pullback map
is built from the recorded canonical composition, tensor and unit comparisons.
Its statement specifies the entire data interface; its own dependencies cite
the existing scheme, fibre-product, spectrum, invertibility and pullback notions
and the existing comparison results used to construct the data. The source is
07RU/0D2J together with the canonical tensor-pullback comparisons named by the
assigned node. The searches above and in its record found no existing owner.
The inherited null blueprint ancestor is retained, and its via chain prepends
the assigned item as required. The item cites this node directly.

## Second reading by Q19

I performed this separate reading after the modules compiled, reopening the
original node and both final Lean files. The dispatcher forbids starting other
agents; this section is a second pass by the dispatched worker, not a claim
that a second worker was launched. The maintainer's independent review is still
required as specified in the brief.

I checked the affine square first: the top arrow is `v.app U`, the other source
arrow is `j.app U`, and both target arrows end in the same ring on the inverse
image of `U` in the intersection. The `appLE` transport is justified by the
pullback equation, so `IsPullback` has the desired ring orientation. Neither a
scheme pushout nor an unrelated ring product has replaced this condition.

I then checked the two projections of every triple and lift against the source:
`left` lives on `A = X'`, `right` lives on `B = Z`, and the overlap has direction
`(j')^* M → w^* N`. The full-faithfulness equation has the same orientation as
a commuting square between these overlap arrows. It quantifies over all maps,
so reducing to Picard classes or to a groupoid has not lost zero or noninvertible
morphisms. The chosen equivalence criterion therefore retains automorphisms.

For tensor products I found that binary compatibility alone did not explicitly
record the structure-module comparison. I added `pinchingUnitIso`,
`pinchingUnitTriple`, and the unit-lift conjunct. The unit comparison uses the
existing adjoint structure-sheaf map and its existing isomorphism theorem.
The binary equation uses the section-characterized pullback tensor witness,
so it fixes which comparison is meant.

For naturality I traced all three base-change maps: the finite and closed maps
go from the corresponding `A_T` and `B_T` to `X_T`, and the overlap map goes
from `A_T ×_{X_T} B_T` to `A ×_X B`. The new overlap is pulled back along that
last map. Both projection isomorphisms go from the branch restriction of the
pulled-back reconstructed line to the pullback of the prescribed branch line.
Thus the lift equation states precisely that the reconstruction commutes with
this base change. Uniqueness of Hom lifting gives naturality and the identity
and composition laws, without assuming exactness for a nonflat tensor functor.
The affine premise remains explicit for arbitrary base changes; only the final
conjunct requires flatness and proves that premise in that case.

The data definitions have no `sorry`; choosing the existing comparison witnesses
postpones no arbitrary object because the local pure-tensor/unit normalization
fixes them. A server compile exposed two `letI` style warnings in proof-valued
fields; these were changed to `let`. The subsequent compile of each file in
its actual module context was clean. All universes and variables are explicit.
The mathematical edge cases above are still admitted by the final binders.

Validation on 2026-10-23: re-read the live stage-2 handoff, unchanged item,
recorded dependency interfaces and the two Stacks fibre-product lemmas. Repeated
LeanFinder, Loogle and Mathlib/project/DAG name and concept searches found no
existing line-triple interface. Both delivered modules compiled cleanly with
`scompile.py` in their library module contexts. The first dry run requested the
new-node schema field `import_flags`; added the empty list, since the item cites
this definition and no import flag applies. No Lean statement changed.
