## Worker report

Recorded the exact existing definition
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructiblePullbackSquareComparison`
from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`.
No Lean module, theorem, sorry, new node, dependency repair or statement correction is added.
Only the item's `lean` record changes. The source is the current blueprint
`main-20261015`, `sec-six-functors-basics/sk-def-sfb-base-change-morphism/`
`det-def-sfb-base-change-morphism-comparison.md`.

I read the entire item, its proof, all four statement-dependency statements and records,
their declaration docstrings and signatures, and `coord/pefw-upstream-framework.md`.
The authoritative current declarations were retrieved with `scompile.py --source` for
both `Derived.BoundedConstructible` and `BaseChangeTheorems.MorphismDefs` under
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`. The shared local framework source
has older Scheme/IsOver parameters and an explicit `k` argument; the published source
uses Over objects and infers `k`. The record quotes the published signature verbatim.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Field k of characteristic p > 0, p different from ell:
  `{k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
  In a field the positive characteristic is prime, so this expresses exactly the
  node's condition, with p the uniquely determined `ringChar k`.
- Four schemes over k: `{X Y X' Y' : Over (Spec (.of k))}`. Their underlying schemes
  are `.left`, and their k-structure maps are `.hom`.
- Separated finite type: for EACH of X, Y, X', Y', the section has
  `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]`.
  Locally finite type plus quasi-compact is finite type; there is no restriction on
  dimension, smoothness, reducedness or nonemptiness.
- The four arrows are k-morphisms: `{f : X ⟶ Y} {g : Y' ⟶ Y}`
  `{f' : X' ⟶ Y'} {g' : X' ⟶ X}` in that Over category.
- Arbitrary commutative condensed ring: `(Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`. This is precisely the unbundled form
  of the recorded `Profinite.CondensedRing = Mon (Sheaf ... Ab)` with commutative
  underlying monoid object. The single universe u is the existing profinite-site
  framework's universe convention, not an extra small-site universe equality.
- Commutative square: `(sq : CommSq g' f' f g)` has
  `sq.w : g' ≫ f = f' ≫ g`, namely f composed with g' equals g composed with f'.
- The categories are the dependency's actual `BoundedConstructible` categories of
  internal modules over `condensedRingObj Λ T.left`, on the small pro-etale sites.
  The functors in the signature are the recorded restricted derived pullbacks,
  from Y.left to X'.left. Diagrammatic `g* ⋙ f'*` denotes ordinary `f'* ∘ g*`.
- The first factor of the actual definition is
  `(boundedConstructibleUpperStarComp Λ ℓ f' g).symm`:
  `g* ⋙ f'* ≅ (f' ≫ g)*`, exactly the inverse of c_{f',g}.
- The middle factor is `eqToIso (by simp only [sq.w])`. Its endpoints are
  `(f' ≫ g)*` and `(g' ≫ f)*`. It is equality transport using only square
  commutativity, not an arbitrarily chosen isomorphism or a base-change theorem.
- The last factor is `boundedConstructibleUpperStarComp Λ ℓ g' f`:
  `(g' ≫ f)* ≅ f* ⋙ g'*`, exactly c_{g',f}.
- The return type is a natural isomorphism `≅` of these functors. The actual data
  are the `≪≫` composite of these three factors, including naturality and inverses
  supplied by the existing Iso operations. No object is chosen from bare existence.

Dependency declarations used:

- `sk-def-sfb-dc-setting`: the module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  documents and implements the above setting; its recorded
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField` supplies the
  chosen compactification where needed. This pullback-only definition does not
  invoke the compactification or add it as data. The categories are
  `AlgebraicGeometry.ProEtale.BoundedConstructible` and `boundedConstructible`.
- `def-sfb-dc-upper-star`: in the same module,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar` and
  `boundedConstructibleUpperStarCompatibility`; the former lifts the ambient
  derived pullback through the bounded-constructible inclusion, the latter is its
  inclusion compatibility.
- `def-sfb-dc-upper-star-comp`: in the same module,
  `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarComp`.
  I read its entire definition: it is the fully faithful preimage of the ambient
  composition comparison pasted with inclusion compatibilities and associators.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, declaration
  `Profinite.CondensedRing`. I read the abbreviation, its docstring and public
  import. The definition being recorded already takes its exact unbundled ring-object
  data, so no new module/import or private coefficient definition is needed.
- Generic operations were also read: `CategoryTheory.CommSq` (CommSq.lean:49),
  `CategoryTheory.Iso.trans` (Iso.lean:131) and `CategoryTheory.eqToIso`
  (EqToHom.lean:214), in Mathlib/CategoryTheory.

Edge cases checked by inspecting the construction:

- Reflexive commuting equality makes the middle factor an identity isomorphism.
  An identity square is admitted, with the usual identity-pullback identifications;
  the actual formula still uses the specified compositors, not a substituted map.
- A noncartesian square is admitted: for example X = Y = Y' = Spec k,
  X' empty, with the unique arrows from X' and identity arrows elsewhere. No
  pullback square proof or `IsPullback` occurs among the parameters.
- Empty schemes and the zero condensed ring are admitted. All factors remain
  functor isomorphisms and no nonempty/nonzero binder is introduced.
- Coefficients of characteristic equal to that of k are not excluded. In
  particular no `IsFinitenessCoefficient` or `IsEllAdicFinitenessCoefficient` is
  present in this definition (the former appears only in the following BaseChange
  section). The distinct-prime condition is exactly on k and ell as required.
- There is no bound on cohomological degree beyond the dependency's own bounded
  constructible category, and no cartesian or proper hypothesis.

Searches for an existing declaration:

1. `msearch.py ... leanfinder "pullback comparison natural isomorphism for a
   commutative square on bounded constructible derived categories with condensed
   ring coefficients"`: eight hits, including PresheafOfModules.pullbackComp,
   SheafOfModules.pullbackComp and Limits.instIsIsoPullbackComparison. These are
   general or underived operations, not this whole restricted comparison.
2. `msearch.py ... loogle "CategoryTheory.Iso.trans, CategoryTheory.eqToIso"`:
   ten hits including eqToIso_trans and eqToIso_map_trans; generic operations only.
3. `msearch.py ... grep
   "boundedConstructiblePullbackSquareComparison|pullbackSquareComparison|upperStarComp"`:
   zero Mathlib hits. The wrapper records these three queries in searches.jsonl.
4. `rg -n` for `boundedConstructiblePullbackSquareComparison|pullbackSquareComparison|
   det-def-sfb-base-change-morphism-comparison` in the slopmaster2 WeilConjectures
   tree: the Etale.pullbackSquareComparison declaration exists, but its bounded-below
   etale categories and fixed abelian coefficients do not match this item.
   `grep -rn` for this blueprint id in that source tree found no hit.
5. The same `rg -n` in shared `lean/Sheaf` and `lean/WeilConjectures` found the
   EXACT match in the pro-etale ModuleObject/BaseChangeTheorems/MorphismDefs.lean,
   and the existing consumer Sheaf.Paper.BoundedConstructibleBaseChange.
   The consumer calls `boundedConstructiblePullbackSquareComparison Λ ℓ sq`,
   consistently with the authoritative published interface.
6. `rg` for boundedConstructiblePullbackSquareComparison in
   dag/lean_names_upstream.json found no entry; this old index is not the published
   framework. The two `scompile.py --source` reads resolve that distinction and
   verify the exact signature, context and formula quoted above.

No statement fault or disputed statement was found. No claim of proof closure is
made for dependencies of this existing definition. The delivery adds no proof.

## Second reading by N3

I reread the node alongside the authoritative published source, checking each
binder and the three factors independently of the first search. This is the
worker's second pass; no second agent was started, in accordance with the dispatcher
brief. The maintainer supplies the independent delivery review.

The comparison starts with `g* ⋙ f'*` and ends with `f* ⋙ g'*`, so the order
matches ordinary `Lf'^* ∘ Lg^*` to `Lg'^* ∘ Lf^*`. The inverse compositor is
for `(f',g)`, the final compositor for `(g',f)`, and `sq.w` identifies their
intermediate morphisms in the required direction. All four finite-type/separated
triples and over-morphism domains match. The characteristic and arbitrary
commutative coefficient binders are exactly the ones required by the node.
The return type supplies naturality and inverse data; the body supplies precisely
the source's construction. No extra hypotheses were inherited from the later
restricted-pushforward section. No mismatch in the existing declaration was found;
the only adjustment during preparation was to quote the current published
Over-based signature rather than the older local explicit-k spelling.

## Validation

This is an existing-only delivery, with no new .lean file to compile. Source lookup
used only the authorized scompile.py wrapper. The required `deliver2.py N3 det-def-sfb-base-change-morphism-comparison --no-push`
completed successfully: `OK (dry run): commit 0ccd1f8ae9 passes the preflight and
compiles; nothing pushed`. The tool compiled its generated sandbox and library
checks of the existing declaration, each with the 60-second limit. The final
delivery repeats the prescribed checks before pushing.
