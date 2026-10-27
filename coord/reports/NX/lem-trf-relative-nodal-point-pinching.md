# NX: lem-trf-relative-nodal-point-pinching

## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeNodalPointPinching` states
`AlgebraicGeometry.exists_relative_nodal_point_pinching`, with `sorry` as its only proof.
It introduces no definitions and changes the item's JSON only in `lean`. No new nodes,
dependency repairs, or statement corrections are needed.

The previous worker's stale-assignment diagnosis confused stages: Q70's reviewed delivery
recorded in the ledger at 2026-10-22 05:49 is a stage-1 split. The live node has no `lean`
record. This delivery retains that split, including all eleven proof steps and its new
09NN prerequisite, and supplies the requested stage-2 statement.

Hypotheses, matched individually:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The reference k-scheme is `S : Over (Spec (.of k))`. This supplies its actual structural
  morphism, without imposing finite type or separatedness.
- The semistable multipointed curve is `P : MultipointedCurve (Spec (.of k))`, with
  `[IsEmpty P.D]` and `hP : P.IsSemistable`. Thus its marking is the empty scheme, not
  an arbitrary marking. The landed definitions supply flatness, finite presentation,
  pure fibre dimension one, and geometric smooth-or-nodal singularities.
- The proper k-morphism is `s : Over.mk P.x ⟶ S` with `[IsProper s.left]`.
  `Over` supplies compatibility with the structural maps to `Spec k`.
- The finite disjoint unions are `E F : Over (Spec (.of k))`, the sizes `m n : ℕ`,
  the families of k-morphisms `ε` and `φ` from `Over.mk (𝟙 (Spec (.of k)))`, and
  `hE`, `hF`, which say their underlying scheme cofans are colimits. A coproduct of
  these copies of `Spec k` is exactly the required finite disjoint union. Every
  finite union admits such a numbering; no numbering or nonemptiness is imposed
  beyond choosing the given presentation. Both sizes may be zero.
- The closed immersion is `i : E ⟶ Over.mk P.x` with `[IsClosedImmersion i.left]`.
- Every point lies in the smooth locus by
  `hi : ∀ e : E.left, i.left e ∈ P.x.smoothLocus`.
- The k-morphism between the finite unions is `a : E ⟶ F`, its surjectivity is
  `[Surjective a.left]`, and its fibre size condition is `ha`, using
  `(a.left ⁻¹' {f}).encard = 1 ∨ (a.left ⁻¹' {f}).encard = 2` for each `f`.
- The supplied map is `b : F ⟶ S`; its compatibility is `hs : i ≫ s = a ≫ b`.

Conclusions, matched individually:

- The output curve is `Q`, with `IsEmpty Q.D ∧ Q.IsSemistable`; thus the actual
  output scheme `Q.X` has the asserted unmarked semistable structure and structural
  map `Q.x` to `Spec k`.
- The map from X is `v : Over.mk P.x ⟶ Over.mk Q.x`, the map from F is `j`, and the
  induced map to S is `t`. Their compatibilities are `v ≫ t = s` and `j ≫ t = b`.
- Existence of the scheme pushout, including its full universal property for maps
  to every scheme, is `IsPushout i.left a.left v.left j.left`. This is in `Scheme`,
  not merely in the category of schemes over S or k.
- Finiteness and surjectivity of X to Y are `IsFinite v.left ∧ Surjective v.left`.
- The immersion of F is `IsClosedImmersion j.left`.
- Scheme-theoretic inverse image is the actual cartesian square
  `IsPullback i.left a.left v.left j.left`, not a pointwise inverse-image condition.
- The complements are opens `U` and `V` with underlying sets `(Set.range i.left)ᶜ`
  and `(Set.range j.left)ᶜ`. Their isomorphism `e` satisfies
  `e.hom ≫ V.ι = U.ι ≫ v.left`, specifying the map induced by v.
- Properness of the induced map is `IsProper t.left`.
- For a singleton fibre, `∀ z', a.left z' = f ↔ z' = z` specifies exactly its sole
  point. The next existential gives neighbourhoods of `i.left z` and `j.left f`,
  an isomorphism between them, and the same compatibility with v.
- For each double fibre, `z : Fin 2 → E.left`, its injectivity, and
  `∀ z', a.left z' = f ↔ z' ∈ Set.range z` specify the two distinct preimages,
  in either order. The family `α` identifies the two actual maximal-ideal
  completions of the smooth stalks with `PowerSeries k`. The family `ρ` identifies
  their residue fields, written as quotients by their maximal ideals, with k.
  The first equation preserves the given scalar maps `Orgogozo.localScalar P.x`;
  the second says exactly that the residue maps of the completed local rings are
  `PowerSeries.constantCoeff`, namely evaluation at zero. In particular `ρ` is
  compatible with the scalar map as a consequence of those two equations.
- `γ` identifies the completed local ring at `j.left f` with the categorical ring
  pullback of the two `CommRingCat.ofHom PowerSeries.constantCoeff` maps. This is
  exactly `k[[u]] ×_k k[[v]]`, using Mathlib's existing limits, without a private
  fibre-product construction.
- The following equation specifies the two branch projections on germs using the
  actual stalk map of v. Its equality argument
  `h : v.left (i.left (z l)) = j.left f` only transports between equal stalks via
  `stalkCongr`. Such an h follows from the pushout square and the double-fibre
  hypothesis, so it is not an additional restriction on the theorem's data. For
  `l = 0` it uses `pullback.fst`; for `l = 1` it uses `pullback.snd`.
- `δ` identifies this ring pullback with the already landed `Orgogozo.nodeRing k`,
  whose definition is `MvPowerSeries (Fin 2) k` modulo the ideal generated by uv.
  The last scalar equation makes the composite `δ ∘ γ` preserve the specified
  k-structure, rather than only giving an abstract ring equivalence. Thus it
  also exhibits an ordinary double point in the existing sense.
- The subcurve is any scheme `D` with map `d : D ⟶ P.X`, `IsReduced D`, and
  `IsClosedImmersion d`. The existential family `C ⊆ irreducibleComponents P.X`
  with `Set.range d = ⋃₀ C` says exactly that its closed support is a union of
  irreducible components. The fibre bound is the `encard ≤ 1` condition on
  `{z | a.left z = f ∧ i.left z ∈ Set.range d}`. Its conclusion is
  `IsClosedImmersion (d ≫ v.left)`. A closed immersion identifies its reduced
  source with its image, which consequently already has the reduced scheme
  structure; no arbitrary replacement of D or nonreduced image is introduced.
- There is no separatedness assumption on `P.X` or `S.left` over k.

Dependency declarations used, read from their recorded modules:

| Node | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` |
| def-weil-algebraic-closure | `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric-fibre definition uses `AlgebraicClosure` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper` |
| def-trf-multipointed-curve | `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve` |
| def-trf-multipointed-curve-modification | `Sheaf.AlgebraicGeometry.MultipointedCurveModification`: `MultipointedCurve.IsSemistable` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion` |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` |
| def-weil-pbc-category-colimit | `Mathlib.CategoryTheory.Limits.HasLimits` and its shapes API: `IsColimit`, `Cofan.mk`, `IsPushout` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` |
| def-weil-pbc-adic-completion | `Mathlib.RingTheory.AdicCompletion.Basic`, `Algebra`: `AdicCompletion`, its canonical algebra map, `AdicCompletion.evalOneₐ` |
| def-weil-pbc-multivariate-power-series | `Mathlib.RingTheory.MvPowerSeries.Basic`, `Mathlib.RingTheory.PowerSeries.Basic`: `MvPowerSeries`, `PowerSeries`, `PowerSeries.constantCoeff` |
| def-pc-reduced-scheme | `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` |
| def-weil-irreducible-components | `Mathlib.Topology.Irreducible`: `irreducibleComponents` |

Statement imports are public; the remaining available proof modules are imported privately:
`Sheaf.AlgebraicGeometry.FerrandSchemePushout` (`exists_ferrand_scheme_pushout`),
`Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.RingTheory.FinitePresentation`,
`Mathlib.RingTheory.AdicCompletion.Exactness`,
`WeilConjectures.RingTheory.CompletionFiniteExtension`,
`WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.RingTheory.CompletionRegularLocal`,
`WeilConjectures.RingTheory.CompletionDimension`,
`Sheaf.AlgebraicGeometry.IsRegularScheme`,
`Sheaf.RingTheory.RegularCompleteCoefficientCoordinates`, and
`Mathlib.RingTheory.AdicCompletion.Completeness`.
The remaining Mathlib proof dependencies (separatedness, finite-type cancellation,
universal closedness, geometric fibres and adic completeness) are already supplied by the
public statement imports or these proof imports. The newly split
`lem-trf-codimension-one-points-affine-neighbourhood` currently has no recorded Lean
module; it is a proof prerequisite, so no unstated module is imported and no new
statement interface for it is needed here. The theorem docstring preserves its use in
step 1, and all eleven steps of the reviewed proof are retained.

Sources opened: Stacks `more-morphisms.tex`, the 0E25 pushout proposition and
0E26 separatedness/0E27 finite-type lemmas; `varieties.tex`, 09NN at lines 9141–9146;
`curves.tex`, 0E36 at lines 2915–2951 and 0C1J at lines 2984–3011.
The local ring square in 0E36 is used with the actual residue maps, not merely with
unspecified morphisms between isomorphic rings.

Edge cases checked before writing:

- `m = n = 0` gives empty coproducts. All fibre conditions and local calculations are
  vacuous; the pushout is X and the complement isomorphism is the identity.
- A singleton fibre gives a local isomorphism and introduces no singularity.
- A double fibre consists of two distinct smooth points, including when both belong
  to the same irreducible component. The conclusion gives the usual self-node too.
- The power-series calculation does not divide by 2, so characteristic 2 is included.
- No finiteness or separatedness assumption on S over k appears. Properness is only
  relative to S, matching the use of affine opens of S in the proof.
- D may be empty (empty `C`, zero quotient ring), the whole curve when the fibre bound
  permits it, or a disconnected union of components. The condition correctly excludes
  a subcurve containing both points of a double fibre.
- The curve itself is not required to be connected or nonempty. All schemes and k are
  at the common Mathlib scheme universe u; finite indices `Fin m`, `Fin n` and `Fin 2`
  impose no restriction on the finite sets being represented.

Searches for existing statements and notions:

1. `msearch.py ... leanfinder "A pushout of a curve along finitely many smooth points identifying at most two points is semistable with ordinary nodes, finite and proper over a reference scheme"`:
   eight hits, smooth relative-dimension composition/base-change properties and
   `IsIntegralHom.instDescScheme`; none states this theorem.
2. `msearch.py ... loogle "IsPushout, IsClosedImmersion, IsFinite"` and the follow-up
   `loogle "CategoryTheory.Limits.IsPushout"`: both returned zero hits and reported
   that Loogle does not know the pushout identifier. No existence match was inferred
   from these search-service limitations.
3. `msearch.py ... grep "pinch|Pinch|nodal|Nodal" AlgebraicGeometry`: zero hits.
4. `rg -n 'pinch|Pinch'` in `lean/WeilConjectures/AlgebraicGeometry`,
   `lean/Sheaf/AlgebraicGeometry`, and `lean/Sheaf/TraceFormula`: found the general
   Ferrand theorem, affine closed pinching, the DVR pinching theorem and consumers.
   Ferrand gives no nodal conclusion, and the DVR theorem has different hypotheses
   (projective relative curve and étale double branches over a DVR), so neither is
   an exact statement of this node. Both relevant source modules were read.
5. `rg` for the item's id in `lean/WeilConjectures` found no declaration.
   `rg` for `exists_relative_nodal_point_pinching` across Mathlib, WeilConjectures,
   and Sheaf found no name collision.
6. Targeted source searches found the already landed definitions of
   `MultipointedCurve.IsSemistable`, `Orgogozo.nodeRing`, and `Orgogozo.localScalar`;
   those are reused. Mathlib's ring pullback and power series definitions are used
   directly. There are no helper definitions to duplicate.

Validation: the prescribed `scompile.py NX lem-trf-relative-nodal-point-pinching`
compiled the delivered file both as a sandbox module (16.1 seconds) and under its
actual module name (19.8 seconds), with no errors or unexpected warnings. The first
probe exposed a missing pair of parentheses around each cofan's morphism type;
that syntax was repaired before the clean compile. `autoImplicit` and
`relaxedAutoImplicit` are disabled, and every source line has at most 100 characters.

No `STATEMENT-DISPUTED` issue was found. The natural-language statement, proof,
statement dependencies and proof dependencies are unchanged.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
