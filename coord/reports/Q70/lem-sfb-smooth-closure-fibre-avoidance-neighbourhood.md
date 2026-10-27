## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothClosureFibreAvoidanceNeighbourhood` states
`AlgebraicGeometry.exists_affine_smooth_closure_fibre_avoidance_neighbourhood`, with
one postponed theorem and no new definitions. The original statement and all
existing node fields other than `lean` are unchanged.

Hypotheses and clauses, checked against the node:

- Schemes and smooth morphism: `{X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]`.
  The explicit universe `u` is arbitrary; no extra size restriction is imposed.
- Locally Noetherian base: `[IsLocallyNoetherian S]`.
- Every base local ring is an integrally closed domain: `hnormal` quantifies over
  every `s : S`, with `IsDomain (S.presheaf.stalk s)` and
  `IsIntegrallyClosed (S.presheaf.stalk s)` as separate conjuncts, following the
  recorded normal-ring inline convention.
- Point and image: `(x : X)`; the base point `s` is written directly as `f x`.
- Local dimension at least two: `hdim : 2 ≤ ringKrullDim (X.presheaf.stalk x)`.
- The corresponding point in the ordinary scheme fibre is `f.asFiber x`.
  `hnongeneric` says it is not `IsGenericPoint` of any member of
  `irreducibleComponents (f.fiber (f x))`. This concerns the fibre, not `X`.
- Affine neighbourhoods: existential `T : S.Opens`, `V : X.Opens`, with
  `IsAffineOpen T`, `IsAffineOpen V`, `f x ∈ T` and `x ∈ V`.
  `e : V ≤ f ⁻¹ᵁ T` is exactly the containment required by the node.
- Set `A = Γ(S,T)` and `B = Γ(X,V)`. An affine open is canonically isomorphic to
  the spectrum of its section ring (`IsAffineOpen.isoSpec` / `fromSpec`), so no
  additional choice of rings or identifications is necessary. These section rings
  are genuine rings in universe `u`. The three predicates on `Γ(S,T)` assert
  Noetherian, domain and integrally closed, respectively.
- The induced map `V → T` is the existing `f.resLE T V e` and its smoothness
  appears explicitly. The ring map `(f.appLE T V e).hom.FinitePresentation`
  says exactly that `B` has finitely many generators and relations over `A`.
  Between affine schemes this is finite presentation of the scheme morphism.
- The closed set `Z = closure {x} ∩ V` is represented on each fibre by
  `((f.resLE T V e).fiberι t ≫ V.ι) ⁻¹' closure ({x} : Set X)`.
  Membership already restricts to `V`, because the displayed map factors through
  `V.ι`. No reduced structure is needed for a condition on underlying subsets.
- For every `t : T.toScheme` and every irreducible component `C` of its fibre,
  the statement requires `¬ C ⊆` that inverse image. This is precisely
  “contains no irreducible component”, including empty fibres.
- For every generic point `η` of `T`, expressed by `IsGenericPoint η Set.univ`,
  and every `z` in its fibre whose image lies in `closure {x}`, the local ring
  of that fibre at `z` has `ringKrullDim` at least two. The stalk is taken on
  `((f.resLE T V e).fiber η)`, not on `V` or `X`.
  This is a universal implication and imposes no nonemptiness on `Z_η`.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map` (def-pc-scheme, def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, its
  `component_noetherian` field (pqf-def-locnoeth).
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain` (def-weil-pbc-normal-ring).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (def-sbc-smooth-morphisms).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` (def-weil-residue-field).
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`
  (def-weil-pbc-krull-dimension-ring).
- `Mathlib.Topology.Sober`: `IsGenericPoint` (def-sc-generic-point).
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`
  (def-weil-irreducible-components, its exact Mathlib match).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`
  (def-weil-open-immersion), realized by the standard open inclusion `V.ι`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`
  (def-weil-pbc-noetherian-ring).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`;
  these implement the node's displayed pullback along the residue-field point.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Hom.resLE`, and the existing
  `appLE` ring map. `RingHom.FinitePresentation` is the existing algebra
  finite-presentation predicate, with the algebra induced by that ring map.

All five stated non-Mathlib proof dependency modules are imported plainly:
`Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents`
(`normal_topologicallyNoetherian_components`),
`WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct`
(`Scheme.normal_sections_finite_product`),
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
(`Scheme.IdealSheafData.reduced_induced_closed_subscheme`),
`WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity`
(`exists_open_fibre_dense_of_generic_dense`), and
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`
(`Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`).
Mathlib proof inputs are available through the statement imports and the
additional plain import `Mathlib.RingTheory.Ideal.Height`. The docstring carries
all nine DAG proof steps and names their dependencies.

Source verification: read the online English EGA IV4 21.14.3 and the first
reduction paragraph at https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html
(using Python HTTP retrieval after the web reader rejected the large page).
It takes the closure of `x`, shrinks to avoid fibre components by IV3 9.5.3,
and proves the generic-fibre dimension bound by specialization and equality
of generic-fibre stalks. The node's normal-domain affine shrinking is justified
by the recorded normal-components and normal-sections inputs.

Edge cases checked: an empty total space has no `x`; neighbourhoods cannot be
empty because they contain `x` and `f x`. Empty other fibres have no components.
An empty closure generic fibre makes the final implication vacuous; for example,
a closed point on the special fibre of the affine line over a DVR has total
local dimension two and is nongeneric in its fibre, while its closure has empty
generic fibre. A closed point of the affine plane over a field has dimension two,
is nongeneric and satisfies the nonempty generic-fibre case. Generic fibre points
and local dimension one are excluded by the two distinct explicit hypotheses.
There is no global integral or connectedness assumption on `S`: the conclusion
only chooses a domain neighbourhood. No characteristic restriction was added.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: “A nongeneric smooth fibre point admits affine
  neighbourhoods whose point closure avoids every fibre component and has local
  dimension at least two on the generic fibre”. Eight hits, concerning manifold
  fibrewise linear maps, immersion charts and real differentiable maps; no match.
- `msearch.py ... leansearch`: “A smooth morphism at a nongeneric fibre point
  admits affine neighbourhoods whose closure avoids all fibre components”.
  Eight hits: smooth chart constructors/recursors, smooth-at localization and
  relative-dimension composition. None contains the closure avoidance conclusion.
- `msearch.py ... loogle`: `"Smooth", "IsGenericPoint"`: zero hits.
- `msearch.py ... grep`: `closure.*(fiber|fibre)|(fiber|fibre).*closure` in
  Mathlib `AlgebraicGeometry`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for that expression and
  `smooth_closure|fibre_avoidance` found other fibre-closure dimension,
  associated-point, generic-cover and trace-formula statements, not this theorem.
  The item id is absent from `lean/WeilConjectures`. The proposed full theorem
  name is absent from Mathlib, both project source trees and
  `dag/lean_names_upstream.json`.

No statement dispute, dependency repair or new node is needed.

## Second reading by Q70

A second in-thread reading compared the completed Lean signature with the node,
including the fibre-point hypothesis, all affine/normal/Noetherian and finite
presentation clauses, avoidance of every whole component in every fibre, and
the stalk bound for every closure point of the generic fibre. No mathematical
mismatch was found. The use of section rings canonically identifies the affine
neighbourhoods with the requested spectra; the closure inverse image includes
the intersection with `V` automatically. In particular the generic-fibre stalk
is used in the final bound and the empty case remains allowed. No statement or
node correction resulted. This was an in-thread rereading, not an independent
agent review: the dispatch explicitly forbids starting agents, and the maintainer
provides the independent delivery review.

Validation: `scompile.py` passed in module mode (initial library check 2.4 seconds).
The final imports also compiled through the wrapper during
`deliver2.py --no-push`; the dry run reported OK, with preflight and per-file
compilation passing. Only the expected postponed-theorem warning is allowed.
