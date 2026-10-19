## Worker report

The delivery states `AlgebraicGeometry.sepClosed_valuation_geometric_components` in
`Sheaf.AlgebraicGeometry.SepClosedValuationGeometricComponents`. Its only proof is `sorry`.
There are no new definitions, dependency repairs, or changes to the node's natural statement.
The theorem docstring records the seven-step proof in the DAG, including the generic-stalk
argument needed to preserve reducedness of each component.

Hypothesis and clause matching:

- The separably closed field K is `(K : Type u) [Field K] [IsSepClosed K]`.
- The embedded subring is `(V : Subring K)`. Its canonical inclusion provides the scalar
  structure; `[IsFractionRing V K]` specifies the fraction field K. The node's valuation
  condition is exactly `hV : ∀ a : K, a ≠ 0 → a ∈ V ∨ a⁻¹ ∈ V`.
- An arbitrary prime ideal is the point `p : Spec (CommRingCat.of V)`. The field k is the
  recorded dependency's `(Spec (CommRingCat.of V)).residueField p`. This is the stalk
  modulo its maximal ideal. `Spec.residueFieldIso` identifies it canonically with
  `p.asIdeal.ResidueField`; `Ideal.ResidueField` is the residue field of `V_p` and has
  Mathlib's `IsFractionRing (V ⧸ p.asIdeal) p.asIdeal.ResidueField` instance. Thus this
  is exactly the stipulated Frac(V/p), using the dependency's existing scheme interface,
  not a newly chosen or unrelated field.
- The first conjunct `IsSepClosed ...` asserts separable closedness of this k. It is a
  conclusion, never an assumption on the later geometry.
- Every finite type k-scheme is `(Z : Scheme.{u})` with the structure map `f` to `Spec k`
  and `[LocallyOfFiniteType f] [QuasiCompact f]`. These are precisely the two parts of
  finite type in the recorded dependency. `[GeometricallyReduced f]` expresses reducedness
  after every field extension; its Mathlib definition tests all maps from field spectra.
- A component is `T : TopologicalSpace.Closeds Z` satisfying
  `(T : Set Z) ∈ irreducibleComponents Z`. Components are closed, so the bundled closed-set
  parameter does not exclude any component. Its reduced induced structure is exactly
  `(Scheme.IdealSheafData.vanishingIdeal T).subscheme`, with inclusion `subschemeι`,
  as in the recorded reduced-induced-closed-subscheme theorem.
- For every `(L : Type u) [Field L] [Algebra k L]`, the scheme `Z_L` is
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))`. If π is its first
  projection and i is the component inclusion, `pullback i π` is `C ×[Z] Z_L`,
  canonically `C ×[Spec k] Spec L` by pullback pasting. The conclusion `IsIntegral
  (pullback i π)` includes reducedness, irreducibility, and nonemptiness of this actual
  base-changed component; no arbitrary scheme or comparison map is supplied as a hypothesis.
- Every algebraic closure is covered by `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`, not just one chosen model.
- `Set.BijOn (Set.preimage π) (irreducibleComponents Z)
  (irreducibleComponents ↥(pullback f ...))` is precisely the assignment
  C ↦ C_Ω on component supports, with the canonical inverse-image map specified.
- The final clause uses a closed set D whose underlying set equals `π ⁻¹' T` and says
  `(pullback.snd i π).ker = Scheme.IdealSheafData.vanishingIdeal D`. The projection
  `pullback.snd i π` is the canonical base-changed closed immersion. Equality of these
  ideal sheaves identifies its closed subscheme with the reduced induced structure on D,
  by the recorded dependency's uniqueness clause. This encodes the statement about
  structures as well as its topological bijection. D is not extra input to an assumption:
  every such closed representative is covered by the conclusion.
- No finite-height, Noetherian, properness, smoothness, or perfection hypothesis appears.

The universe `u` is bound explicitly. Schemes, residue fields, and extension fields follow
Mathlib's common ambient scheme universe; there is no smaller independent test universe.
All variables are explicitly bound, and there are no local notations, instances, `let`
binders, hidden constructions with `sorry`, or newly proved helper theorems.

Dependency declarations read and reused:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`, `IsSepClosure` (only the former is
  needed here); `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, its field instance,
  `Spec.residueFieldIso`; the node's `Scheme.Hom.residueFieldMap` is not needed since no
  morphism of residue fields is asserted here.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.fst`,
  `pullback.snd`; scheme pullbacks are supplied by the geometry imports.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` (maximal irreducible subsets).
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`; its existing construction
  `vanishingIdeal`, `subscheme`, `subschemeι` is used directly.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, `IsReduced`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`; the dependency's
  `AlgebraicClosure` is the distinguished example, but the theorem covers all examples.

Proof-only imports preserve the DAG route: valuation-ring normality; the normal-scheme
étale theorem (09Z9); the subset geometric-irreducibility criterion; the generic-stalk
geometric-reducedness criterion; product component bijection; minimal-prime localization
and localization/tensor calculations. The field-tensor theorem is imported from the
published `Sheaf.FieldTheory.FieldTensorUniqueMinimalPrime`, already used by the subset
criterion. Its public theorem `IsSepClosed.field_tensor_unique_minimalPrime` has exactly
its recorded signature. The recorded upstream module is available through `scompile.py
--source`, and was read too, but importing it alongside the subset criterion would add a
second module defining the same names. The existing side owner is therefore imported once.
No proof dependency node was changed.

Edge cases checked mathematically: V=K is the trivial valuation and p is its zero prime;
p=(0) for any V recovers K; arbitrary nonmaximal primes and valuations of unbounded rank
are allowed. If Z is empty, there are no components and the canonical map is the empty
bijection; no integrality of the empty scheme is asserted. For Z=Spec(k[x,y]/(xy)), the
components are the two reduced axes, whose base changes remain integral. Imperfect
separably closed k is allowed: a nontrivial purely inseparable finite field extension of k
would be reduced but fail the geometric-reducedness hypothesis, explaining why that
hypothesis cannot be dropped. The identity extension L=k is included.

Searches for existing notions/statements (full msearch responses are in the sandbox's
`searches.jsonl`):

- `msearch.py leansearch`, query “Residue fields of valuation rings in separably closed
  fields are separably closed”: eight hits, including `Valued.ResidueField`, `IsSepClosed`,
  `IsSepClosure.sep_closed`, and residue extension separability statements. None is the claim.
- `msearch.py leanfinder`, query “Residue fields of valuation rings in separably closed
  fields are separably closed, and components of geometrically reduced schemes over them
  are geometrically integral”: eight hits, including the existing scheme residue field,
  `Algebra.IsGeometricallyReduced`, and separability of formally unramified residue maps;
  no matching theorem.
- `msearch.py loogle`, query `IsSepClosed, ValuationRing`: no hits.
- `msearch.py grep`, query `isSepClosed.*residue|[Gg]eometrically.*[Cc]omponent|
  [Cc]omponent.*[Gg]eometrically`: three hits, in Geometrically/Reduced, Irreducible,
  and Connected. These concern already geometrically reduced/irreducible morphisms;
  they do not provide this theorem.
- `rg` of the upstream WeilConjectures source, side `lean/Sheaf`, and the upstream name
  inventory for the item id and patterns `sepclosed.*valuation`, `sepClosed.*residue`,
  geometric components: related consumers and component lemmas, no duplicate theorem.
  `grep -rn` for the item id upstream likewise finds no declaration of the item.

Sources read: local Stacks varieties.tex at `lemma-separably-closed-irreducible` (020J),
`lemma-separably-closed-field-irreducible-components` (038H), and
`lemma-generic-points-geometrically-reduced` (04KS); the recorded upstream 09Z9 theorem
and its complete signature; the dependency modules listed above. The source-place metadata
still mentions the older monic-polynomial proof, but its residue-field statement agrees with
the current seven-step normal-stalk argument. No statement correction or dispute is needed.

Validation: the initial compile detected a scheme/type coercion ambiguity in component
sets; adding the explicit carrier coercions `↥(pullback ...)` repaired it. The statement
then compiled cleanly both as a sandbox module and under its final library module name
through `scompile.py`, within the 60-second limit. The final dry run and delivery perform
the required complete checks again.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
