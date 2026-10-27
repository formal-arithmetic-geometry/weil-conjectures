## Worker report

The module `Sheaf.AlgebraicGeometry.NormalizationAffineStalkClosure` states
`AlgebraicGeometry.normalization_affine_stalk_closure`, with its entire proof `sorry`.
It defines no new notion. The node is unchanged except for `lean`.

Hypotheses and objects:
- The field is `{k : Type u} [Field k]`.
- The scheme is `{X : Scheme.{u}} [X.Over (Spec (.of k))]`.
- Reducedness is `[AlgebraicGeometry.IsReduced X]`.
- Finite type of the structure map is the two existing classes
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`, exactly as its dependency record prescribes.
- The normalization and its morphism are the actual constructed
  `X.reducedNormalization` and `X.fromReducedNormalization` of the recorded dependency,
  not an arbitrary scheme with assumed normalization properties.

Conclusion, clause by clause:
- `IsNoetherian X ∧ IsNoetherian X.reducedNormalization` expresses locally Noetherian
  affine rings plus compactness of the underlying spaces. `Finite (irreducibleComponents X)`
  states finiteness of the component family.
- `IsFinite X.fromReducedNormalization ∧ Surjective X.fromReducedNormalization` states the
  two morphism properties using their recorded classes.
- The open `N` has membership equivalent, for every point, to
  `IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  `Dense (N : Set X)` and `IsIso (X.fromReducedNormalization ∣_ N)` give the dense normal
  locus and the isomorphism there, with no normality assumption on X.
- For every open `V`, the existential isomorphism identifies the actual inverse-image
  open with `V.toScheme.reducedNormalization`. Its equation with
  `V.toScheme.fromReducedNormalization` states compatibility with the normalization map.
- `jU` simultaneously provides all affine embeddings of the actual section rings of the
  inverse images into `FractionRing Γ(X,U)`. Here `FractionRing` is Mathlib's localization
  at `nonZeroDivisors`, including for reduced rings with zero divisors.
- On every nonempty affine open, the structural section map is injective and `.Finite`.
  `RingHom.Finite` is precisely `Module.Finite` for the module structure induced by that map;
  this avoids supplying an unrelated module instance. The map `jU U` is injective, extends
  the structural map to the canonical base-to-total-fractions map, and has image exactly
  `integralClosure Γ(X,U) (FractionRing Γ(X,U))`.
- `t` and `p : Fin t ≃ {p : Ideal Γ(X,U) // p ∈ minimalPrimes Γ(X,U)}` enumerate all minimal
  primes exactly once. The equivalence `q` identifies the total fraction ring with the
  dependent product of the fields `FractionRing (Γ(X,U) ⧸ (p i).1)`. Its base-element equation
  fixes each coordinate to the quotient map followed by the fraction map.
- `b` identifies the actual inverse-image section ring with the product of the integral
  closures of these quotients in their fraction fields. The equation
  `(b s i).val = q (jU U s) i` makes this the identification inside the specified ambient
  total fraction product, rather than an unrelated abstract ring isomorphism.
- The actual stalk `A_x` is `X.presheaf.stalk x`. The actual `C_x` is written directly as
  `((TopCat.Presheaf.pushforward CommRingCat X.fromReducedNormalization.base).obj
  X.reducedNormalization.presheaf).stalk x`. The structure map is the stalk functor applied
  to `X.fromReducedNormalization.c`. This is the underlying expression of the already
  available `normalizationPushforwardStalk`; importing its owning downstream singular-curve
  theorem would create an inappropriate dependency on the consumer. No duplicate definition
  is introduced.
- For every point, the theorem asserts reducedness and Noetherianity of `A_x`, injectivity
  and finiteness of the actual stalk structural map, and an injective `jx x` with image the
  integral closure in `FractionRing A_x`, commuting with that structural map.
- On an affine neighborhood, explicit `@IsLocalization` propositions use the germ algebra
  structures and `(U.2.primeIdealOf x).asIdeal.primeCompl` (respectively its image under the
  structural section map). These are exactly `A_x = R_p` and `C_x = (R\p)^(-1)T`, with
  their given germ maps, not only abstract ring isomorphisms.
- `qx` identifies `Q(A_x)` with the subproduct indexed by those `i` with `p_i ≤ p_x`.
  The map `ρ` extends the affine germ to total fractions; `qx (ρ z) i = q z i.1` specifies
  deletion of precisely the other factors. The final stalk equation commutes `jx`, `jU`,
  `ρ`, and the actual pushforward germ.
- The final clause supplies, for every affine inclusion, a total-fraction map extending
  restriction, and equates restriction of actual normalization sections with `jU` followed
  by that map. Along with the open-map and germ equations this states the requested
  restriction/localization compatibility.
- The empty scheme is permitted: there is no `Nonempty X` or `Nontrivial Γ(X,U)` hypothesis.
  Its componentwise normalization is the empty coproduct by the existing definition; its
  morphism is consequently the unique empty morphism. No nonempty affine open or point
  exists in this case. `N = ⊥` is dense in the empty space, so the global clauses include it.

Dependencies used directly (full signatures and docstrings were read):
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; its companion
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalizationComponent`,
  `Scheme.isIntegral_reducedNormalizationComponent`, `Scheme.reducedNormalization`, and
  `Scheme.fromReducedNormalization`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; integral morphisms are the
  corresponding `IsIntegralHom` class, although the conclusion asks only for finiteness.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed` and the normal
  domain conjunction with `IsDomain`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and the usual affine section/stalk objects.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, via `RingHom.Finite`.

The available recorded proof modules are imported privately, including upstream normalization
(transitively through ReducedNormalization), reduced-induced subschemes, affine pushforward
stalk localization, total fraction decomposition, and the reduced-normal characterization.
The Mathlib localization, support, and zero-dimensional localization proof tools are imported
privately as well. The two unstated proof nodes about componentwise generic properties and
normalization affine total fractions have no module to import; no substitute theorem is added.

Sources read: Stacks morphisms.tex Tags 035P, 0C3B, 0CDV, and varieties.tex Tag 0BXR.
The stalk source explicitly identifies the actual pushforward stalk with the integral closure
in the reduced local total fraction ring and the product of minimal-prime residue fields.
Reducedness here removes the reduction quotient. The componentwise source and finite-type
normalization source give exactly the scheme and finiteness used above.

Edge cases checked before finalizing:
- Empty X: described above, all conclusions remain meaningful.
- A normal affine domain: t = 1, normalization and stalk embeddings are the structural ones.
- A product of fields: one minimal prime per factor, normalization is the identity and
  localization removes the other factors.
- The crossing k[s,t]/(st): two field factors globally; at the crossing both survive and away
  from it exactly one survives. No false domain assertion is imposed on the crossing stalk.
- The cusp k[t^2,t^3]: the integral closure strictly contains the affine ring and the singular
  stalk, allowed by the image clauses; outside its support the structural map is an isomorphism.
- Characteristic is unrestricted, including imperfect base fields. No smoothness, separability,
  connectedness, properness, or dimension hypothesis has been added.

Searches:
- msearch.py leanfinder: "For reduced finite type schemes over a field componentwise
  normalization affine sections and stalks are finite integral closures in total fraction
  rings"; also "Normalization affine and stalk canonical integral closure in total quotient
  ring". The hits are relative-normalization affine/integrality results and function-field
  stalk results, not this combined statement for a reduced scheme with several components.
- msearch.py loogle: "integralClosure, IsLocalization" returned
  `IsLocalization.integralClosure` and
  `TensorProduct.toIntegralClosure_bijective_of_isLocalization`. These are the existing
  localization tools, not the required finite scheme statement.
- msearch.py grep: "normalization.*stalk|stalk.*normalization" in AlgebraicGeometry returned
  no Mathlib matches.
- rg on WeilConjectures and Sheaf for the same expressions and the node id found related
  relative/stalk and singular-curve statements. The singular-curve statements require extra
  properness/dimension/algebraically-closed hypotheses and are downstream users; none states
  the requested theorem. The reduced algebraic field-change module supplies global
  normalization properties but not this affine/stalk product statement.
- rg for `normalization_affine_stalk_closure` in Mathlib, WeilConjectures, Sheaf and the
  upstream name inventory found no existing declaration.

No statement correction, new nodes, or dependency-module repair is needed.

## Second reading by Q65

I reread the node and the final Lean side by side after elaboration. This is a second pass
by the same dispatcher-started worker; the brief prohibits starting another agent, so it
is not presented as an independent agent review.

The first draft's missing stalk and compatibility clauses were replaced before delivery:
the final signature explicitly quantifies the actual pushforward stalk, fixes its structure
map, gives the germ localization structures and surviving-component product, and adds both
germ and affine restriction commuting squares. The product is a dependent function type
`∀ i, ...`, not multiplicative `∏` notation on types. The normal locus is specified by the
normal-domain conjunction at every point. Both finite-type conditions and all global clauses
are present, while nonemptiness is imposed only for the affine assertion where the node
imposes it. The finite-module assertion uses the given structural map via `RingHom.Finite`.
The product and total-fraction equivalences are normalized on base elements and the embedding,
so they cannot float independently. The empty case follows from the existing componentwise
construction and is not excluded by any binder. No theorem has a proof other than `sorry`.
