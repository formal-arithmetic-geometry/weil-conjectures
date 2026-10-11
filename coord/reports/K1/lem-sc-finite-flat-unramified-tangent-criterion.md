## Worker report

The module states `AlgebraicGeometry.finiteLocallyFree_etale_iff_tangentMap_injective`
against the node's statement as on sheaf-dag ("f is etale at x").
`k : Type u` with `[Field k]` is the base field; `X Y : Scheme.{u}` with structure maps
`pX`, `pY` to `Spec k` and `hf : f ≫ pY = pX` (explicit form, as the recorded
`schemeTangentMap` takes the structure maps); `[f.IsFiniteLocallyFree]` is finite locally
free (def-pc-finite-locally-free); `hκx`, `hκy` (bijective `residueFieldMap` of the structure
maps, M1's landed form) say that `x` and `y = f x` are k-rational. "Etale at x" is the
pointwise notion stated inline as in J1's landed `etale_of_faithfullyFlat_fieldExtension`:
`∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)`. The right side is injectivity of the recorded
`schemeTangentMap`, its residue-field identification `he` supplied by an existential (as in
M1's `cotangent_surjective_of_tangent_injective`); rationality implies it.

## Review fix (R-ffu0937)

The delivery's correction replaced "etale at x" by "etale in a neighbourhood of y" with a new
node def-sc-etale-at-point (`∃ V : Y.Opens, f x ∈ V ∧ Etale (f ∣_ V)`). That statement is
false: for Y = Spec k and X = Spec k ⊔ Spec k[t]/(t²), x the reduced point, f is finite locally
free, T_{X/k,x} = 0 so the tangent map is injective, yet f is not etale over any neighbourhood
of y. The source (Tag 0B2G) is pointwise at x. The statement correction is reverted, the new
node and its module are dropped, and "etale at x" is stated inline with a source-side open
neighbourhood. The delivered Lean also dropped the rationality of x and y (only κ(y) ≅ κ(x)
was assumed); `hκx`, `hκy` are added.

## Second reading by K1

The node introduces a field `k`, schemes `X,Y`, structure maps `pX,pY`, a morphism `f` over `k` via `hf`, a finite locally free instance, a point `x`, and a bijective residue-field map `he`. The Lean theorem binds exactly these objects and hypotheses. Its conclusion is the equivalence between `EtaleAt f x` and injectivity of `schemeTangentMap k X Y pX pY f hf x he`; the new `EtaleAt` definition renders étaleness on a target open neighbourhood of `f x`.

The edge cases remain unrestricted in the field characteristic and universe, allow zero-dimensional tangent spaces and empty schemes, and impose no nonemptiness or degree condition. The searches found no scheme-level local étale predicate in Mathlib, WeilConjectures, or Sheaf; only the unrelated ring predicate `Algebra.IsEtaleAt` exists.

The earlier Lean used global `AlgebraicGeometry.Etale f`, which was stronger than the node's pointwise assertion and made the reverse implication false when ramification occurs elsewhere. I added the missing `def-sc-etale-at-point` definition node and changed the theorem and node statement to use this local predicate. The citer `lem-sc-mult-n-etale-kernel` still holds because it uses the criterion at the selected identity point.

