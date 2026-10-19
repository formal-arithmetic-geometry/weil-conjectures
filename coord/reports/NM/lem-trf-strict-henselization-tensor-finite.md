## Worker report

The module `Sheaf.TraceFormula.StrictHenselizationTensorFinite` states the finite base-change
comparison from Stacks Tag 0GIP, case (1). It uses the existing strict henselization colimit
(`Scheme.strictHenselizationRing`) and the published functorial strict-local maps. The helper
`strictTensorRing` is the Mathlib commutative-ring tensor product with the two algebra
structures induced by its two ring maps; `strictTensorLeft`, `strictTensorRight`, and
`strictTensorTmul` are its canonical inclusions and pure tensors.

The theorem's hypotheses render the node's `A → B` finite map as `[Algebra A B]` and
`[Module.Finite A B]`, and the arbitrary `A → C` map as `[Algebra A C]`. The chosen
geometric point is `s : Spec Ω ⟶ Spec (B ⊗[A] C)`, with `[Field Ω]` and `[IsAlgClosed Ω]`.
The definitions `strictTensorPointB`, `strictTensorPointC`, and `strictTensorPointA` are the
induced geometric points and therefore encode the primes `q`, `r`, and `p` (the point of the
tensor product encodes `m`). The maps `strictTensorMapAB`, `strictTensorMapAC`,
`strictTensorMapBD`, and `strictTensorMapCD` are the canonical maps of strict henselizations
transported through affine spectrum/global-section equivalences. `strictTensorPointCBaseEq`
proves the equality of the two induced maps to `Spec A`, and `strictHenselizationRingMapEq`
transports the C-side map to the common A strict henselization.

The conclusion supplies a ring homomorphism `φ` from
`B_q^sh ⊗[A_p^sh] C_r^sh` (the unfolded `strictTensorRing`) to
`(B ⊗[A] C)_m^sh` with `Function.Bijective φ`, hence a ring isomorphism. The first two
conjuncts say that the map restricts to the canonical B and C strict-local maps on the tensor
inclusions, which gives the compatibilities with `Spec B` and `Spec C` and the structure maps.
The final universal pure-tensor equation says evaluation at the selected geometric point is
`ε_B(b) * ε_C(c)`, giving compatibility with the tensor-product structure map and the chosen
point. No hypotheses beyond the finite/algebra and geometric-point data are added.

Every theorem proof is `sorry`; all definitions have real data. The module imports only
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`, which supplies the canonical
functorial strict-local map, and `Mathlib.RingTheory.TensorProduct.Basic`.

### Dependency declarations used

- `AlgebraicGeometry.Scheme.strictHenselizationRing` from
  `Sheaf.AlgebraicGeometry.StrictHenselization` (the recorded
  `def-weil-pbc-strict-henselization-limit` declaration).
- `AlgebraicGeometry.IsFinite` / `AlgebraicGeometry.IsIntegralHom` are the recorded Mathlib
  match for `def-weil-finite-integral-morphism`; the finite hypothesis is rendered by
  `Module.Finite A B`.
- `CategoryTheory.Limits.pullback` is the recorded Mathlib match for
  `def-pc-fibre-product`; the affine tensor product is Mathlib's pullback coordinate ring.
- `IsAlgClosed` and `Scheme.SpecToEquivOfField` are the recorded Mathlib match for
  `def-weil-geometric-point`.
- The dependency `lem-weil-pbc-strict-henselization-functoriality` is repaired in this
  delivery to use the full published declaration
  `AlgebraicGeometry.strictHenselizationFunctoriality` from
  `Sheaf.Paper.StrictHenselizationFunctoriality`. Its old record pointed only to
  `strictHenselizationClosedLift_over`, which does not provide the local map, residue
  compatibility, uniqueness, or neighbourhood compatibility needed here. The node copy's
  `lean.note` records this interface repair.

### Edge cases checked

The statement retains arbitrary (including zero) commutative rings, arbitrary `C`, and an
arbitrary tensor-product geometric point. No nonemptiness, reducedness, Noetherian, or
characteristic assumption is introduced. The empty tensor spectrum is covered vacuously by
the geometric-point binder. The pure-tensor clause covers zero factors and the unit tensor;
`Function.Bijective` expresses an isomorphism without choosing an inverse map or excluding
these cases.

### Searches made

- `msearch.py ... leanfinder "strict henselization commutes with tensor product when one ring map is finite"`:
  returned ordinary quasi-finite/étale/base-change declarations, no strict-henselization tensor theorem.
- `msearch.py ... loogle "StrictHenselization tensor finite"`:
  zero hits; `StrictHenselization` is unknown to Loogle.
- `msearch.py ... grep "strictHenselization|henselization.*tensor|tensor.*henselization" AlgebraicGeometry`:
  zero Mathlib hits.
- Repeated LeanSearch/LeanFinder searches for “base change of strict henselizations for a finite
  morphism” and “strict henselization tensor product finite ring map” returned only ordinary
  finite, étale, quasi-finite, and tensor-product permanence results.
- `rg` over `WeilConjectures/` and `lean/Sheaf` found the existing strict henselization
  construction and functoriality modules but no tensor-comparison statement.
- `grep -rl 'lem-trf-strict-henselization-tensor-finite' dag/nodes` found only this item and
  its blueprint references; no duplicate node or declaration exists.

## New nodes

None. The tensor-ring and canonical-map helpers are declarations in the owning module, with
source and blueprint docstrings, because they are components of this item's canonical
construction rather than independent notions.

## Dependency modules

The dependency module for **`lem-weil-pbc-strict-henselization-functoriality`** is the
copied node record
`dag/nodes/sec-proper-base-change/lem-weil-pbc-strict-henselization-functoriality.json`.
It records the published declaration
`AlgebraicGeometry.strictHenselizationFunctoriality` in
`Sheaf.Paper.StrictHenselizationFunctoriality`; its previous
`strictHenselizationClosedLift_over` interface was insufficient.  The copied record's
`lean.note` explains that this repaired interface supplies the local map, residue
compatibility, uniqueness, and neighbourhood compatibility required here.

## Second reading by NM

I reread the item statement, all four statement dependencies, and the module signature. The
finite assumption is exactly `Module.Finite A B`; `C` has only an algebra map. The four induced
points are used to form the strict henselizations, and `strictTensorPointCBaseEq` supplies the
only transport needed to put both factors over the same A strict henselization. The theorem
conclusion has one canonical comparison map, bijectivity, both tensor-factor compatibility
clauses, and the chosen-point evaluation clause. The compile wrapper reports no errors or
warnings. The dependency repair is reflected in the copied node and its note.
