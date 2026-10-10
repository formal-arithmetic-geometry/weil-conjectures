Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fibre-spec-homeomorphism.json`: statement, Mathlib verdict `match`.
- `citations.json`: empty, because the item is a Mathlib leaf and has no proof steps.

Attachments:

None.

WANTED:

None.

What was checked:

The item statement was compared with Mathlib's `PrimeSpectrum.preimageHomeomorphFiber` in `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`, lines 212 onward. The Mathlib declaration assumes commutative rings `R`, `T`, an `R`-algebra structure on `T`, and a prime `p : PrimeSpectrum R`; it gives a homeomorphism between the set of primes of `T` whose comap is `p` and `PrimeSpectrum (p.asIdeal.Fiber T)`. The latter fibre ring is the residue field tensor product `kappa(p) tensor_R T`. Its inverse maps a prime of the tensor product to its contraction along the inclusion of `T`, exactly the map in the node after applying `Algebra.TensorProduct.comm` to use `T tensor_R kappa(p)`. The set of primes whose comap is `p` is the subspace `f^{-1}(p)` for the induced spectrum map. The source therefore covers all hypotheses and the claimed homeomorphism.

I also searched the whole DAG and blueprint for duplicate statements and checked the slopmaster2 source for an existing declaration tagged with this item; none was found. The small edge cases are consistent: for `T = R` the fibre is `Spec(kappa(p))`, and for a field base with `p = 0` it is the usual spectrum of `T tensor_R R`.

## Review by M1

I read the item node, its `sk-thm-iff` unit and `sec-proper-base-change` chapter metadata, and the Mathlib source at the declaration line. There are no proof steps or cited DAG nodes, so `citations.json` is correctly empty. I verified that the declaration's commutative-ring and algebra hypotheses match the node's ring-map setting, that `p.asIdeal.Fiber T` is the residue-field tensor product, and that the inverse homeomorphism contracts a tensor-product prime to the original `T` prime. I recorded the tensor-factor symmetry explicitly in `mathlib_match.how`, rather than treating the reversed tensor order as definitional. The item is marked `status: mathlib` and has the required split report and blueprint search record.

What could not be finished:

Nothing.
