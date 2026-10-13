## What changed

Marked `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits` as STATEMENT-DISPUTED,
without changing its signature, visibility, imports, docstring, or remaining proof.
Added three fully proved private declarations in the same module as certified
counterexample evidence: `empty_fixed_ring_no_iso`, `trivial_torsor_split_data`, and
`affine_torsor_fixed_orbits_counterexample`. They use Mathlib only and never apply
the disputed theorem. No repository files outside the sandbox were edited by the worker;
the prescribed delivery dry run performs its own temporary transaction.

The counterexample takes R = H = C = ℚ, g = 1, iota the identity, G = PUnit,
and rho constantly the identity algebra homomorphism. Let U = D(1) = Spec ℚ,
Y = U.toScheme, p = U.ι, j the identity, T = Y, t = p, and k the identity.
The algebra C over H is finite and faithfully flat, C is a domain, and g is
nonzero. The identities satisfy the action laws. The morphism j is finite and
etale. The torsor's projection q is the identity, so U.ι followed by q is etale.
The rotation condition holds: agreement after composition with the identity
algebra map gives a = b, and PUnit has exactly one element. The required equation
for k is the identity equation.

Choose d = 1. The pullback of p along itself has invertible second projection
(p is an isomorphism, in particular a monomorphism). Compose that projection's
isomorphism with the inverse of `coproductUniqueIso` for Fin 1. This constructs δ
and proves its exact projection equation in `trivial_torsor_split_data`.

Now choose m = 0 and the empty family K. The only hypothesis concerning these
choices is m ≤ d, which holds. The product B indexed by Fin 0 is the zero ring,
so Spec B, and every principal open inside it, is empty. Conversely, the base
change of p along the identity has a point: lift a point of U to the pullback.
`empty_fixed_ring_no_iso` proves that no nonempty scheme can be isomorphic to this
empty fixed-ring principal open. `affine_torsor_fixed_orbits_counterexample`
combines these constructions to negate the theorem's entire implication tail
specialized to this trivial torsor and identity cover. This is a refutation,
not a proposed reduction of the false assertion.

Compiled the complete delivery module using lcompile.py. The delivery dry run
also checks the declarations' axioms and the unchanged public signatures.

## Proved and sorry left

Holes closed: 0. Holes added: 0. Split off: 0.

`AlgebraicGeometry.Scheme.affine_torsor_orbit_data` was already proved and is unchanged.
The three private counterexample declarations named above are proved without sorry.
The sole remaining sorry is `AlgebraicGeometry.Scheme.affine_torsor_fixed_orbits`,
node `lem-sbc-affine-torsor-fixed-puncture-descent-core`. It remains intentionally
unproved because the stated assertion is false. No false intermediate statement
has been introduced to hide the error.

## No longer needed

None. No imports, nodes, or modules were removed. No replacement proof route is
claimed. The unit's statement and route were not changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `affine_torsor_fixed_orbits` quantifies universally over arbitrary
m and K with only m ≤ d. Neither the statement nor any premise relates them to the
orbit decomposition of the descent action. Its natural-language node instead says
"after choosing ... orbit representatives and stabilizers". This relationship is
essential, and cannot be recovered from a numerical upper bound.

The preceding attempt identified absent geometric theory but did not test m = 0.
The present failure is mathematical, not a missing Mathlib lemma or a still-sorry
dependency: a true collection of smaller statements cannot imply this assertion.
The node has one geometric proof step and an empty proof_deps list. There are no
stated dependency declarations whose imports would implement a valid proof of it.

The downstream parent module
`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescent` already exploits
this defect: `affine_torsor_orbit_data` chooses m = 0 for every d, and the parent's
proof sets every K to bottom and calls the core. The parent statement is an
existential, and can be true; its current proof uses a false universally quantified
core. Its repair must construct genuine orbit data, then prove descent for those
data (or retain the existential in the descent step). It must not use arbitrary
m and K. Merely replacing m ≤ d by m = d would still not specify stabilizers of
the actual action. The parent and other unheld modules were not edited: marking
a disputed theorem does not force a compilation adaptation.

Checked the cited sources. [Stacks Tag 03SF](https://stacks.math.columbia.edu/tag/03SF)
describes finite etale Galois covers and their corresponding finite group sets;
it does not allow arbitrary orbit counts or stabilizers. [Stacks Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
is Abhyankar's lemma for a regular divisor, with substantial geometric hypotheses.
Neither source asserts the false universal fixed-orbit claim. Existing docstrings
and DAG statements were preserved for the reader to decide the repair scope.

## Second reading by S4

1. **Signatures and visibility.** Compared the delivered module with the repository version. The public theorem `affine_torsor_fixed_orbits` is byte-for-byte unchanged in its signature, imports, visibility, and docstring; only the required dispute comment and private evidence declarations were added.

2. **Proof and axioms.** Compiled the complete module with `lcompile.py --all`. The existing theorem remains the sole named `sorry`; the three added private counterexample declarations are fully proved and introduce no `sorry`, `axiom`, or unsafe feature. Their proofs use only standard Lean/Mathlib constructions.

3. **Statement correctness.** Checked the counterexample at the smallest edge case `m = 0`, `d = 1`, with the identity torsor over `ℚ`, `G = PUnit`, and `K` empty. The hypotheses hold, while the fixed-ring product is the zero ring and its principal open has empty spectrum, whereas the pullback has a point. Thus the universal implication tail is false as written. No split-off statement was added.

4. **DAG and route.** The item node remains unchanged because its target statement is disputed rather than repaired. No imports or proof dependencies were removed, and the unit route is untouched. The report records that the parent currently chooses arbitrary empty orbit data and therefore needs a later mathematical repair.

5. **Pruning and changes.** No public declarations, definitions, or imports were changed, so there are no downstream adaptations or pruning claims. The only change is the explicit, certified counterexample evidence and this second-reading record.
