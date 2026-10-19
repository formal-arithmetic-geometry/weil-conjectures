## Worker report

The module `Sheaf.TraceFormula.FibreAssociatedPrimesModuleRing` declares the
canonical source-oriented fibre map
`RingTheory.fibreRingMap A B p : B →+* B ⊗[A] p.ResidueField` and states
`RingTheory.fibre_associated_primes_module_ring`.  The theorem uses Mathlib's
`p.ResidueField`, the tensor product `B ⊗[A] p.ResidueField`, and the project's
`RingTheory.annihilatorAssociatedPrimes` (exact element annihilators).

The Lean statement renders the node clause by clause.  The ring homomorphism
`A → B` is the algebra map `[Algebra A B]`; `p` is a prime ideal through
`[p.IsPrime]`; `L` is an arbitrary additive commutative group with a module
structure over the fibre ring.  The displayed `Set.BijOn (Ideal.comap
(fibreRingMap A B p)) ...` is the contraction bijection from associated primes
of the fibre ring to associated primes of `B`, with the `B`-module structure
written explicitly as `Module.compHom L (fibreRingMap A B p)` so that it is exactly
restriction of scalars.  For each `z : L`, the first equality says contraction of
the fibre annihilator is the `B` annihilator, the second says the fibre
annihilator is the ideal extension `Ideal.map fibreRingMap` of the `B`
annihilator, and the final equivalence says the two annihilators are prime
simultaneously.  The last clause states that every associated `B`-prime
contracts along `algebraMap A B` to `p`, which is the restriction to the fibre of
the fibre-prime correspondence.  There are no flatness, Noetherian, or other
extra hypotheses.

Dependencies used: `Sheaf.RingTheory.AnnihilatorAssociatedPrimes`, declaration
`RingTheory.annihilatorAssociatedPrimes`; `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`,
including `Ideal.ResidueField`, the tensor fibre construction, and the canonical
prime correspondence (`PrimeSpectrum.preimageOrderIsoFiber` and its contraction
lemmas); Mathlib's tensor-product definitions provide `B ⊗[A] p.ResidueField`.
The recorded localization-at-a-prime and module-tensor-product dependencies are
Mathlib declarations imported transitively by the fibre module and are used by
the node proof plan.

Edge cases checked: `z = 0` makes both annihilators top and the equalities remain
well typed; the zero fibre/module is permitted; `p` may be any prime (including a
minimal or maximal prime); no nonemptiness, flatness, finite generation, or
Noetherian condition is imposed; all three universes `u`, `v`, and `w` are
explicit and independent.  The source tensor order `B ⊗[A] κ(p)` is used
literally, with `fibreRingMap` the map `b ↦ b ⊗ 1`; Mathlib's reversed fibre
convention `κ(p) ⊗[A] B` is related by its canonical tensor commutation in the
recorded fibre-prime dependency.

Searches made: `msearch.py Q96 lem-trf-fibre-associated-primes-module-ring
leanfinder "associated primes of a module over a fibre tensor ring and its
restriction of scalars"` returned only localization and support results, with no
matching theorem; `msearch.py ... loogle "associatedPrimes, TensorProduct,
Ideal.comap"` returned zero hits; `msearch.py ... grep
"associatedPrimes.*TensorProduct|fibre.*associated|Fiber.*associated"
Mathlib/RingTheory` returned zero hits.  Direct `rg` over
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
`lean/Sheaf` found no declaration of this fibre associated-prime comparison, and
grep for the node id in the source found no existing declaration.  The existing
Mathlib associated-prime API concerns radical annihilators or localization and
therefore does not state this arbitrary-ring result.

The file was compiled with `scompile.py`; it produced no errors or warnings.

## Second reading by Q96

I reread the node, all four statement dependencies, and the module after the
successful compile.  The algebra map, prime ideal, fibre tensor, module, and
restriction-of-scalars action are all present.  `Set.BijOn` gives exactly the
contraction bijection; each of the three per-element assertions is explicit;
and the final contraction-to-`p` clause is retained.  No source hypothesis was
added or dropped, and the canonical tensor inclusion is used instead of an
arbitrary map.  No mismatch was found.
