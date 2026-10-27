## Worker report

The module `Sheaf.RingTheory.BasisOfMaximalResidueBases` states
`Module.bijective_linearCombination_of_maximal_residue_bases`, with its proof
left as `sorry`. It introduces no definitions. The node changes only in `lean`.
The source read is Stacks Project `algebra.tex`, lines 19291–19351: Tag 02M9's
last proof hint and Tag 03C1's opening basis-lifting argument. This node supplies
the prescribed-vector globalization step, rather than the semilocal selection
of vectors. Its five proof steps are reproduced in the theorem docstring.

The statement correspondence is as follows.

- A commutative ring E: `{E : Type u} [CommRing E]`. There is no nontriviality
  assumption and no semilocality assumption.
- An E-module P: `{P : Type v} [AddCommGroup P] [Module E P]`. The universes
  of E and P are independent. No global finite-generation, flatness, finite
  presentation, or freeness assumption is introduced.
- The nonnegative integer r and prescribed elements: `(r : ℕ) (n : Fin r → P)`.
  The labels `0, …, r-1` replace `1, …, r` without changing the family.
- Every maximal ideal q: both hypotheses quantify over
  `∀ (q : Ideal E) [q.IsMaximal]`. Its primality is supplied by Mathlib.
- The objects E_q and P_q are exactly `Localization.AtPrime q` and
  `LocalizedModule q.primeCompl P`, using the recorded dependency declarations.
- The assumption P_q ≅ E_q^r is
  `Nonempty (Module.Basis (Fin r) (Localization.AtPrime q)
  (LocalizedModule q.primeCompl P))` in `hfree`. A basis is a linear
  equivalence with finite-support coordinates. For `Fin r`, these coordinates
  are the finite direct sum E_q^r. No basis vectors at this localization are
  prescribed by this hypothesis, matching the node.
- The quotient P/qP is literally `P ⧸ (q • (⊤ : Submodule E P))`; its scalar
  ring is literally `E ⧸ q`. Mathlib's quotient scalar action is used.
- The prescribed residue family is a basis precisely when there exists
  `b : Module.Basis (Fin r) (E ⧸ q) (P ⧸ (q • (⊤ : Submodule E P)))`
  with `∀ i : Fin r, b i = (q • (⊤ : Submodule E P)).mkQ (n i)`.
  This is `hres`; the equation retains each prescribed vector and its index.
- The map φ is `Fintype.linearCombination E n : (Fin r → E) →ₗ[E] P`.
  Its definition, read in `Mathlib.LinearAlgebra.Finsupp.LinearCombination`,
  sends `a` to `∑ i, a i • n i`. A finite product of coordinates represents
  the finite direct sum in the node. The conclusion is exactly
  `Function.Bijective (Fintype.linearCombination E n)`.
- The node's equivalent basis formulation is represented by this same
  bijectivity conclusion: the inverse coordinate equivalence is a basis
  whose ith vector is n i. No separate stronger conjunct is imposed.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule` and
  `LocalizedModule.mkLinearMap`, module
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. The definition is the
  fraction construction, not a new abstract localization.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`, module
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, the localization at
  `q.primeCompl`. The recorded ancillary `Ideal.ResidueField` and `Ideal.Fiber`
  declarations were also inspected; the statement needs E/q itself.
- `def-weil-pbc-free-module`: `Module.Free` and `Module.Basis`, modules
  `Mathlib.LinearAlgebra.FreeModule.Basic` and
  `Mathlib.LinearAlgebra.Basis.Defs`. The exact fixed-rank assumption uses
  `Module.Basis`, rather than unspecified-rank `Module.Free`.
- The quotient scalar action is Mathlib's instance in
  `Mathlib.Algebra.Module.Torsion.Basic`, lines 641–649.
- The proof dependencies are already Mathlib leaves and are imported with
  plain imports: `IsLocalRing.map_mkQ_eq_top` from
  `Mathlib.RingTheory.LocalRing.Module`,
  `OrzechProperty.bijective_of_surjective_endomorphism` from
  `Mathlib.RingTheory.OrzechProperty`, and `bijective_of_localized_maximal`
  from `Mathlib.RingTheory.LocalProperties.Exactness`. Their full signatures
  and surrounding assumptions were read. They require no dependency repairs.

Edge cases checked mathematically before writing:

- Zero ring: there are no maximal ideals, so both hypotheses are vacuous;
  every E-module is zero since p = 1 • p = 0 • p = 0. The coordinate map
  is bijective for every r. No `[Nontrivial E]` excludes this case.
- Rank zero over any ring: local freeness forces every maximal localization
  of P to vanish, hence P = 0 by the localization criterion. `Fin 0` is
  empty, and the coordinate map is the zero map between zero modules.
- Over a field, q = 0 and `hres` is exactly the ordinary basis condition.
- For E = Z/6, P = E, r = 1, n = 5, both residue maps are invertible and
  the conclusion holds. With n = 2 the residue condition fails modulo 2,
  so a nonbasis is not admitted.
- The local-free hypothesis matters: P = Q/Z over Z has zero quotient
  P/pP for every maximal ideal but is nonzero. For r = 0 it fails `hfree`,
  so this example does not falsify the statement.

Searches actually run through `msearch.py` for this group and item:

- LeanFinder: “A prescribed finite family is a basis if it is a basis modulo
  every maximal ideal and all maximal localizations are free of the same rank”.
  Eight hits included `Module.nonempty_basis_of_flat_of_finrank_eq`,
  `Module.Basis.ofIsLocalizedModule`, and
  `Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective`; none states
  the global prescribed-family conclusion under exactly these hypotheses.
- Loogle: `Module.Basis, MaximalSpectrum`. One hit:
  `Module.nonempty_basis_of_flat_of_finrank_eq`. Its signature was read: it
  assumes a semilocal ring and global finite flatness and provides an
  unspecified basis, so it is not an exact match.
- Grep in Mathlib `RingTheory`: `basis.*(maximal|residue)|bijective.*maximal`.
  Twenty-five hits included the maximal-localization bijectivity criterion
  and the rank-at-stalk theorem in `Flat/LocallyFree.lean`. They do not
  already assert this residue-basis lifting result.
- LeanSearch: “Prescribed elements form a basis when their images are bases
  modulo every maximal ideal and the module is free of the same rank at all
  maximal localizations”. Eight hits included
  `Module.exists_basis_of_basis_baseChange`, whose full signature requires
  a local ring, finite presentation, and an extra tensor injectivity premise.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `basis.*(maximal|residue)|basisOfMaximal|basis_of_maximal` and the item id.
  `PrescribedResidueBasisSpreads` assumes finite presentation and spreads
  one prime's prescribed basis to an open; `BasisIffBasisQuotientOfNilpotent`
  assumes a flat module over a local ring with nilpotent maximal ideal;
  `SemilocalFiberGenerators` selects generators from dimension bounds.
  These modules were read and are not this assertion. No item-id match.
- The proposed declaration name was searched in both project source trees
  and `dag/lean_names_upstream.json`: no collision.

No new nodes, dependency modules, statement correction, or statement dispute
are needed. The earlier compact-object example's Sheaf module is withdrawn;
its node's current upstream module was read for the header and docstrings.

Validation: `scompile.py Q100 lem-a1-basis-of-maximal-residue-bases` compiled
the delivered file against the live published library, including its library
module form, with exit code 0 and no unexpected warnings. All variables and
universes are explicit, and `autoImplicit` is disabled. Delivery preflight is
run through the prescribed `deliver2.py` wrapper.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
