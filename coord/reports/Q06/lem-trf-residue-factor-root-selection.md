## Worker report

The module `Sheaf.FieldTheory.ResidueFactorRootSelection` states
`Polynomial.exists_residue_factor_root_selection`, with `sorry` as its entire proof.
It introduces no definition and changes only the item's `lean` record.

The source is the final residue-field paragraph of Stacks Project, Algebra, Tag 00UF,
label `lemma-standard-etale-finite-flat-Zariski`, read in
`literature/stacks-project/algebra.tex`. It selects a root of the irreducible residue
factor at which the localization polynomial is nonzero. The declaration docstring
carries all five steps of the node's expanded proof, with their dependency ids.

Clause-by-clause correspondence:

- The field `k` is `{k : Type u} [Field k]`.
- The two polynomials in `k[t]` are `(f g : k[X])`.
- Leading coefficient one is `(hf : f.Monic)`: Mathlib defines `Monic` as
  `leadingCoeff f = 1`.
- The extension field is `{L : Type v} [Field L] [Algebra k L]`, and its given
  coefficient homomorphism is `algebraMap k L`. The dependency explicitly permits
  this equivalent algebra encoding of a field extension. Any specified unital ring
  homomorphism gives this encoding by `RingHom.toAlgebra`.
- The finite indexed family is `{I : Type w} [Fintype I] (α : I → L)`. There is
  no `Nonempty I` assumption; a `Fintype` structure is an enumeration of any finite
  set, and the conclusion does not depend on the enumeration.
- The prescribed coefficient-image factorization is
  `(hfactor : f.map (algebraMap k L) = ∏ i : I, (X - C (α i)))`.
  The product includes multiplicities and becomes one for an empty index type.
- The irreducible factor is `(f₁ : k[X]) (hirr : Irreducible f₁)`.
  Mathlib's `Irreducible` says nonunit and that every factorization has a unit
  factor. In the nontrivial polynomial ring over a field it also excludes zero:
  the factorization `0 = 0 * 0` would force zero to be a unit. Thus it gives
  exactly the node's nonzero, nonunit, and unit-factor requirements.
- Divisibility of `f` is `(hdiv : f₁ ∣ f)`.
- Failure to divide `g` is `(havoid : ¬ f₁ ∣ g)`.
- The chosen index is `∃ i : I`. Both required conclusions use this same index.
- Vanishing of the factor is `f₁.eval₂ (algebraMap k L) (α i) = 0`.
- Nonvanishing of the localization polynomial is
  `g.eval₂ (algebraMap k L) (α i) ≠ 0`, joined to the previous clause by `∧`.
  In each clause `eval₂` evaluates with exactly the given coefficient map.

Statement dependencies, with the declarations and their source modules read:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  `Polynomial.Monic` and `Polynomial.leadingCoeff`,
  `Mathlib.Algebra.Polynomial.Degree.Defs`. Basic is publicly imported by Eval.Defs.
- `def-pc-field-extension`: `Algebra` and `algebraMap`,
  `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-polynomial-root`: `Polynomial.eval₂`,
  `Mathlib.Algebra.Polynomial.Eval.Defs`.

The statement uses the existing `Irreducible` definition from
`Mathlib.Algebra.Group.Irreducible.Defs`; it does not define a private replacement.
The coefficient image is the existing `Polynomial.map` from Eval.Defs.
The additional imports are the plan's already stated proof dependencies:
`Mathlib.Algebra.Polynomial.FieldDivision` provides
`Polynomial.instEuclideanDomain`; `Mathlib.RingTheory.PrincipalIdealDomain` provides
`EuclideanDomain.to_principal_ideal_domain` (`lem-pur-polynomial-field-pid`);
`Mathlib.Algebra.Polynomial.Eval.Coeff` provides `Polynomial.map_injective`
(`lem-weil-coefficientwise-extension-injective`), whose ring-homomorphism and
finite-product clauses use `Polynomial.mapRingHom` and `Polynomial.map_prod`
in Eval.Defs; `Mathlib.Algebra.Polynomial.Splits` provides
`Polynomial.Splits.of_dvd` (`lem-trf-divisor-of-split-polynomial`). These proof-only
imports are not public. No dependency interface needs repair.

Edge cases checked before writing:

- Empty `I`: the product is one; injectivity of coefficient extension forces
  `f = 1`. A nonunit irreducible cannot divide one, so the premises are impossible.
  The theorem still includes this case, with no nonemptiness binder.
- `f = 0` is excluded precisely by monicity over a field, not by an added hypothesis.
  A constant monic `f` is one and again cannot have the asserted irreducible divisor.
- `f₁ = 0` and nonzero constant `f₁` are excluded by irreducibility as explained above.
- `g = 0` is excluded by `havoid`, because every polynomial divides zero.
  Nonzero constant `g` is permitted and evaluates to a nonzero field element.
- Repeated roots, inseparable factors, arbitrary characteristic, and arbitrary field
  extensions are allowed. No separability, algebraic-closure, finite-extension,
  or characteristic hypothesis is present.
- The universes of `k`, `L`, and the finite indexing type are explicitly and
  independently bound; no size restriction is added.

Searches for an existing full statement (all run through `msearch.py` with this group
and item, supplemented by source `rg`):

- LeanFinder query: "An irreducible divisor of a polynomial split into a specified
  finite product of linear factors over a field extension has a root in that list
  where a polynomial it does not divide is nonzero". Eight hits included
  `Polynomial.Splits.dvd_of_roots_le_roots`,
  `Polynomial.Splits.dvd_iff_roots_le_roots`,
  `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd`, and
  `AdjoinRoot.mul_div_root_cancel`. None selects an index in the prescribed family
  and proves both evaluation clauses.
- Loogle query: `Polynomial.Splits, Irreducible`. Seven hits concerned degree-one
  irreducibles, splitting-field degree, algebraic closure, and the Galois action;
  none states this result.
- LeanSearch query: "An irreducible factor of a polynomial split over a field
  extension has a root where a polynomial not divisible by it is nonzero".
  Eight hits included `Polynomial.rootOfSplits'`, `Polynomial.exists_root_of_splits'`,
  `Polynomial.factor`, and splitting-field constructions. These supply portions
  of the argument, not the full prescribed-index and avoidance statement.
- Mathlib grep query: `exists_eval_eq_zero|of_dvd|eval.*ne_zero`, restricted to
  `Algebra/Polynomial`. Twenty-five returned hits included
  `Polynomial.Splits.exists_eval_eq_zero` and results about divisibility, roots,
  and coprime evaluation. None states the complete item.
- Source-tree and side-library `rg` queries:
  `lem-trf-residue-factor-root-selection|residue.*factor.*root|root.*selection`
  and `residue_factor_root_selection`, plus
  `residueFactorRoot|exists.*eval₂.*ne|irreducible.*root|root.*irreducible`.
  No full statement or declaration-name collision was found. The existing
  `StandardEtaleFiniteFreePrimeLifts` docstring mentions root selection as a proof
  step, without providing this declaration. Other matches concern different
  irreducible-root results. The name was also checked in `dag/lean_names_upstream.json`.

No statement correction, new node, disputed statement, or dependency fault was found.
Compilation and the delivery dry run are performed using only the authorized wrappers.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
