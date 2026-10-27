## Worker report

The module `Sheaf.RingTheory.FiniteEtaleCohenExtension` states
`IsCohenRing.exists_finiteEtale_extension`, with one whole `sorry` proof and no
new definitions. The item node changes only in `lean`.

Hypothesis-by-hypothesis correspondence:

- The prime `p` and Cohen ring `D` are `(p : ℕ) (D : Type u) [CommRing D]
  (hD : IsCohenRing p D)`. The recorded upstream definition includes `Nat.Prime p`,
  the domain/DVR structures, maximal ideal `pD`, and adic completeness. No extra
  primality, localness, or completeness hypothesis is imposed.
- The named residue field `F = D/pD` is represented by `(F : Type v) [Field F]`
  and `eF : (D ⧸ Ideal.span {(p : D)}) ≃+* F`. This is an explicit identification
  of the named field with that quotient, not a second residue-field construction.
  An arbitrary model of the quotient is permitted. In particular `eF` can be
  the identity when F is the quotient with its induced field structure.
- The specified extension `L/F` is `(L : Type (max u v w)) [Field L]
  [Algebra F L]`. Its specified inclusion is `algebraMap F L`.
- Finite-dimensionality is `[Module.Finite F L]`, rather than finite type as an
  algebra. Separability is the recorded `[Algebra.IsSeparable F L]`, which also
  entails algebraicity. No normality or Galois hypothesis is imposed.

Conclusion-by-conclusion correspondence:

- `∃ B : CommAlgCat.{max u v w} D` supplies a commutative ring and its actual
  D-algebra structure. Thus the map `i` is exactly `algebraMap D B`.
- `IsCohenRing p B` says B is a Cohen ring with the same prime uniformizer.
- `Function.Injective (algebraMap D B)` is the required injection.
- `IsLocalHom (algebraMap D B)` is localness; Mathlib defines this by reflection
  of units, equivalent to inverse image of maximal ideals for these local rings.
- `Module.Finite D B ∧ Algebra.Etale D B` is finite étale in exactly the node's
  meaning. The ring formulation of étaleness is equivalent to the spectrum
  formulation through the recorded `AlgebraicGeometry.Etale` ring-hom-property
  instance and `RingHom.etale_algebraMap`; the project explicitly permits either
  ring or scheme formulation. This also avoids equating the universes of D and B.
- `∃ e : (B ⧸ Ideal.span {(p : B)}) ≃+* L` is the requested residue isomorphism.
- `∀ d : D, e (Ideal.Quotient.mk _ (algebraMap D B d)) =
  algebraMap F L (eF (Ideal.Quotient.mk _ d))` says the residue map agrees with
  the specified inclusion, including its dependence on the chosen identification.
- `∃ ρ : (B ≃ₐ[D] B) ≃* (L ≃ₐ[F] L)` gives a bijection of the indicated groups
  of base-fixing ring automorphisms. Its value is fixed by the final equation
  `ρ α (e (Ideal.Quotient.mk _ b)) = e (Ideal.Quotient.mk _ (α b))` for every
  α and every b. Since quotient reduction and e are surjective, this equation
  determines every value of ρ. It is precisely residue reduction conjugated by e,
  rather than an unspecified identification of automorphism groups. The group
  compatibility is part of the reduction assertion (also explicit in proof Step 5).

Dependency declarations read and used:

- `WeilConjectures.RingTheory.CohenRing`, `IsCohenRing` (full definition read).
- `Mathlib.FieldTheory.Separable`, `Algebra.IsSeparable` (signature and docstring read).
- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `Spec.map`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale` and its
  `HasRingHomProperty @Etale RingHom.Etale` instance. These recorded statement
  dependencies are public imports; their ring-algebra formulation is used above.
- `Mathlib.Algebra.Category.CommAlgCat.Basic`, `CommAlgCat` bundles the existential
  ring and algebra structure without any choice or placeholder data.

The proof-only imports follow the existing proof dependencies:
`Mathlib.RingTheory.Henselian` (`IsAdicComplete.henselianRing`),
`WeilConjectures.Mathlib.RingTheory.Henselian` (recorded henselian terminology),
`Sheaf.RingTheory.HenselianFiniteEtaleFieldLift`
(`CommAlgCat.FiniteEtale.exists_finiteEtale_residueField_equiv_of_finite_separable`),
`Mathlib.RingTheory.Smooth.Flat` (`Algebra.Smooth.flat`),
`Mathlib.RingTheory.LocalRing.Module` (`Module.free_of_flat_of_isLocalRing`),
`Mathlib.RingTheory.PrincipalIdealDomain` and
`Mathlib.RingTheory.Polynomial.RationalRoot` (the PID Noetherian/normal instances),
`WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct`
(`Algebra.finite_over_complete_local_product`), and
`Sheaf.RingTheory.HenselianFiniteEtaleMapBijective`
(`CommAlgCat.FiniteEtale.bijective_baseChange_residueField_map_of_henselianLocalRing`).
The full signatures/docstrings of the recorded project declarations were read.
The proof dependency `lem-sfb-finite-free-field-fibre-dvr` has no recorded Lean
module or Mathlib match at the time of writing; it is consequently mentioned in
proof Step 3, with no invented import. It is not needed to type this statement.

Source checked locally: `literature/stacks-project/algebra.tex`,
`lemma-henselian-cat-finite-etale` (Tag 04GK), including the full-faithfulness and
essential-surjectivity paragraphs, and `definition-cohen-ring` (Tag 0327).
The five proof steps in the docstring reproduce the node's complete proof route.

Edge cases checked before writing:

- Degree one L/F is allowed; take B=D, with the given residue identification.
- Non-normal finite separable extensions are included; both automorphism groups
  can be trivial, and the statement does not assert that their order is [L:F].
- All primes, including p=2, are covered. Primality follows from hD.
- Zero rings and fields as D or B are excluded by the actual Cohen-ring definition,
  not by a new assumption. L is nonzero because it is a field, so the lift has
  positive rank, as used in the node's proof.
- Imperfect residue fields are allowed. No perfectness is used in the statement.
- D and F have independent universes u and v; L and B use max u v w, with an
  additional arbitrary w. There is no lower-universe quantification over test
  objects and no imposed equality of the ring universes.
- The automorphism equation quantifies over all b, so it cannot accidentally
  assert an arbitrary group equivalence or forget the specified reduction map.

Searches (2026-10-24), all through the prescribed msearch wrapper or direct rg:

- LeanFinder: "A Cohen ring admits a finite etale Cohen extension with prescribed
  finite separable residue field and a bijection of automorphism groups".
  Eight hits: `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`,
  field classification of formally étale and étale algebras,
  `Algebra.Etale.exists_subalgebra_fg`, `StandardEtalePresentation`,
  `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`,
  `StandardEtalePair.instEtaleRing`, and formal étaleness of separable extensions.
  None states the Cohen extension with the specified reduction on automorphisms.
- LeanSearch: "A finite separable extension of a Cohen ring residue field lifts to
  a finite etale Cohen extension with automorphisms lifting uniquely".
  Eight hits involving `IsSepClosed.lift`, formally étale separable fields,
  field classification, and `StandardEtalePresentation.lift_bijective`.
  None has this statement over a Cohen ring.
- Loogle: `"IsCohenRing", "Etale"`: zero hits.
- Mathlib grep via msearch: `Cohen.*[Ee]tale|[Ee]tale.*Cohen|cohen.*[Ee]tale`:
  zero hits.
- Direct rg with the same expression in `lean/WeilConjectures` and `lean/Sheaf`:
  no hits. Direct grep for the item id in `lean/WeilConjectures`: no hits.
- Further rg for the item id and `finite_etale_cohen` in `dag/lean_names_upstream.json`
  and both Lean source roots found no matching declaration. Broader Cohen-extension
  hits concern power-series parameter extensions and Cohen–Macaulay field extension,
  not this theorem.

Validation: `scompile.py Q64 lem-per-finite-etale-cohen-extension` on the module
passed both sandbox and library-mode checks, with no errors or unexpected warnings.
No statement dispute, statement correction, new node, or dependency repair is needed.

## Second reading by Q64

This is a separate self-review pass by the sole dispatched worker; no independent
worker was started, in accordance with the dispatcher's instruction. Independent
review belongs to the maintainer's review of this delivery.

Reopened the node and the final module and checked every clause: hD includes the
prime; eF identifies the precise quotient D/pD; Module.Finite and IsSeparable
express exactly the finite separable extension; the witness B includes its actual
D-algebra map; the Cohen, injectivity, localness, finiteness, and étaleness clauses
are all present; the equation on d specifies the residue inclusion; the equation
on α and b specifies reduction transported by e. In particular, the automorphism
clause is not merely Nonempty of an unrelated equivalence. No `let`, auto-bound
variable, private definition, arbitrary witness choice, or extra Galois/perfectness
hypothesis appears. No mismatch was found and no change was necessary.
