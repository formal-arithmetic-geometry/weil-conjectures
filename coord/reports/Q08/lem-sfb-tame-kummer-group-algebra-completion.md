## Worker report

Item: `lem-sfb-tame-kummer-group-algebra-completion`. The delivery changes only
its `lean` field and adds `Sheaf.RingTheory.TameKummerGroupAlgebraCompletion`.
The sole theorem is
`Algebra.TameKummer.finite_free_etale_and_complete_local_factors`, with proof `sorry`.
Its docstring carries all seven proof steps and their DAG references.

`Algebra.TameKummer.BaseChange` is an abbreviation for the tensor product already
specified in this item's statement. It installs the actual character-evaluation
and inclusion maps using Mathlib's universal group-ring maps. The two named
instances install Mathlib's tensor commutative-ring and coefficient-algebra
structures. These are real constructions, have no postponed proofs, and introduce
no independent mathematical notion or arbitrary comparison map. Their `letI`s
occur only inside construction bodies; the theorem signature contains no `let`.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Abelian groups L and M, finitely generated | `L : Type u`, `M : Type v`, `[AddCommGroup L]`, `[AddCommGroup M]`, `[AddGroup.FG L]`, `[AddGroup.FG M]` |
| Inclusion L into M | `i : L →+ M`, `_hi : Function.Injective i` |
| No torsion-free assumption | Neither group has any torsion-free or free-group binder |
| Finite cokernel | `[Finite (M ⧸ i.range)]` |
| Positive integer N annihilating that cokernel | `N : ℕ`, `_hN : 0 < N`, `_hkill : ∀ c : M ⧸ i.range, N • c = 0` |
| Commutative coefficient ring with N invertible | `E : Type w`, `[CommRing E]`, `_hunit : IsUnit (N : E)` |
| Group homomorphism to E units | `ρ : Multiplicative L →* Eˣ`; `Multiplicative` merely changes the notation for the additive group law |
| Integral group rings with the stated multiplication | `AddMonoidAlgebra ℤ L`, `AddMonoidAlgebra ℤ M`; their convolution multiplies `single l 1` and `single l' 1` to `single (l+l') 1` |
| The character scalar map | `(AddMonoidAlgebra.lift ℤ E L ((Units.coeHom E).comp ρ)).toRingHom.toAlgebra`, whose basis formula is exactly `[l] ↦ ρ(l)` |
| The inclusion scalar map | `(AddMonoidAlgebra.mapDomainRingHom ℤ i).toAlgebra`, whose basis formula sends `[l]` to `[i(l)]` |
| U is the displayed tensor product | `BaseChange i ρ` unfolds to `E ⊗[AddMonoidAlgebra ℤ L] AddMonoidAlgebra ℤ M` with precisely those two scalar structures |
| U commutative, pure tensors multiply as specified | `baseChangeCommRing` is Mathlib `Algebra.TensorProduct.instCommRing`; its `tmul_mul_tmul` gives the exact formula |
| U is an E-algebra | `baseChangeAlgebra` is the canonical left tensor algebra; `algebraMap E U` sends `a` to `a ⊗ 1` |
| Finite free of rank cardinality of M/L | `Nonempty (Module.Basis (M ⧸ i.range) E (BaseChange i ρ))`, with the finite quotient binder; a finite quotient-indexed basis states exactly finite freeness of the specified rank |
| E to U is etale | `Algebra.Etale E (BaseChange i ρ)`; the project explicitly permits the ring-algebra form of the etale morphism notion |
| Additional hypotheses only for the local conclusion | The third conjunct universally binds `Nontrivial E`, `IsNoetherianRing E`, `IsLocalRing E`, and `IsAdicComplete (IsLocalRing.maximalIdeal E) E` |
| Finitely many maximal ideals index the factors | `Finite (MaximalSpectrum (BaseChange i ρ))` and `A : MaximalSpectrum (BaseChange i ρ) → Type (max u v w)` |
| Product as E-algebras | `∃ e : BaseChange i ρ ≃ₐ[E] (∀ p, A p)` |
| Nonzero complete Noetherian local E-algebras | Existential `CommRing`, `Algebra E`, `Nontrivial`, and `IsLocalRing` structures on every `A p`; `IsNoetherianRing (A p)` and `IsAdicComplete (IsLocalRing.maximalIdeal (A p)) (A p)` |
| Index p is the corresponding maximal ideal | `(IsLocalRing.maximalIdeal (A p)).comap ((Pi.evalRingHom A p).comp e.toRingHom) = p.asIdeal`; thus the index is tied to its product projection |
| Each factor finite etale over E | `Module.Finite E (A p) ∧ Algebra.Etale E (A p)` |
| Canonical residue extension | The existential `IsLocalHom (algebraMap E (A p))` supplies Mathlib's induced residue-field algebra; this records the local structure already implicit in the finite E-algebra map between the stated local rings |
| Residue extensions finite and separable | `Module.Finite (IsLocalRing.ResidueField E) (IsLocalRing.ResidueField (A p))` and `Algebra.IsSeparable` for these same residue fields, with their canonical induced algebra |
| Local means unique maximal ideal; complete means canonical completion map is an isomorphism | Mathlib `IsLocalRing` and `IsAdicComplete`; `AdicCompletion.of_bijective_iff` identifies the latter with the exact canonical completion-map condition |

### Dependency declarations used

All statement dependencies were read from their node records and source signatures
and docstrings. No dependency record needs repair.

- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, in
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic` (exposed by tensor imports).
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`,
  `includeRight`, `ext` in `Mathlib.RingTheory.TensorProduct.Basic`, and
  `productMap`, `productMap_apply_tmul` in `.Maps`.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. The conclusion uses
  `Algebra.Etale` in `Mathlib.RingTheory.Etale.Basic`, the explicitly accepted
  ring-algebra formulation (brief-stage2, ETale RING MAPS convention).
  The affine bridge is `HasRingHomProperty @Etale RingHom.Etale`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-adic-completion`: `AdicCompletion`, `IsAdicComplete`,
  `AdicCompletion.of_bijective_iff`, `Mathlib.RingTheory.AdicCompletion.Basic`.
- `def-weil-pbc-free-module`: `Module.Free` and its basis formulation,
  `Mathlib.LinearAlgebra.FreeModule.Basic`; the actual signature states the
  more informative specified basis using the underlying `Module.Basis`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, `Mathlib.AlgebraicGeometry.ResidueField`.
  Here the node asks for local-ring residue fields, so the signature uses their
  underlying `IsLocalRing.ResidueField` and canonical induced algebra from
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`; the recorded scheme residue
  field is defined by this exact local-ring quotient construction.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`; it already implies algebraicity.

Proof-only imports preserve the accepted proof plan:
`Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`),
`Mathlib.RingTheory.Etale.StandardEtale` (`StandardEtalePair`),
`Mathlib.RingTheory.Ideal.GoingUp`,
`WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct`
(`Algebra.finite_over_complete_local_product`), and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen`
(`AlgebraicGeometry.Scheme.finite_product_principal_open`). The remaining proof
dependencies are exposed through the statement imports: etale permanence,
scheme coproducts, completeness, tensor universal property, and separability
of etale residue-field extensions.

### Edge cases and source reading

- The coefficient ring may be the zero ring in the first two conclusions.
  A quotient-indexed basis remains meaningful there; using finrank equality
  would wrongly fail to express the intended basis rank in this case.
- For `i` an isomorphism the quotient is trivial, so the basis has one index,
  the tensor product is E, and the complete-local decomposition has one factor.
- `N = 1` forces a trivial quotient and is allowed; `N = 0` is excluded by the
  node's explicit positivity. No characteristic assumption is added beyond
  invertibility of N.
- Torsion is allowed in L and M. In particular `L = 0`, `M = Z/2`, and
  `N = 2` over a ring with 2 invertible give the usual finite etale group ring.
- Positive characteristic is allowed whenever N is invertible. If the
  characteristic divides N the unit hypothesis correctly fails for nonzero E.
- The local conclusion explicitly assumes E nonzero. Nontrivial factors and
  the product isomorphism force a nonempty maximal-spectrum index set.
- The group universes `u,v` and coefficient universe `w` are independent.
  The tensor's carrier lies in `Type (max v w)`, since the scalar-ring universe
  does not raise the tensor carrier. Factor carriers may live in
  `Type (max u v w)`; this imposes no equality or bound on the input universes.

Read ILO VI 2.2, printed p.72 (PDF page 78): the invertible-exponent
Kummer chart and its etale diagonalizable group. Read the existing complete
local product theorem and its Stacks 0325 proof. The item's seven-step expansion
supplies the coset basis, cyclic adjunctions, derivative criterion, local product,
maximal-ideal indexing and residue-field finiteness/separability. No mathematical
fault or statement correction was found.

### Searches for reuse

All msearch calls used group Q08 and this item id on 2026-10-24.

- LeanSearch: "For a character of a finite index abelian subgroup, base change
  of the integral group ring is finite free etale when the quotient exponent is
  invertible, with complete local factors". Eight hits, including
  `Algebra.Etale.baseChange` and `RingHom.Etale.isStableUnderBaseChange`.
  They assume the starting etaleness and do not state this calculation.
- LeanFinder: "A character-twisted group algebra for a finite index inclusion of
  finitely generated abelian groups is finite free etale and decomposes into
  complete local rings". Eight hits; `Algebra.Etale.iff_exists_algEquiv_prod`
  requires a field coefficient ring and does not supply this theorem.
- Loogle: `"MonoidAlgebra", "Etale"`. Zero hits.
- msearch grep: `(MonoidAlgebra|AddMonoidAlgebra).*(Etale|complete)|(Etale|complete).*(MonoidAlgebra|AddMonoidAlgebra)`.
  Zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `tame.kummer|KummerGroup|kummerGroup|groupAlgebra|GroupAlgebra` found unrelated
  representation-theoretic and multiplicative-character constructions, not this
  base change theorem. Searching the item id in `lean/WeilConjectures` found none.
- Exact namespace/declaration-name search in `dag/lean_names_upstream.json`, both
  project roots, and Mathlib found no collision.
- DAG concept search found the retired per twin with no Lean record and this
  sfb node. There is no existing statement declaration to record.
- Read Mathlib's `AddMonoidAlgebra.lift` and `mapDomainRingHom`; the delivery uses
  these existing maps instead of reimplementing group rings or their universal
  properties.

### Validation

Compiled the delivered file with the prescribed `scompile.py Q08
lem-sfb-tame-kummer-group-algebra-completion <file>`. Both sandbox and library
module compile checks passed, with no errors and no warnings (2.2 and 2.0 seconds).
The initial compile diagnosed `Units.valHom` (fixed to `Units.coeHom`) and the
carrier universe (fixed to `max v w`); the subsequent compile is clean.

## Second reading by Q08

The assigned worker reread the original node and the final file clause by clause;
this is a self-check, not a claim of an independent second worker. The dispatcher
explicitly forbids starting another agent and assigns independent review to the
maintainer. The correspondence table above records this reading in full.

The rereading checked that `BaseChange` fixes both scalar maps, the basis index
is the actual cokernel `M/i.range`, the extra local hypotheses are confined to the
third conjunct, and the product projections contract the local maximal ideals
to their specified indices. It also checked that residue extensions use the
canonical local E-algebra map. No mismatch required a mathematical change;
only the compiler-level units-map name and result universe were corrected.
No new nodes or dependency modules, and no statement correction, are included.
