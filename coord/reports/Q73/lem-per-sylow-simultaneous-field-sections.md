## Worker report

The module `Sheaf.FieldTheory.SylowSimultaneousFieldSections` states
`FieldTheory.exists_primeTo_extension_simultaneous_field_sections`, with one `sorry` and no
new definitions. The node is unchanged except for its `lean` record. No statement correction,
missing notion or unusable dependency was found.

The source was read directly from the local ILO PDF, physical pages 35--36 (printed 29--30):
the compositum's quasi-Galois closure, Sylow fixed field, the characteristic-dependent degree,
and the descent on each irreducible component using II 2.2.6. This matches the ten proof steps
of the node, all included verbatim, wrapped to the line limit, in the declaration docstring.

Every hypothesis and conclusion is represented as follows:

| Node clause | Lean rendering |
| --- | --- |
| K is a field | `(K : Type u) [Field K]` |
| ell is a prime | `(ell : ℕ) (hell : ell.Prime)` |
| ell differs from the characteristic of K | `(hchar : ell ≠ ringChar K)` |
| I is a finite set, possibly empty | `(I : Type t) [Finite I]`; no Nonempty hypothesis |
| Each K_i is a field extension of K | `(Ki : I → Type v)`, dependent Field and Algebra K instances |
| Each K_i/K is finite | `[∀ i : I, FiniteDimensional K (Ki i)]` |
| Each K_i/K is separable | `[∀ i : I, Algebra.IsSeparable K (Ki i)]` |
| Each F_i is a field extension of K_i | `(Fi : I → Type w)`, dependent Field and Algebra (Ki i) instances |
| Each F_i/K_i is finite | `[∀ i : I, FiniteDimensional (Ki i) (Fi i)]` |
| Its degree is prime to ell | `hdegree : ∀ i, Nat.Coprime (Module.finrank (Ki i) (Fi i)) ell` |
| One extension K'/K works simultaneously | The existential K', Field and Algebra K binders precede the universal i and m |
| K'/K is finite | `FiniteDimensional K K'` |
| Its degree is prime to ell | `Nat.Coprime (Module.finrank K K') ell` |
| Every i and every field factor | `∀ (i : I) (m : Ideal (Ki i ⊗[K] K')), m.IsMaximal → ...` |
| Factor means quotient by a maximal ideal | The codomain is literally `(Ki i ⊗[K] K') ⧸ m` |
| The factor retains its canonical K_i map | Tensor-product leftAlgebra followed by Ideal.Quotient.algebra sends a to the class of a tensor 1 |
| The factor retains its canonical K' map | `Algebra.TensorProduct.includeRight` composed with `Ideal.Quotient.mk m`; no map is chosen or varied |
| Tensor multiplication is ac tensor bd | Mathlib Algebra.TensorProduct.instCommRing and tmul_mul_tmul, not the bare module tensor alone |
| A K_i-algebra homomorphism F_i to that factor | `Nonempty (Fi i →ₐ[Ki i] ((Ki i ⊗[K] K') ⧸ m))` |
| Degrees are vector-space dimensions | `Module.finrank` everywhere, with explicit finiteness hypotheses |
| F_i/K_i need not be separable | No IsSeparable instance is requested for this extension |

The phrase finite etale describes the tensor algebra resulting from finite separable K_i/K;
it is not an extra input or an additional conclusion of the node. The tensor has precisely
that commutative algebra structure. Maximal-ideal quotients are fields by Mathlib, although the
AlgHom type itself only needs their canonical commutative ring and K_i-algebra structures.
`Nonempty` says that a map exists, without choosing it or adding an extra property.

Universes u, v, w and t are explicit and independent. The witness K' is in Type (max u v w),
which can contain the finite normal closure of a finite compositum of the input fields.
There is no restriction on the universe of the finite index type. Quotients automatically
live in the universe of the tensor algebra. No auto-bound variables or local instances occur.

Statement dependencies used, with their actual recorded declarations and imports:

- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs. Read the class docstring
  and fields: the field extension map is the central ring homomorphism algebraMap.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`, Mathlib.FieldTheory.Separable.
  Read its docstring and signature; algebraicity is built into separability of minpolys.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, Mathlib.LinearAlgebra.TensorProduct.Defs.
  Read the quotient construction and the bilinearity relations, plus lift, ext', rTensor,
  and rTensorHom in Basic/Map. The same tensor type carries Mathlib's algebra multiplication.
- `def-weil-vector-space-dimension`: `Module.finrank`, Mathlib.LinearAlgebra.Dimension.Finrank.
  Read its complete signature and docstring describing finite-dimensional vector-space dimension.

The statement additionally uses Mathlib.RingTheory.TensorProduct.Basic and
Mathlib.RingTheory.Ideal.Quotient.Operations for canonical algebra and quotient structures.
All already stated proof dependencies are imported without `public`. They include the
Mathlib modules recorded for degree multiplicativity, algebraic closure and embeddings,
finite-dimensional domains, normal closure, embedding counts, Sylow subgroups, fixed-field
degrees, inseparable degrees, algebra tensor maps, scalar extension dimensions, length and
simple modules. The two project imports are
`WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable`
(`Normal.fixedField_purelyInseparable`) and `WeilConjectures.RingTheory.SimpleFiltration`
(`Module.exists_simple_filtration_of_length_lt_top`). Their current source and full docstrings
were read using `scompile.py --source`, since they are absent from the older local checkout.
No proof import was omitted for a cycle.

Edge cases checked mathematically before writing:

- Empty I: choose K itself, lifted to the witness universe; degree 1 is coprime to ell and
  the remaining quantifiers are empty.
- Trivial K_i/K or F_i/K_i: the stated quotients and algebra maps retain their usual meanings;
  the identity extension of degree 1 is allowed.
- Characteristic zero: ringChar K = 0, so every prime ell satisfies the characteristic condition.
- Positive characteristic p with ell different from p: purely inseparable degree p^r is allowed
  in F_i/K_i and in K'/K. No Galois or separability condition is silently imposed on either.
- Example K = F_p(t), K_i = K and F_i = K(t^(1/p)), ell different from p: a purely inseparable
  K' of degree p supplies the desired map; a separable-only existential would have been wrong.
- Multiple factors: e.g. a split quadratic tensor algebra has two maximal ideals. Both are
  quantified, including the actual different K_i structural maps, rather than one chosen embedding.
- Zero tensor algebra / zero quotient are not extra cases here: the tensor of field extensions
  is nonzero, and maximal ideals are proper. The statement never assumes the tensor is a domain.

Searches made using the required wrapper (all successful):

- LeanFinder: `simultaneous prime to ell field sections Sylow fixed field`, eight hits, including
  fixedByFinite, IsGaloisGroup.fixedPoints and fixingSubgroup_fixedField; no simultaneous assertion.
  An earlier longer plain-language query likewise returned only general field-theory inputs.
- Loogle: `IntermediateField.fixedField, Module.finrank`, two hits: IsGalois.tfae and
  IntermediateField.finrank_fixedField_eq_card. Neither is the simultaneous theorem.
- LeanSearch: `simultaneous field extensions prime to ell Sylow fixed field sections`, eight hits
  on fixed fields and Galois subgroups, none giving the field-factor assertion.
- Mathlib grep: `sylow|primeTo.*degree|fieldSections|exists.*section` in FieldTheory, zero hits.
- Direct rg in WeilConjectures and lean/Sheaf: simultaneous, Sylow, primeTo degree, fieldSections,
  followed by focused FieldTheory field-section and prime-to searches. Hits concern unrelated
  roots, differential field models, Galois covers and scheme constructions, not this statement.
- Required upstream grep for `lem-per-sylow-simultaneous-field-sections`: zero hits.
- Exact proposed-name search in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  zero hits for sylow_simultaneous_field_sections or sylowSimultaneousFieldSections; the module
  uses the fresh name `FieldTheory.exists_primeTo_extension_simultaneous_field_sections`.

Validation: `scompile.py Q73 lem-per-sylow-simultaneous-field-sections <module>` compiled both
its sandbox and library forms cleanly, in 2.1 s and 2.2 s respectively, without warnings.
All source lines are at most 100 characters. There are no new or repaired dependency nodes.
No STATEMENT-DISPUTED or other node fault.

## Second reading by Q73

The dispatch expressly forbids starting another agent, so this is a separate second reading
by the same worker; the maintainer's independent review remains required. I reopened the final
node statement and final Lean signature after compilation and checked the table above against
both. In particular the existential is outside both universal quantifiers, finite extensions
are explicit on both input levels and on the witness, and maximal ideals rather than arbitrary
prime quotients specify the factors. The AlgHom codomain uses the canonical left algebra
structure and not a newly supplied K_i structure. No separability of F_i/K_i, nonempty I,
normality of K'/K or perfection of K is assumed. All four statement dependency interfaces are
used directly. The proof docstring contains every step and its uses. No mismatch was found,
and no change to the mathematical node was needed.
