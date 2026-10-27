## Worker report

Item: `lem-sfb-length-two-witt-extension-verschiebung`. Module:
`Sheaf.AlgebraicGeometry.LengthTwoWittExtensionVerschiebung`, namespace
`AlgebraicGeometry.LengthTwoWitt`. No natural-language statement, dependencies, or other
node fields change: only the item's `lean` record is supplied. No new nodes or dependency
repairs are needed. Four theorems are deliberately `sorry`: `group_existsUnique`,
`extension`, `canonical_verschiebung`, and `additive_canonical_verschiebung`.
Each states clauses of this one node, has its blueprint identifier and a source-based
proof docstring. Every definition has actual data. The group instance is selected only
from a unique-existence theorem specifying all three group operations.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp. 226–227
(PDF pp. 238–239), Section 11(j), S₀, S₁, Proposition 11.43, Proposition 11.44,
and the paragraph describing canonical Verschiebung. The node correctly disambiguates
two coordinates from Milne's zero-based W₁ notation. No unit correction is needed.

Hypothesis and clause correspondence:

- The base is arbitrary `k : Type u` with `[Field k]`. The characteristic is
  `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]`. Prime implies p>0; no smoothness,
  connectedness, perfectness, or algebraic-closure assumption is made.
- The exact correction polynomial is `correction k p`, the negative sum over
  `Finset.Ico 1 p` of `C ((p.choose i / p : ℕ) : k) * X 0 ^ i * X 1 ^ (p-i)`.
  The division occurs in the integers/naturals BEFORE reduction to k, never in k.
  The prime divisibility makes this precisely reduction of the integral polynomial.
- The affine plane is `scheme k p = StandardGroupSchemes.affine k
  (MvPolynomial (Fin 2) k)`, definitionally Spec of the indicated two-variable ring.
  Its p parameter indexes the group law while its underlying scheme has two coordinates
  for every p. `isAffine` reuses the existing affine-spectrum instance, explicitly.
- `comul k p` substitutes the two tensor-polynomials
  `X₀⊗1+1⊗X₀` and `X₁⊗1+1⊗X₁+cₚ(X₀⊗1,1⊗X₀)`.
  By polynomial evaluation and tensor universal properties this IS the required law
  on every commutative k-algebra, including nonreduced algebras, not only field points.
  `correctionValue` permits algebras `R : Type v` in any universe v.
- `counit k` substitutes `(0,0)`; `antipode k p` substitutes
  `(-X₀,-X₁-cₚ(X₀,-X₀))`. `group_existsUnique` asserts that those exact maps,
  transported through the dependency's `multiplication`, `identitySection`, and `map`,
  specify a unique `GrpObj (scheme k p)`. `group` selects that determined structure.
- Commutativity is `IsCommMonObj (scheme k p)` in `extension`.
  Finite type is `LocallyOfFiniteType (scheme k p).hom ∧ QuasiCompact (scheme k p).hom`,
  exactly the recorded finite-type dependency's convention.
- The inclusion `inclusion k p` is the spectrum of `MvPolynomial.aeval ![0,Polynomial.X]`.
  The projection `truncation k p` is the spectrum of `Polynomial.aeval (MvPolynomial.X 0)`.
  Both use the existing `StandardGroupSchemes.map`. The two `IsMonHom` clauses explicitly
  assert that these particular substitutions are homomorphisms for the specified group laws.
- The closed embedding is `IsClosedImmersion (inclusion k p).left`.
  Scheme-theoretic exactness is the isomorphism
  `e : StandardGroupSchemes.additive k ≅ GrpObj.ker (truncation k p)` together with
  `e.hom ≫ GrpObj.kerι (truncation k p) = inclusion k p`.
  This preserves the actual kernel inclusion, rather than stating an abstract isomorphism.
  With the two homomorphism clauses, this also identifies the kernel group law.
- Faithful flatness is `Flat (truncation k p).left ∧ Surjective (truncation k p).left`.
  Finite presentation is all three of `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated` of that same projection, as the node's definition dependency specifies.
- Gₐ is the recorded `StandardGroupSchemes.additive k` with its recorded `additiveGroup`;
  no second additive-group definition is introduced. `additiveIsAffine` simply exposes
  its existing affine-spectrum instance through this interface.
- Canonical Witt Verschiebung is `canonical_verschiebung`. Its first conjunct fixes
  an algebra isomorphism `e : twist k p Γ(W₂,⊤) ≃ₐ[k] MvPolynomial (Fin 2) k`
  on EVERY `pure ... a c` by `C c * MvPolynomial.map (frobenius k p) (ΓSpecIso.hom a)`.
  This is exactly f⊗c ↦ c f^[p], with Frobenius on coefficients only, and fixes the
  canonical identification over an imperfect field as well. Its second conjunct
  computes the actual dependency term `projection ... (iteratedComul ... p a)`
  under e on EVERY global coordinate a. It equals `shiftCoordinates k` of that coordinate,
  where the explicit substitution is `![0,X₀]`. Contravariantly this states V(a,b)=(0,a),
  for the canonical map rather than an arbitrary map satisfying VF=[p].
- `additive_canonical_verschiebung` fixes the corresponding twist identification by
  `Polynomial.C c * Polynomial.map (frobenius k p) (ΓSpecIso.hom a)` and computes the
  same canonical projection/coproduct construction as `Polynomial.aeval (0 : Polynomial k)`.
  This is the coordinate map of the zero group homomorphism, not the zero ring map.
- `coordinateHopf` and `additiveCoordinateHopf` reuse
  `HopfAction.coordinateHopfAlgebra` with the actual specified group structure and
  Mathlib's `specOverSpec`; they expose no new Hopf structure choices. The explicit
  instances avoid nonterminating inference of an unbundled field from a bundled base.

Dependency interfaces read and used:

- Mathlib `Algebra.Field.Defs`: `Field`; `AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- Mathlib `Algebra.MvPolynomial.Basic` and `.Eval`: `MvPolynomial`, `aeval`, and the
  polynomial universal property. The actual signatures and docstrings were inspected.
- Mathlib `CategoryTheory.Monoidal.Grp` and `.Mon`: `GrpObj`, `IsMonHom`, `IsCommMonObj`;
  the `GrpObj.ker`/`kerι` convention was also read in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.ClosedImmersion`,
  `.Flat`, `.UnderlyingMap`, and `.FinitePresentation`: `LocallyOfFiniteType`,
  `QuasiCompact`, `IsClosedImmersion`, `Flat`, `Surjective`, `LocallyOfFinitePresentation`.
  Their full class signatures and docstrings were inspected, not guessed from names.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `multiplication`,
  `identitySection`, `additive`, `additiveGroup`, and its unique-existence specification.
- `Sheaf.AlgebraicGeometry.AffineGroupFrobeniusVerschiebung`: full module read, including
  `twist`, `pure`, `projection`, `iteratedComul`, `Maps`, `GroupMaps`, and the full
  `frobenius_verschiebung` theorem. Those latter specifications identify the particular
  projection/coproduct term used here with the canonical coordinate Verschiebung.
- `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`: `HopfAction.coordinateHopfAlgebra`,
  read and reused through the recorded Frobenius/Verschiebung dependency's imports.
  Mathlib `AlgebraicGeometry.Group.Affine`: `specOverSpec`, the global-coordinate Hopf
  instance and `isAffine_Spec`; `Scheme.ΓSpecIso` is the existing canonical coordinate iso.
- Available proof dependencies are imported as proof imports: tensor product maps,
  Hopf-spectrum functor, affine spectra and affine fibre products, affine morphisms and
  their permanence properties. No proof-dependent declarations are redefined here.

Searches run using the prescribed `msearch.py`, group Q54/item key:

- LeanFinder: “The affine plane with length two Witt addition is an extension of the
  additive group by itself and its canonical Verschiebung is (a,b) to (0,a)”: eight hits,
  chiefly `WittVector.verschiebung`, `wittAdd`, and infinite-vector polynomial APIs;
  no scheme extension or canonical group-scheme comparison.
- Loogle: `"TruncatedWittVector", "verschiebung"`: zero hits.
- Mathlib grep: `verschiebung|add_coeff_one` in `RingTheory/WittVector`: 25 displayed hits,
  giving infinite Witt-vector operations, not this scheme-level theorem.
- LeanSearch: “The two coordinate Witt group scheme is an extension of the additive
  group by itself with canonical Verschiebung given by shifting coordinates”: eight
  infinite Witt-vector shift/coordinate results, no matching scheme theorem.
- `rg` of `Witt|witt|verschiebung|Verschiebung` in project `lean/Sheaf/AlgebraicGeometry`
  and `lean/WeilConjectures/AlgebraicGeometry`: the recorded canonical-construction
  dependency and unrelated Hall–Witt Lie results, no two-coordinate extension.
- Search for this node ID in `lean/WeilConjectures`: no hits. Search for the proposed
  `LengthTwoWitt|lengthTwoWitt` namespace in Mathlib, both project libraries, and
  `dag/lean_names_upstream.json`: no hits. Thus no existing declaration was duplicated.

Edge cases read against source and formulas before finalizing:

- p=2: the correction is -XY=XY in characteristic two; the stated antipode and shift
  are still correct. No odd-characteristic argument or restriction is introduced.
- Imperfect k (e.g. Fₚ(t)): twist identification uses coefficient Frobenius in the forward
  direction and generators in the inverse; it never takes a p-th root of a scalar.
- Nonreduced test algebras: all maps are polynomial substitutions and equalities on
  whole coordinate rings, so rational-point detection is not substituted for scheme equality.
- The zero ring is allowed as a test k-algebra; all displayed substitutions remain valid.
  The base itself is a field and consequently nontrivial, exactly as the node assumes.
- No assertion that the section a↦(a,0) is a group homomorphism is made.
- The additive zero Verschiebung is evaluation at zero on coordinates; it preserves 1.
- Arbitrary universe u for the base and v for evaluation covers all sizes without
  forcing unrelated universe equalities. Auto-implicit variables are disabled.

Validation: the substantive module compiled through `scompile.py` on the live server
with no errors or warnings. Only the final import bookkeeping was subsequently expanded;
the delivery dry run recompiles that final file. No local/global build or live-tree edit
was performed. There are no statement disputes or source corrections.

## Second reading by Q54

Author's fresh clause-by-clause reading, with the source node and final module open;
the maintainer supplies the independent review, as the dispatcher brief requires.
I checked that the binomial quotient occurs before reduction, the finite sum excludes
both endpoints, the sign agrees with S₁, and the specified zero, product and inverse
fix every data field of the chosen group. I matched the closed immersion, compatible
kernel isomorphism, both homomorphisms, flatness, surjectivity, and all THREE finite
presentation conditions with the node. The two-coordinate index remains two also at p=2.
For the last clause, I reopened the dependency's `Maps` specification: its canonical
coordinate map is precisely `projection (iteratedComul ...)`, so the final two theorems
identify the canonical map on full coordinate rings. Their twist identifications specify
all pure tensors and raise coefficients rather than variable exponents; this retains
imperfect fields. Gₐ's zero map is unital evaluation, not an impossible zero ring homomorphism.
The final reading found that unused section instances would otherwise be omitted from
`group_existsUnique`; I added explicit `include hp hk in` so its hypotheses retain prime
characteristic exactly. No other semantic mismatch was found. Compilation prompted explicit exposure of the existing
Hopf/scalar interfaces and an explicit polynomial tensor type; these repairs change
no mathematical hypotheses or conclusions. All four postponed statements are exactly
subclauses of this item's statement and their docstrings retain the seven-step proof.
