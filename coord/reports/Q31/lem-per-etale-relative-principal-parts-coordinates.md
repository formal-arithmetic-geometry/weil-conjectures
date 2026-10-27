## Worker report

The module `Sheaf.RingTheory.EtalePrincipalPartsCoordinates` states the complete
node as `DiagonalJets.etale_relative_principalParts_coordinates`, with one `sorry`.
All seven supporting abbreviations/definitions have actual data and belong to the
canonical quotient and Taylor constructions of this item. No other node is changed,
no new independent notion is introduced, and there is no statement correction.

The source is Stacks Project, Algebra, Tags 0H93 (the full diagonal-power quotient
isomorphism), 0H90 (principal parts as the diagonal quotient, first-factor action),
and 0H8Z (arbitrary base change). I read the full local statements and proofs in
`literature/stacks-project/algebra.tex`, and checked those three official tag pages.
The module docstring and theorem docstring give the node's ten proof steps, including
the coefficientwise translation calculation and nilpotent uniqueness argument.

Hypothesis and clause correspondence, in theorem order:

1. `R₀ : Type u`, `R : Type v`, `[CommRing R₀]`, `[CommRing R]`, `[Algebra R₀ R]`
   represent the arbitrary base and coordinate algebra. `n : ℕ` is unrestricted.
   `φ : MvPolynomial (Fin n) R₀ →ₐ[R₀] R` represents the given polynomial ring map.
   An arbitrary ring map from that polynomial ring induces exactly this base
   algebra structure, so the algebra-hom spelling imposes no extra condition.
   `hφ : φ.toRingHom.Etale` is equivalent to the node's étale affine-spectrum
   hypothesis, by `HasRingHomProperty.Spec_iff` and the recorded étale instance.
2. `principalParts R₀ R t` is precisely the dependency's quotient by the
   `(t+1)`st power of the multiplication kernel. Its first-factor `R`-algebra
   structure is the existing tensor-product and ideal-quotient instance.
   `coordinateRing R n t` is the literal quotient
   `MvPolynomial (Fin n) R ⧸ MvPolynomial.idealOfVars (Fin n) R ^ (t+1)`.
   The variable ideal is Mathlib's existing definition, not a private replacement.
3. `∃ e : ∀ t : ℕ, coordinateRing R n t ≃ₐ[R] principalParts R₀ R t` is the
   displayed family of `R`-algebra equivalences. Its first conjunct fixes the
   value at every variable to the class of `1 ⊗ z_j - z_j ⊗ 1`. This uniquely
   determines each equivalence: it already preserves coefficients, polynomial
   algebra maps are determined by variables, and the quotient map is surjective.
   No arbitrary isomorphism or choice of an unspecified map replaces canonicity.
4. `rightJet` is the composite of `Algebra.TensorProduct.includeRight` and the
   actual quotient map as an `R₀`-algebra homomorphism. `coordinateTaylor` is
   `e.symm` composed with that exact map, restricted to `R₀` scalars. Thus it
   is exactly `h ↦ 1 ⊗ h` under the inverse equivalence. The second conjunct
   says `T_t(z_j) = z_j + Y_j`. The third says `constantCoeff p = h` for EVERY
   polynomial representative `p` of `T_t(h)`: this is precisely reduction
   modulo `(Y)`, and is independent of the chosen representative.
5. The fourth conjunct commutes `e` with the two actual truncation maps for
   every `s ≤ t` and every quotient element. Both truncation helpers are
   `Ideal.Quotient.factor` for the canonical inclusion of ideal powers.
   The fifth conjunct states the induced truncation compatibility for `T`.
6. The sixth conjunct is the coordinate monomial basis mentioned in the node's
   base-change clause and proof. It gives a `Module.Basis` indexed by all
   finitely supported `β : Fin n →₀ ℕ` with total degree at most `t`, and pins
   every basis vector to `e t` applied to the actual monomial class. This is
   exactly the displayed coordinate basis, including the zero-ring case.
7. The seventh conjunct quantifies over every commutative `R₀`-algebra `R₀'`,
   with no flatness condition. I use `R₀' ⊗[R₀] R` for `R'`, the canonical
   tensor commutation of `R ⊗[R₀] R₀'`, so the usual left `R₀'`-algebra
   instance is available without installing a different tensor-product action.
   Likewise base change of principal parts is `R₀' ⊗[R₀] P`, as in the recorded
   `def-weil-module-base-change` interface. There is a primed coordinate family
   `e'` with its explicit coordinate-difference formula, and an `R₀'`-algebra
   equivalence `θ` on the actual base-changed principal-parts rings. Its formula
   `a ⊗ [r ⊗ h] ↦ [(a ⊗ r) ⊗ (1 ⊗ h)]` fixes the canonical base-change map
   on additive generators and hence uniquely specifies it. The next formula
   for every polynomial `p` states coefficient and coordinate-monomial basis
   compatibility. The last formula, for every representative of `T_t(h)`,
   identifies the Taylor map on every `a ⊗ h`; these pure tensors additively
   generate `R'`, so this is exactly the base-changed Taylor-map equality.
8. The last conjunct quantifies over an arbitrary commutative `R₀`-algebra `C`
   and `τ : R →ₐ[R₀] MvPowerSeries (Fin n) C`, with only the required condition
   `τ(z_j) = MvPowerSeries.X j`. For all `t,h`, every representative `p` of
   `T_t(h)`, every series exponent `α` and every polynomial exponent `β` of
   total degree at most `t`, it asserts
   `coeff α (τ (coeff β p)) = (∏ j, Nat.choose (α j + β j) (β j)) •
   coeff (α + β) (τ h)`.
   The left side is the coefficient after applying `τ` to coefficients of
   `T_t(h)`. The right side is exactly the coefficientwise binomial definition
   of continuous formal translation in proof Steps 7--8. Natural-number scalar
   multiplication is the integral binomial factor in `C`, valid in every
   characteristic. Coefficients with `|β| ≤ t` uniquely determine the quotient
   class: Mathlib's `MvPolynomial.mem_pow_idealOfVars_iff'` says its kernel is
   precisely the polynomials with all these coefficients zero. Hence this
   renders the full asserted translation identity, not just its constant term
   or polynomial inputs. No topology choice or convergence hypothesis is
   inserted: the node defines its continuous translation coefficientwise, and
   this is that formula in all coefficients. The proof docstring records its
   adic continuity estimate.

Dependency interfaces read and used:

- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial`, `MvPolynomial.algHom_ext`; `Mathlib.Algebra.MvPolynomial.Eval`,
  `MvPolynomial.aeval`, coefficient maps and constant coefficient.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`, used in the affine
  interpretation of the étale hypothesis and imported through the étale module.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` and its `HasRingHomProperty @Etale RingHom.Etale`
  instance. `Mathlib.RingTheory.RingHom.Etale`, `RingHom.Etale`, gives the same
  hypothesis on the coordinate ring map without requiring equal scheme universes.
- `def-trf-diagonal-jets`: `Sheaf.RingTheory.DiagonalJets`,
  `DiagonalJets.principalParts`, read in full, including its docstring and the
  underlying `KaehlerDifferential.ideal` multiplication-kernel abbreviation.
- `def-weil-module-base-change`: `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `LinearMap.baseChange`, `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.AlgebraTensorModule.distribBaseChange`; the record explicitly
  uses left tensor-factor extension of scalars, as does this theorem.
- `def-weil-pbc-multivariate-power-series`:
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, `MvPowerSeries.coeff`
  and `MvPowerSeries.X`; these are the actual coefficient families of the node.
- Proof-only: `Sheaf.RingTheory.FormallyEtaleAssociatedGraded`,
  `Ideal.formallyEtale_powerQuotient_associatedGraded`, with its full signature
  and proof docstring read; its hypothesis is formal étaleness and surjectivity
  modulo the ideal, not a hidden equality of ideals.
- Other recorded proof interfaces are Mathlib matches:
  `Mathlib.RingTheory.Etale.Basic`, `Algebra.Etale.baseChange`;
  `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`,
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`;
  `Mathlib.RingTheory.Unramified.Basic`,
  `Algebra.FormallyUnramified.iff_comp_injective` and `.comp_injective`;
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`, `.mk`;
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, `.lift`, `.ext'`;
  `Mathlib.LinearAlgebra.TensorProduct.Map`, `LinearMap.rTensor`;
  `Mathlib.Algebra.Algebra.Hom`, `AlgHom`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.algebra`, `.mkₐ`;
  `Mathlib.RingTheory.Ideal.Operations`, ideal products and powers.
  All these declared signatures/docstrings were opened, and the available
  proof-dependency modules are imported directly or through their owning module.

Edge cases checked before finalizing:

- `n=0`: `Fin 0` is empty, the variable ideal is zero, only the zero exponent
  indexes the basis, empty products of binomial coefficients are one. The
  hypotheses permit arbitrary étale algebras over `R₀`, not just `R₀` itself.
- `t=0`: the quotient kills all variables, only `β=0` occurs, and translation
  reduces to the constant coefficient formula. Truncation also includes `s=t`.
- Zero rings: there is no `Nontrivial` hypothesis on any coefficient ring;
  `Module.Basis` over a zero ring is allowed. All tensor and quotient maps still
  have their actual data and all displayed coefficient equalities typecheck.
- Positive characteristic and nonflat base changes: no inverses, factorials,
  field structure, flatness, Noetherianity, or regularity assumption occurs.
- Universes `u v w x` are independently explicit; every variable is bound with
  `autoImplicit false`. No artificial equality of universes or implicit
  restriction on the base-change or power-series coefficient rings is imposed.

Searches (2026-10-24, prescribed `msearch.py Q31 <item>`):

- LeanFinder: `etale polynomial coordinates higher principal parts diagonal ideal
  quotient Taylor translation base change`: 8 hits, including standard étale
  presentations and `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`;
  none states the higher principal-parts coordinate and compatibility theorem.
- Loogle: `MvPolynomial, MvPowerSeries, Algebra.FormallyEtale`: 0 hits.
- LeanSearch: `etale principal parts higher diagonal quotient polynomial coordinates
  truncation base change Taylor expansion`: 8 hits, including
  `Algebra.Etale.baseChange`, univariate polynomial Taylor isomorphisms, and
  `MvPowerSeries.trunc`; none is an exact statement match.
- msearch grep: `principalParts|principal_parts|hasseDeriv|hasse.*deriv` in
  `RingTheory`: hits are Hasse derivatives for one-variable/Laurent series and
  unrelated principal-parts residue constructions, not this theorem.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `principalParts|principal.parts|diagonalJets|etale.relative.principal|formalTranslation|hasseDeriv|hasse.*deriv`:
  the existing `DiagonalJets.principalParts` is used; residue principal parts are
  a different notion. Searching the item's exact blueprint id in upstream Lean
  gives no match. No exact theorem or coordinate quotient interface was found.
- Additional Mathlib/project grep for origin variable ideals found
  `MvPolynomial.idealOfVars` in `Mathlib.RingTheory.MvPolynomial.Ideal`; I removed
  the provisional duplicate ideal definition and now use that declaration.
  `mem_pow_idealOfVars_iff'` also confirms the representative-independent
  coefficient rendering of the translation identity. Full intended declaration
  names were checked in `dag/lean_names_upstream.json` and both source trees;
  there is no collision in the `DiagonalJets` namespace.

No STATEMENT-DISPUTED issue or unusable dependency was found. The old example
`Sheaf.CategoryTheory.CompactObject` is now withdrawn; I read its replacement
`WeilConjectures.CategoryTheory.CompactObject` and the recorded node instead.
Only the sandbox has been written; compilation uses `scompile.py` exclusively.

## Second reading by Q31

The dispatcher expressly prohibits starting other agents; the maintainer performs
an independent review of this delivery. This section records my separate final
cross-check, not a claim of an independent worker reading.

I reopened the node and compared every conjunct with the complete theorem. I
checked that the two occurrences of `coordinateTaylor` use the actual inverse
of the same equivalence, that the first-factor structure has not been exchanged
in `principalParts`, and that tensor commutation is applied consistently in the
base-change representative formula. The coefficient identity quantifies over
all formal-series exponents `α` and all retained `β`, not merely over polynomial
series or low total `Z,Y` degree. The basis indexing includes degree zero, and
`hφ` is the given map's étaleness, not formal smoothness alone. I also checked
that all helpers have data and that only the theorem proof is postponed.

The only mismatch found in this pass was a duplicate provisional definition of
the polynomial variable ideal; it was removed in favor of
`MvPolynomial.idealOfVars`. No node or dependency statement needed correction.
