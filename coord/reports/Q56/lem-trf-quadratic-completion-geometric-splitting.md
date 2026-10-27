## Worker report

Delivered module: `Sheaf.RingTheory.QuadraticCompletionGeometricSplitting`.
Its only declaration is the theorem `Algebra.quadratic_completion_geometric_splitting`,
with proof `sorry`. No definitions, helper nodes, dependency repairs, or statement
corrections are needed. The item JSON changes only in `lean`.

Sources read: Stacks `curves.tex`, lemma-nodal-algebraic (0C49), and lemma-nodal
(0C4D), especially the first paragraph of its proof; `varieties.tex`,
lemma-base-change-complete-local-ring (0C54). The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof were consulted for the recorded branch; this item is the nodal
commutative-algebra sublemma, not that unit's statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `k`: `{k : Type u} [Field k]`.
- A finitely generated commutative `k`-algebra `S`:
  `{S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]`.
  `Algebra.FiniteType` is the algebra-instance form of the recorded
  `RingHom.FiniteType`, whose definition is precisely that predicate for the
  ring map's induced algebra instance.
- A maximal ideal `p`: `(p : Ideal S) [p.IsMaximal]`.
- `A = S_p`: every occurrence of `A` is `Localization.AtPrime p`.
- `F = S/p`: represented by `p.ResidueField`, the residue field of `S_p`.
  For maximal `p` this is the canonical, coefficient-preserving identification
  `Ideal.bijective_algebraMap_quotient_residueField`, not a different field
  extension. Its constant and residue maps are the same maps through this
  identification. This is also the encoding used in the recorded completion
  presentation dependency.
- Finite separability of `F/k`: `[FiniteDimensional k p.ResidueField]`
  and `[Algebra.IsSeparable k p.ResidueField]`.
- `A`'s maximal-ideal-adic completion: the literal
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (Localization.AtPrime p)`.
- The coefficient section: the `k`-algebra homomorphism `σ` with the exact equation
  `hσ : ∀ d, AdicCompletion.evalOneₐ ... (σ d) = d`.
- The quadratic coefficients and nondegeneracy: `(a b c : p.ResidueField)` and
  `hΔ : b ^ 2 - 4 * a * c ≠ 0`. Its power-series expression is written directly
  with `MvPowerSeries.C` and `MvPowerSeries.X 0`, `MvPowerSeries.X 1`.
- The given complete local `F`-algebra isomorphism: `e₀` is the inverse-direction
  ring equivalence from this quadratic quotient to `A`'s completion. `he₀`
  says it sends the class of the constant `d` to `σ d`, exactly specifying
  `F`-linearity for the action through `σ`, without an arbitrary second action.
  On residues `hσ` makes this the identity on `F`. Both rings are intrinsically
  complete local rings: finite type over a field makes `A` Noetherian, and the
  quadratic quotient is a quotient of a Noetherian complete local power-series
  ring. A ring equivalence between local rings preserves the unique maximal
  ideals and all their powers, hence is continuous in both directions. Thus
  omitting redundant topology structures from the binder does not weaken the
  given complete local isomorphism hypothesis.
- Every algebraic closure and every embedding:
  `(Ω : Type w) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]`
  and `(ι : p.ResidueField →ₐ[k] Ω)`. The universes `u v w` are independent;
  no restriction of the base ring or algebraic-closure size is imposed.
- The displayed evaluation kernel: `q` with `hq` setting it equal to the kernel
  of `Algebra.TensorProduct.lift` applied to `ι` after the residue map, and
  `AlgHom.id k Ω`. This evaluates `s ⊗ d` as `ι (s mod p) * d`.
  The binder `[q.IsPrime]` merely makes the explicitly determined localization
  type available; it follows from `hq` since the evaluation targets a field.
  It imposes no additional mathematical condition.
- `B = (S ⊗_k Ω)_q`: the literal `Localization.AtPrime q`.
- `q` lies over `p`: the first conjunct is contraction along
  `Algebra.TensorProduct.includeLeft` equal to `p`.
- `B/m_B = Ω`: the second conjunct gives `ρ : q.ResidueField ≃+* Ω`.
  By definition `q.ResidueField` is precisely the residue field of `B`.
  Its equation on every `1 ⊗ d` specifies the evaluation identification and
  makes it an isomorphism of `Ω`-algebras, rather than just abstract fields.
- The split completed ring: the third conjunct gives `e` from `B`'s completion
  to the literal quotient `MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`.
  Its equation on constants says exactly that it respects the canonical
  `Ω`-action through `1 ⊗ d` and then localization and completion.
  The remaining existential local-ring structures, `IsLocalHom`, and the two
  `IsAdicComplete` conjuncts explicitly give the complete local content.
  As above a ring equivalence preserves maximal-ideal powers, so continuity
  of the isomorphism and its inverse follows without choosing topologies.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` / `Algebra.FiniteType`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`,
  with the maximal-ideal quotient identification stated above.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.LocalRing`:
  `AdicCompletion`, `IsAdicComplete`, and its completed-local-ring instances;
  `.Algebra`: `AdicCompletion.evalOneₐ`.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosure`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, supplied together
  with its algebra structure and evaluation by `Mathlib.RingTheory.TensorProduct.Maps`.

The stated proof dependencies are imported privately:
`Sheaf.RingTheory.FieldExtensionCompletionPresentation`
(`Algebra.field_extension_completion_presentation`),
`WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
(`MvPowerSeries.power_series_field_cohen_regular_complete`), and
`WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete`
(`MvPowerSeries.exists_ringHom_of_isAdicComplete`). Their full signatures and
docstrings were read. `lem-trf-separable-evaluation-local-base-change` currently
has neither `lean` nor `mathlib_match`, so has no module to import; this is a
proof dependency only and is not needed to type the present statement.
`def-weil-algebraic-closure` is a Mathlib dependency and is imported publicly.

Edge cases checked before writing: `a = 0` forces `b ≠ 0`, and the two linear
forms `v`, `bu+cv` are independent; the characteristic-two case still has
`b ≠ 0` and uses no division by two; `a ≠ 0` permits division by `a` and the
discriminant identity gives distinct roots; split forms already isomorphic to
`uv` are included; a nonsplit form over the residue field is permitted; repeated
linear factors have discriminant zero and are correctly excluded. Zero `S`
cannot supply a maximal ideal, so no empty closed point is accidentally included.
All field and ring universes are bound explicitly; `autoImplicit` is false.

Searches executed for an existing full statement:

- `msearch.py ... leanfinder`: "A separable quadratic completion splits
  geometrically after extension to an algebraic closure as power series modulo uv".
  Eight hits concerning quadratic extensions, separably closed fields and
  polynomial splitting; none gives the completed-local-ring assertion.
- `msearch.py ... loogle`: `MvPowerSeries, IsAlgClosed`: zero hits.
- `msearch.py ... grep`: `quadratic.*(split|factor)|nodal|nondegenerate.*quadratic`
  in `RingTheory`: zero hits.
- `msearch.py ... leansearch`: "Base change a completed binary quadratic
  hypersurface to an algebraic closure and split into two independent linear factors".
  Eight hits including `IsAlgClosed.splits`, degree-two polynomial splitting,
  and `QuadraticForm.baseChange`; these are ingredients, not this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the quadratic, nodal and
  geometric-splitting phrases and the item id found related formal-Jacobian,
  normalization and nodal-point modules, but no existing full statement.
  Their quadratic expressions were inspected; no helper notion is redefined here.
- Exact declaration/module-name search in `dag/lean_names_upstream.json`,
  Mathlib, `lean/WeilConjectures` and `lean/Sheaf`: no collision.

Compilation: prescribed `scompile.py Q56 lem-trf-quadratic-completion-geometric-splitting`
accepted both sandbox and library-module checks (3.0 s and 3.1 s), with no errors
or warnings. The module has one `sorry`, its named theorem, and no proofs of
auxiliary results. No statement dispute or node fault was found.

## Second reading by Q56

This is the dispatcher's single-worker re-reading; the independent maintainer
review reads the delivery. I re-opened the node and the completed module and
checked each hypothesis and each of the three conclusions against the mapping
above. In particular `he₀` is essential: a bare ring equivalence would forget
the chosen coefficient section; it is present. The residue conclusion specifies
the `Ω`-scalar map with `ρ`, and the completion conclusion specifies it with
`e`, so neither conclusion is an arbitrary ring isomorphism. The `e₀`
orientation is opposite the node's displayed isomorphism, but inversion is
exactly equivalent and preserves its constant equation and adic continuity.
`p.ResidueField` was checked against the canonical maximal-ideal quotient
isomorphism; it introduces no extra separability hypothesis. The prime-ideal
instance on the evaluation kernel is forced by its defining equality. Checked
the characteristic-two and nonsplit cases again. No mismatch or change was
found in this re-reading; no independent second agent was started, as directed.
