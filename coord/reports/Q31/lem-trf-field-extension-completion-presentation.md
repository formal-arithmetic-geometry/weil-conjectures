## Worker report

This repairs the returned stage-2 delivery at immutable head `48876594161e`.
The retained sandbox had only the four launcher brief markers: no Lean module,
node copy, report or compiler evidence. The return describes that same empty
stage-2 payload. This packet supplies the actual theorem rather than rebasing
or re-pushing that payload. Its node was compared with the current shared node:
all fields other than `lean` are identical. The delivery wrapper refreshes
`newtargets-dag` and constructs the rebased commit; no direct Git command or
write was made in either read-only checkout.

The new module is `Sheaf.RingTheory.FieldExtensionCompletionPresentation`; its
only declaration is `Algebra.field_extension_completion_presentation`, with
`by sorry` as the entire proof. There are no helper definitions, additional
postponed theorems, new nodes or dependency-record repairs. All types are the
existing Mathlib constructions. In the table, A denotes `Localization.AtPrime p`,
B denotes `Localization.AtPrime q`, and hats denote
`AdicCompletion (IsLocalRing.maximalIdeal _) _`; these are report abbreviations
only, not local Lean notation or new definitions.

| Node hypothesis or clause | Exact Lean rendering and meaning |
| --- | --- |
| An extension of fields k ⊆ K | `{k : Type u} {K : Type w} [Field k] [Field K] [Algebra k K]`. A unital map between fields is injective; no algebraicity or finiteness of K/k is assumed. |
| A finitely generated k-algebra S | `{S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]`. This is the algebra-instance form of the recorded `RingHom.FiniteType (algebraMap k S)`, equivalent by `RingHom.finiteType_algebraMap`. |
| A maximal ideal p | `(p : Ideal S) [p.IsMaximal]`. |
| F = S/p, finite separable over k | `p.ResidueField`, `[FiniteDimensional k p.ResidueField]`, and `[Algebra.IsSeparable k p.ResidueField]`. The recorded localization dependency defines `p.ResidueField` as A/m; for maximal p the canonical S-algebra identification with S/p is an isomorphism. |
| A = S_p | Every occurrence uses `Localization.AtPrime p`, the recorded Mathlib localization, with its actual localization map. |
| Ahat is the inverse limit A/(pA)^r | `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)`. `Localization.AtPrime.map_eq_maximalIdeal` identifies this ideal with pA. This is the recorded compatible-sequence completion. |
| Fix a k-embedding F → K | `(ι : p.ResidueField →ₐ[k] K)`. Injectivity follows from the field source. |
| q is the kernel of s tensor c ↦ ι(s mod p)c | `(q : Ideal (S ⊗[k] K)) [q.IsPrime]` and `hq` identify q with `RingHom.ker` of `Algebra.TensorProduct.lift (ι.comp (IsScalarTower.toAlgHom k S p.ResidueField)) (AlgHom.id k K) (fun _ _ ↦ Commute.all _ _)`. `lift_tmul` is exactly the required formula. |
| B = (S tensor K)_q and Bhat its completion | `Localization.AtPrime q` and `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)`. There is no abstract substitute for B or Bhat. |
| Fix a k-algebra residue section σ | The `σ` binder is a `p.ResidueField →ₐ[k] Ahat`. `hσ` says `AdicCompletion.evalOneₐ mA (σ c) = c` for every c. The codomain of this projection is definitionally `p.ResidueField`. |
| Any number n of variables and s of equations | `(n s : ℕ)`, `Fin n`, and `Fin s`, with no lower bounds or nonemptiness assumptions. |
| A presentation F[[t]] → Ahat over the action through σ | `φ : MvPowerSeries (Fin n) p.ResidueField →ₐ[k] Ahat`; `hφ_constants : ∀ c, φ (MvPowerSeries.C c) = σ c` says exactly that φ is an F-algebra map for the specified section. An independent F-action on Ahat is not assumed. |
| The presentation is onto | `hφ_surjective : Function.Surjective φ`. |
| Its kernel is (f_1,...,f_s) | `f : Fin s → MvPowerSeries (Fin n) p.ResidueField` and `hφ_kernel : RingHom.ker φ.toRingHom = Ideal.span (Set.range f)`. |
| The kernel lies in the variable ideal | `hf` is the inclusion of that span in `Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) p.ResidueField))`. |
| Continuity of the input presentation | `hφ_continuous : ∀ r : ℕ, ∃ N : ℕ, (variableIdeal ^ N).map φ.toRingHom ≤ (mA.map (algebraMap A Ahat)) ^ r`. This is continuity for the two indicated adic topologies, expressed with ideals. |
| The canonical map A → B | The conclusion provides `g : A →+* B` with `g (algebraMap S A a) = algebraMap (S ⊗[k] K) B (a ⊗ₜ[k] 1)` for every a. Localization's universal property uniquely determines g from this equation. |
| The induced canonical map Ahat → Bhat | The conclusion provides `h : Ahat →+* Bhat`. For every r, z and a representing z at level r, its r-th projection equals the class of g(a). This determines h on every finite quotient and hence on the inverse limit, rather than merely on the dense image of A. |
| Coefficients of equations transported through ι | The source of `e` is `MvPowerSeries (Fin n) K ⧸ Ideal.span (Set.range (fun j : Fin s ↦ MvPowerSeries.map ι.toRingHom (f j)))`. |
| Isomorphism to the actual Bhat | `e` is a `≃+*` from exactly that quotient to Bhat. |
| Isomorphism of K-algebras | The first conjunct specifies `e (Ideal.Quotient.mk _ (MvPowerSeries.C c))` as the image of `1 ⊗ₜ[k] c` under tensor localization followed by the canonical completion map. These are exactly the source and target structural maps from K. Thus the ring equivalence is K-linear for the prescribed, canonical action; an arbitrary K-action or comparison is not supplied. |
| The chosen F-algebra presentation is preserved | For every series z over F, `e (Ideal.Quotient.mk _ (MvPowerSeries.map ι.toRingHom z)) = h (φ z)`. This is the commutative square of Tag 0C54, including `h (σ c) = image(ι c)` when z is constant. |
| Every variable has its chosen image from Ahat | `∀ i : Fin n, e (Ideal.Quotient.mk _ (MvPowerSeries.X i)) = h (φ (MvPowerSeries.X i))`. |
| Complete local K-algebras | The final existential supplies `IsLocalRing` on the displayed quotient and on Bhat, with `IsLocalHom e.toRingHom` and `IsAdicComplete` for each maximal ideal. A local ring isomorphism identifies maximal ideals and every power, so e and its inverse are automatically continuous for these complete local topologies. |

The explicitly bound q and its prime instance are a way to name the specified
kernel for `Localization.AtPrime`; they do not restrict the point: the tensor
map sends `1 ⊗ c` to c, so its kernel is maximal, in particular prime. The
hypothesis hq completely fixes it. Similarly g and h are *conclusions*, with
normalizations determining their values uniquely. They are not arbitrary maps
assumed as extra hypotheses, nor definitions chosen from a mere existence axiom.

The ring-equivalence encoding avoids a noncanonical global right-factor algebra
instance on S tensor K. There is no universe equality, size truncation, hidden
`let` in the signature, local notation, private declaration or hollow definition.
The module uses `set_option autoImplicit false` and `universe u v w`.

Statement-dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType` and `Algebra.FiniteType`; the former is defined using the
  latter for the induced algebra. The existing equivalence at `algebraMap` was read.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`, with
  `Localization.AtPrime.map_eq_maximalIdeal`; and
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Ideal.ResidueField`.
  `Ideal.Fiber` is the dependency's additional clause, not needed in this signature.
- `def-weil-pbc-separable-algebraic-extension`: `Mathlib.FieldTheory.Separable`,
  `Algebra.IsSeparable`; its docstring and `IsSeparable.isIntegral` confirm that
  algebraicity is included.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion` and `IsAdicComplete`, with the ring/algebra and quotient maps
  `AdicCompletion.evalₐ` and `evalOneₐ` in
  `Mathlib.RingTheory.AdicCompletion.Algebra`. `LocalRing` imports these publicly.
- `def-weil-pbc-multivariate-power-series`:
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, `C`, `X`, and `map`.
  `Fin n` is the node's finite variable set.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, supplied by
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with its algebra multiplication
  and canonical universal map in `Mathlib.RingTheory.TensorProduct.Maps`,
  `Algebra.TensorProduct.lift`. This uses the dependency's Mathlib match,
  which does not need a `lean` record.

All statement dependency modules are present through public imports. The existing
proof dependencies are imported without `public`: finite type Noetherianity
(`FiniteType`), field-extension faithful flatness (`Flat.FaithfullyFlat.Basic`),
flat localized maps (`RingHom.Flat`),
`Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`,
`Sheaf.AlgebraicGeometry.DimensionAtPointFieldExtension`,
`WeilConjectures.RingTheory.AdicCompletionNoetherian`, the local-completion and
completion-mod-ideal facts (`AdicCompletion.LocalRing`, already public),
`Sheaf.RingTheory.FlatCompletion`,
`Sheaf.RingTheory.PowerSeriesUniversalPropertyComplete`,
`Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete`, complete-source
surjectivity (`AdicCompletion.Functoriality`), and
`Sheaf.RingTheory.FlatModInjective`. The current upstream
`WeilConjectures.RingTheory.AdicCompletionNoetherian` was read using
`scompile.py --source` because it is absent in the older local source checkout.
There is no import of the downstream separable-closed-point theorem: its helper
structure imposes n ≥ 2 and its theorem cites this item as a proof dependency.

Edge cases checked before and after writing:

- `n = 0`: `Fin 0` is empty, the variable ideal is zero, and hf makes every
  equation zero. Surjectivity and the constant condition then force Ahat ≅ F;
  the asserted extension is K ≅ Bhat. No variable or indexing case is excluded.
- `n = 1` is retained; `S = k[x]/(x²)` at (x) has the expected presentation
  `K[[x]]/(x²)`, so nilpotents are retained. No reducedness assumption on S was added.
- `s = 0`: the relation span is bottom and the quotient is the full power series
  ring. Zero and repeated equations are permitted for any s.
- `K = k`, when the specified embedding exists, gives the identity comparison
  after the canonical identifications. Transcendental extensions K/k, such as
  k(t)/k, are also allowed; only F/k is finite dimensional.
- For a nontrivial finite separable F/k and two embeddings into a splitting
  field K, hq distinguishes the two corresponding points. The section is the
  given σ and is not replaced by a convenient choice.
- Fields of every characteristic, including positive characteristic, are
  allowed. A purely inseparable residue extension is correctly excluded by
  `Algebra.IsSeparable`. The zero ring S has no maximal p, just as in the node.
- The coordinate r = 0 is the zero quotient and imposes no false restriction;
  all positive r still specify the actual inverse-limit map.

Searches made with `msearch.py` (raw responses are retained in sandbox
`searches.jsonl`):

| Tool | Query | Result |
| --- | --- | --- |
| leanfinder | `Completion of a finite type local algebra after field extension is a power series quotient with extended coefficients` | 8 hits, headed by `PowerSeries.algEquivQuotientWeierstrassDistinguished` and `LaurentSeries.powerSeriesAlgEquiv`; they concern Weierstrass or valued-field constructions, not this local completion comparison. |
| loogle | `AdicCompletion, MvPowerSeries, TensorProduct` | 0 hits. |
| grep, RingTheory | `completion.*tensor\|MvPowerSeries.*base.change\|AdicCompletion` | 25 hits; relevant APIs include `MvPowerSeries.toAdicCompletion`, completion lifts and general power series constructions; none states this theorem. |
| leansearch | `field extension local completion power series quotient coefficients` | 8 hits about Weierstrass division and power series coefficients, no exact theorem. |

Additional `rg` searches of `WeilConjectures`, `lean/Sheaf`, the upstream name
index and Mathlib found no `field_extension_completion_presentation` declaration.
The item-id search of upstream `WeilConjectures` returned no match. Searches
for completion/base-change/presentation terms found the downstream
`SeparableClosedPointFormalPresentation`, whose theorem includes further
Jacobian clauses and `n ≥ 2`; it is not an exact existing declaration of this
item. Existing `FormalLocalPresentation` and its source were read as well:
its `two_le` field explains why it cannot encode this unrestricted input.
The delivered module defines no competing notion; it simply uses the general
Mathlib constructors inline.

No statement correction or dispute is needed. The item still has exactly its
original statement, statement dependencies, proof and proof dependencies.

Validation: the exact delivered module was checked with
`scompile.py Q31 lem-trf-field-extension-completion-presentation
lean/Sheaf/RingTheory/FieldExtensionCompletionPresentation.lean`.
The server compiled it both as a sandbox and at its library module path:
3.9 seconds and 4.3 seconds respectively, with no error or warning. Output is
retained in sandbox `compile-1.log`. Line widths and the verbatim `lean.statement`
were checked locally without running any prohibited project checking tool.

## Second reading by Q31

This is the author's separate, substantive second pass; no other agent was
started. The maintainer's independent review remains the independent reading.
I reopened the entire node, the delivered Lean signature, all six recorded
statement dependencies, the current unit `sk-i-curve-zero`, the direct citing
node `lem-trf-separable-closed-point-formal-presentation`, and Stacks
`varieties.tex`, Tag 0C54 including the commutative diagrams and its complete
proof, together with the relevant Tags 0C4Y and 0C50.

The check found and avoided two interface mismatches before the final draft:
using the landed `FormalLocalPresentation` would add the unrequested `2 ≤ n`
hypothesis; using the downstream theorem for its auxiliary maps would reverse
the proof dependency. The delivered signature instead uses unrestricted n/s
and only the existing general Mathlib constructions. No dependency node was
modified to accommodate the statement.

I checked the hypotheses one by one against the table above: three independent
universes, fields and algebra structures, finite-type S, maximal p, finite
separable residue extension, the chosen embedding, the exact evaluation kernel,
the chosen k-section with its actual residue equation, and the arbitrary
continuous surjection with exactly the displayed kernel and containment. None
of finite K/k, algebraically closed K, reduced S, n ≥ 2, or an arbitrary
unrelated F-action occurs. The explicit prime instance on q is available for
the prescribed kernel and is only structural data for the named localization.

I then checked each conclusion against the two Tag 0C54 diagrams. The source
quotient uses coefficientwise `MvPowerSeries.map ι.toRingHom` on *each* f_j,
not the untransported ideal. The direction of e is from the K-power-series
quotient to Bhat. The constant equation uses the right tensor factor and the
actual localization and completion maps, so the coefficient action is fixed.
The all-series equation is the lower-square compatibility with the chosen φ,
and the separate variable equation has exactly h(φ(X_i)) on its right side.
The section is preserved by specializing the all-series equation to C(c)
and using hφ_constants. The normalized maps g and h cannot float: the equation
on S determines the localization map, and the r-th coordinate condition for
all r determines its map of completions. Finally the local instances,
`IsLocalHom`, and the two `IsAdicComplete` clauses express the phrase
"complete local K-algebras" and ensure the inverse is continuous as well.

The edge-case rereading retained n=0, n=1, s=0, the identity field extension,
nontrivial residue embeddings, nilpotents, arbitrary characteristic and
transcendental K/k. The whole proof docstring follows the node's six proof
steps, including the complete-source surjectivity argument before the
flat-mod-injective argument. There is one whole-proof sorry and no data sorry.
The clean per-file server compile checks the actual final statement, rather
than a shortened probe. This resolves the returned H1/H2/H3/H8/H10/H11 defects
by supplying their missing artifacts and concrete mathematical comparison.

The prescribed `deliver2.py Q31 lem-trf-field-extension-completion-presentation
--no-push` returned `OK (dry run): commit 5b05838207 passes the preflight and
compiles; nothing pushed`. Its staged list contained exactly this report,
the item node, and the single theorem module. The wrapper reported no stale
non-owned fields. The normal delivery below repeats preflight and compilation
on the rebased packet including this validation record.
