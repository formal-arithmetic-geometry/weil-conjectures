## Worker report

The new module `Sheaf.RingTheory.SplitLocalPowerSeriesSectionCriterion` states
`IsLocalRing.splitLocal_powerSeries_section_criterion`, with its whole proof `sorry`.
It introduces no definitions, auxiliary theorems, new nodes or dependency repairs.
The item's only changed field is `lean`.

Source read: `literature/stacks-project/formal-defos.tex`, Tag 06SG,
`lemma-power-series`, statement and complete proof (lines 1099 onward).
The node already resolves the printed “left inverse” terminology by recording the
right-inverse equation actually used in the argument. Its current statement is
retained verbatim. The strengthened explanatory construction clauses of the node
are all included, rather than merely stating the final isomorphism implication.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Commutative rings B and C, common field l | Independent `Type u`, `Type v`, `Type w`; `[CommRing B] [CommRing C] [Field l]` |
| Noetherian and local | `[IsNoetherianRing B] [IsNoetherianRing C] [IsLocalRing B] [IsLocalRing C]` |
| Specified residue fields | `eB : ResidueField B ≃+* l`, `eC : ResidueField C ≃+* l`; no coefficient-field embedding is assumed |
| Their unique maximal ideals | Mathlib's `IsLocalRing.maximalIdeal` throughout |
| Complete for those ideals | The two `[IsAdicComplete (maximalIdeal ...) ...]` binders |
| Inclusion i and the B-algebra structure on C via i | `[Algebra B C]`, with i represented by `algebraMap B C`; `hi` states injectivity. Every ring map into a commutative ring yields this algebra structure, so this encodes the given map without restricting it |
| Locality of i and rho | `[IsLocalHom (algebraMap B C)]`, `[IsLocalHom ρ]`; for local rings this is exactly inverse image of maximal ideal equals maximal ideal |
| Both maps induce the identity on l | `hires` and `hρres` are commutative residue squares expressed on the original rings, hence on their residue fields by surjectivity of `residue` |
| rho i = id | `hsplit : ρ.comp (algebraMap B C) = RingHom.id B` |
| I = ker rho | The ideal `RingHom.ker ρ` itself, with no second definition |
| r >= 0 and x_j in I | `r : ℕ`, `x : Fin r → RingHom.ker ρ` |
| Images are an l-basis of I/m_C I | `b : @Module.Basis (Fin r) l ...` and `hb`. The quotient is the actual module quotient of I by `(maximalIdeal C • ⊤ : Submodule C I)`; its natural `C/m_C` action is transported along `eC.symm.toRingHom` using `Module.compHom`. This is the l-action determined by the specified marking, not a separately chosen scalar structure |
| S = B[[X_1,...,X_r]] | `MvPowerSeries (Fin r) B`; no local notation or alternate series definition |

Conclusion-by-conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| S is Noetherian local | First two conjuncts, `IsNoetherianRing ... ∧ IsLocalRing ...` |
| Its maximal ideal is (m_B, X_1,...,X_r) | Explicit equality with `(maximalIdeal B).map MvPowerSeries.C ⊔ Ideal.span (Set.range MvPowerSeries.X)` |
| Complete for that maximal ideal | Next `IsAdicComplete` conjunct |
| S has residue field l | `∃ eS : ResidueField S ≃+* l`, with equality specifying the constant-coefficient residue map |
| Existence of a continuous B-algebra map sending X_j to x_j | `∃ φ : S →ₐ[B] C`, its displayed variable equations, and explicit `@Continuous` using the two `Ideal.adicTopology` structures |
| Uniqueness among exactly those maps | Universal clause on `ψ : S →ₐ[B] C`, assuming only its variable values and the same maximal-ideal-adic continuity, concluding `ψ = φ` |
| phi is local | `IsLocalHom φ.toRingHom` |
| phi induces the identity on l | Equality of its residue composite with `eS.toRingHom.comp (residue S)` |
| Every n >= 1 gives a canonical quotient map phi_n | The family `p n` at exponent `n + 1`, with its composite with the quotient projection equal to the quotient projection after phi. This equation uniquely characterizes the induced map since each quotient projection is surjective; it is not an arbitrary family of maps |
| These maps are surjective | `Function.Surjective (p n)` for every natural n |
| Quotients are Artinian local rings with residue l | Explicit `IsArtinianRing` and `IsLocalRing` conjuncts for both quotients. Families `qS n`, `qC n` are surjective ring maps to l and their composites with the projections are exactly the previously marked residue maps. A surjection onto a field has maximal kernel, and a local ring has a unique maximal ideal, so these equations specify precisely the induced residue-field identifications |
| Each quotient map respects the residue marking | `(qC n).comp (p n) = qS n` (locality of `p n` is also displayed) |
| Sections exist for all sufficiently large n | Antecedent `∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ σ ...` |
| Sections are local and induce identity on l | `IsLocalHom σ ∧ (qS n).comp σ = qC n` |
| phi_n sigma_n = id | `(p n).comp σ = RingHom.id ...`, in exactly that order |
| No B-linearity or compatibility imposed on sections | Each `σ` is merely a `RingHom`; each level has its own existential, and there is no relation across levels |
| phi is an isomorphism of complete local B-algebras | `∃ e : S ≃ₐ[B] C, e.toAlgHom = φ`, together with explicit maximal-ideal-adic continuity of `e.symm`. Forward continuity and locality have already been stated for phi; a local-ring isomorphism also has local inverse |

The indexing `n + 1` ranges over exactly every positive exponent, including exponent
one, without inventing a local/residue structure on the zero ring at exponent zero.
The eventual section condition is unchanged by this shift.

Dependency declarations used, with their source declarations and docstrings read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, abbreviation for the self-module being Noetherian.
- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs` (mathlib leaf).
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion` and companion `IsAdicComplete`. The theorem needs the latter,
  equivalent to bijectivity of the canonical inverse-limit map, as recorded on the node.
- `def-weil-pbc-multivariate-power-series`:
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, imported publicly through
  `Mathlib.RingTheory.MvPowerSeries.Inverse`, which also gives the local-ring instance.
- Existing Mathlib module quotient and scalar transport:
  `Mathlib.Algebra.Module.Torsion.Basic`, the canonical `Module (C ⧸ m) (I ⧸ m • ⊤)`
  instance; `Module.compHom`; `Mathlib.LinearAlgebra.Basis.Defs`, `Module.Basis`.
- Existing residue fields, local homomorphisms, quotient rings and adic topology:
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
  `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`.

The already-stated proof dependencies are plain imports, including the canonical
upstream `WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase` and
`WeilConjectures.RingTheory.PowerSeriesAdicEvaluation` modules, the recorded
`Sheaf.RingTheory.CompleteLocalCotangentGradedRigidity`, and Mathlib's
`MvPowerSeries.Equiv`, `Ideal.KrullsHeightTheorem`, and `HopkinsLevitzki` modules.
The complete six-step natural-language proof is in the theorem docstring.

Edge cases checked mathematically:

- `r = 0`: the basis is empty and Nakayama gives I = 0; the series ring is B.
  The `Fin r` family and the empty ideal span include this case without assumptions.
- Positive exponent one: both finite quotients are their residue fields. All
  assertions apply at `n = 0`, meaning exponent one; exponent zero is correctly excluded.
- B or C a field: maximal ideal zero, with its discrete adic topology and unchanged
  completeness convention. No nonzero-maximal-ideal or positive-dimension assumption occurs.
- Mixed characteristic and unequal carrier universes: no l-algebra structure on B or C
  is required and `u`, `v`, `w` are independent.
- The split map forces i injective, but the explicit `hi` records the node's inclusion
  hypothesis as written. No section is forced to be B-linear or compatible with another.

Searches for an existing statement (all negative for the full criterion):

- `msearch.py Q148 lem-sfb-split-local-power-series-section-criterion leanfinder`
  query: “A split inclusion of complete Noetherian local rings has a power series
  presentation which is an isomorphism if finite maximal ideal power quotients admit
  ring sections”. Result: 8 hits, all one-variable Weierstrass factorization/division
  or adic-complete Henselian results, not this criterion.
- `msearch.py ... loogle 'MvPowerSeries, IsLocalRing, IsAdicComplete'`:
  `OK 0 hit(s)`.
- `msearch.py ... grep 'IsLocalHom|IsAdic|quotientCotangent|Cotangent'
  RingTheory/MvPowerSeries`: 3 hits, the `map.isLocalHom` API in `Inverse.lean`;
  no split local section criterion.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for split-local names and
  power-series/section combinations found only unrelated punctured-spectrum section
  statements, the existing smooth complete-local theorem, and cotangent criteria.
  `grep -rn 'lem-sfb-split-local-power-series-section-criterion' lean/WeilConjectures`
  found no match. None states this theorem.
- Read the recorded declarations of all four statement dependencies; each is usable
  directly. No definition node or dependency repair is needed.

No statement dispute or node correction is needed.

## Second reading by Q148

A separate rereading of the node, source and final signature was performed by this
worker; the dispatcher's instruction forbids starting a second agent, and the
maintainer's independent review remains external to this delivery.

This pass checked every row of the two correspondence tables against the signature.
It found and repaired the initial implicit residue-scalar instance: `ResidueField C`
is a type alias whose generic quotient-module action is not synthesized automatically.
The final signature instead explicitly supplies the canonical quotient action with
`Module.compHom` along the specified `eC.symm`, giving a basis over l itself.
It also checked that the quotient-family variables are determined by commuting with
surjective projections, that the section equation is `p ∘ σ = id`, and that the
existentials do not impose compatibility or B-linearity. The complete local
B-algebra conclusion is tied to the unique phi, not an unrelated equivalence.
No clause of the node was dropped and no source-based statement change was required.
