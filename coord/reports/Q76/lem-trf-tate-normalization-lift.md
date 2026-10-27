## Worker report

The new module `lean/Sheaf/RingTheory/TateNormalizationLift.lean` states
`RestrictedSeries.tate_normalization_lift`, with its proof exactly `sorry`.
It introduces no definitions or helper theorems. Only the item's `lean` field changes.
There are no statement corrections, disputed statements, or unusable dependencies.

Source checked: Bosch, Lectures on Formal and Rigid Geometry (April 2008),
Section 1.2, Corollary 10 and its proof, printed p. 14, PDF page 16:
https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf .
The online primary PDF was read with the web tool. It explicitly gives a monomorphism
into the original Tate algebra whose quotient composite is finite and injective.
The induction in the source gives the node's bound on the variable count.
Its additional Krull dimension assertion is outside the assigned node's statement.

Hypotheses and clauses, individually:

- The field is `(K : Type u) [NormedField K]`. `NormedField` extends Mathlib's
  `Field`, the `mathlib_match` of `def-weil-field`; it supplies a real-valued,
  multiplicative, separated norm and its induced metric.
- Nonarchimedeanness is `[IsUltrametricDist K]`; in this setting it is equivalent
  to `IsNonarchimedean (norm : K → ℝ)`. Completeness is `[CompleteSpace K]`.
- Nontriviality of the absolute value is `hK : ∃ a : K, a ≠ 0 ∧ ‖a‖ ≠ 1`.
  This does not require discreteness, dense value group, algebraic closure, or a
  characteristic restriction.
- The variable count is `r : ℕ`. The ring `T_r` is exactly the subtype
  `↥(MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ)))`.
  At these radii Mathlib's weighted coefficient decay is ordinary coefficient
  decay in the cofinite filter. Its ring operations are inherited formal series
  addition and Cauchy multiplication, as in the dependency node.
- `I : Ideal ...` binds an arbitrary ideal of this very ring, and `hI : I ≠ ⊤`
  says it is proper. No primeness, radicality, closedness, or finite generation
  hypothesis is introduced.
- `∃ d : ℕ, d ≤ r ∧ ...` says exactly that there is an integer `0 ≤ d ≤ r`;
  nonnegativity is built into `ℕ`.
- The existential `ι` is a ring homomorphism from the same restricted-series
  construction on `Fin d` into that on `Fin r`. The equality
  `ι.comp (constants K d) = constants K r` says it respects the specified
  constants. A unital ring homomorphism with this equation is precisely a
  `K`-algebra homomorphism for the constants algebra structures; there is no
  arbitrary scalar structure or extra hypothesis in this encoding.
- `Function.Injective ι` states injectivity of the lift into `T_r` itself.
- `Function.Injective ((Ideal.Quotient.mk I).comp ι)` states injectivity of its
  actual composite with the canonical quotient map.
- `((Ideal.Quotient.mk I).comp ι).Finite` states module finiteness for exactly
  that composite. Mathlib's `RingHom.Finite` installs the algebra structure
  obtained from this map and asserts `Module.Finite` for that structure. Thus
  this clause asserts finite generation for the action in the node, rather than
  an independently quantified module structure.
- When `d = 0`, the domain uses `Fin 0`, so its only multi-index is zero.
  Every formal series is constant, every such series is restricted, and the
  constants map identifies this domain canonically with `K`. This encodes the
  node's last sentence without removing the zero-variable case or adding a
  separate normalization condition. See the existing
  `MvPowerSeries.isEmptyEquiv` in `Mathlib.RingTheory.MvPowerSeries.Equiv`.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`: the recorded Mathlib match of
  `def-weil-field`, inherited through `NormedField`.
- `RestrictedSeries.constants`,
  `Sheaf.RingTheory.RestrictedSeriesPresentation`: the recorded dependency
  module and its actual constant-series scalar map. Its full definitions of
  `IsTopologicallyFinitelyPresented`, `IsAffinoidQuotient`, and
  `HasBoundedTopologicallyGeneratedImage` were read; they impose additional
  presentation conditions not needed in this theorem and are not assumed.
- `MvPowerSeries.IsRestricted` and `MvPowerSeries.IsRestricted.subring`,
  `Mathlib.RingTheory.MvPowerSeries.Restricted`, used through the same dependency
  module. Both the coefficient-decay predicate and subring definition were read.
- `Ideal.Quotient.mk`, `Mathlib.RingTheory.Ideal.Quotient.Defs`, and
  `RingHom.Finite`, `Mathlib.RingTheory.Finiteness.Defs`, use the actual quotient
  and actual scalar action. The latter module is already publicly imported by
  the presentation dependency.

Both additional proof dependencies
`lem-per-tate-triangular-distinguished-coordinate` and
`lem-trf-tate-weierstrass-norm-division` have no `lean` or `mathlib_match`
records in the read repository. Their statements were read and are named
in the theorem's step-by-step proof docstring, but have no modules to import.
They are not prerequisites for typing the statement; no missing notion or
replacement interface is needed. The maintainer can add their private proof
imports when those nodes are stated, according to stages/2-statements.md §3.7.

Edge cases checked before drafting:

- `r = 0`: the ring is canonically `K`, and its only proper ideal is zero;
  choose `d = 0` and the identity. The quotient is generated by one.
- `I = 0`, including positive `r`: choose `d = r` and the identity, with the
  canonical quotient isomorphism finite and injective.
- `d = 0` for positive `r`: all source series are constants; the conclusion
  is a finite-dimensional, nonzero quotient over `K` and retains its lift.
- An improper ideal is excluded exactly by `hI`; otherwise the zero quotient
  could not admit the stated injection. Nonreduced proper quotients remain
  included, and no restriction on characteristic is present.
- `u` is arbitrary; all series and quotient types live in the inherited
  coefficient universe, with no extra universe equality imposed.

Searches actually run (2026-10-24):

1. `msearch.py ... leanfinder` with query
   `Noether normalization for Tate algebra quotients lifting to an injective homomorphism into the original restricted series ring`:
   eight hits, including `exists_integral_inj_algHom_of_quotient`,
   `exists_integral_inj_algHom_of_fg`, and `exists_finite_inj_algHom_of_fg`.
   Their signatures concern polynomial algebras, not restricted series;
   none states the assigned theorem or its lift.
2. `msearch.py ... loogle` with query `"NoetherNormalization"`: three hits,
   `NoetherNormalization.varChange`, `NoetherNormalization.T1`, and
   `NoetherNormalization.varChange_leadingCoeff_isUnit`, all polynomial.
3. `msearch.py ... grep` with query `TateAlgebra|[Nn]oether.*[Nn]ormali[sz]`:
   five hits, all in `Mathlib/RingTheory/NoetherNormalization.lean`.
   The normalization signatures in that file were opened and read.
4. `msearch.py ... leansearch` with query
   `Noether normalization for quotients of a Tate algebra by a proper ideal with a lifted injective finite homomorphism`:
   eight hits; polynomial normalization, generic quotient facts, and formal
   smoothness lifts, with no match to this restricted-series theorem.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `RestrictedPowerSeries|RestrictedSeries|tate.*[Nn]ormal|[Nn]ormal.*[Tt]ate`
   located the presentation module and existing analytic consumers. Targeted
   searches for `tate_normalization_lift|normalization.*restricted|normalization.*Tate|Noether.*Tate`
   found no theorem implementing this normalization. An exact node-id search
   for `lem-trf-tate-normalization-lift` in `lean/WeilConjectures` found nothing.
6. Mathlib declaration-source searches found `RingHom.Finite`, the inherited
   normed-field definitions, and `MvPowerSeries.isEmptyEquiv`; these supply the
   standard notions and explain the zero-variable case, without new definitions.

Validation: `scompile.py Q76 lem-trf-tate-normalization-lift` compiled this module
both as its sandbox module and as `Sheaf.RingTheory.TateNormalizationLift`.
Both passed without errors or non-sorry warnings (13.3 s and 4.2 s).
Both auto-implicit options are false, and every universe and binder is explicit.

## Second reading by Q76

The worker reread the source, node, and final signature as a separate self-check;
this is not a claim of an independent agent review. No subagents were started.
The maintainer's independent review remains the delivery review.
The signature binds the complete nontrivially normed nonarchimedean field,
the arbitrary natural variable count, and the proper ideal. It concludes the
bounded natural variable count, the lift, scalar compatibility, injectivity of
the lift, injectivity of the quotient composite, and finiteness of that same
composite. The `Fin 0` case retains the canonical field of constants. The only
postponed proof is the named theorem matching this node, with the induction
spelled out in its docstring. No correction or dependency module was required.
