## Worker report

The module `Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence` defines
`WeilConjectures.compactWeilCocycleEndomorphism`, the explicit composite U_r of
the recorded direct power transport and H of the specified iterated Weil map,
and states `WeilConjectures.compact_weil_cocycle_endomorphism_recurrence`.
The only postponed proof is this named theorem, with `sorry`; its docstring
contains the five steps of the node proof. Definitions have real data.

Hypothesis and clause correspondence:

- The prime p, positive a, q=p^a, finite field k₀ of cardinality q, and its fixed
  algebraic closure k are the fields and laws of `D : FiniteFieldDatum.{u}`.
- The prime ell distinct from p and the chosen algebraic closure of Q_ell are
  `C : D.CoefficientDatum` (including `C.prime` and `C.different`). The finite
  extension inside that closure is `E : Padic.FiniteCoefficientFields C.l C.Qbar`.
  `Coefficient.{u} C.l C.Qbar E` is the existing small model, not a different
  field or an extra condition. Its existing coefficient-extension ring uses
  the valuation ring and uniformizer convention of the dependency.
- Every positive coefficient exponent is represented by `n + 1` with `n : ℕ`.
  The coefficient ring throughout is `Padic.coefficientExtensionRing C.l
  (Coefficient.{u} C.l C.Qbar E) (n + 1)`, namely O_E/varpi_E^(n+1).
- `X₀ : Over (Spec (.of D.k₀))` supplies the model and structure map;
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]` jointly mean finite type,
  and `[IsSeparated X₀.hom]` is the separatedness hypothesis. The geometric
  scheme and a_X are `D.geometricFiber X₀` and its structure map.
- The one retained compactification is `c₀ : Compactification X₀.hom`, passed
  unchanged to every occurrence of `compactPowerCohomology` and
  `compactPowerTransport`. Their implementations use its geometric base change.
- H is the actual functor `compactPowerCohomology D C.l
  (Coefficient.{u} C.l C.Qbar E) X₀ c₀ n`: intrinsic compact-support direct image
  followed by the derived exact point-sections functor. It acts on complexes,
  not cohomology groups. The finite point category's full-subcategory inclusion
  is faithful, so writing the equalities in this ambient derived category is
  exactly equality of the bounded finite-cohomology coefficient-complex maps.
- gamma, g, h, their powers and P_r are the constructions used by
  `compactPowerTransport`: geometric Galois Frobenius, its scheme powers, and
  `compactPowerPullback`. The specified g is also explicitly used in the
  `pointPowerPullbackModel` comparison in the endomorphism helper.
- K is in the recorded strict Weil category for
  `TraceFormulaCoefficientConventions.mk D C E (n+1) (Nat.succ_pos n) X₀`.
  Thus `K.obj.carrier` is bounded constructible finite-Tor and
  `strictWeilFrobenius K` is exactly phi : P_1 K ≅ K. No stability,
  cocycle, naturality, recurrence, or arbitrary map is assumed as input.
- The specified phi^[r] is `iteratedWeilIsomorphism K r hr`. It uses the
  intrinsic pullback presentation, while the direct transport has the recorded
  finite tensor pullback presentation. `pointPowerPullbackModel ... (g^r)`
  identifies those presentations with the existing unit-normalized comparison.
  This is the same canonical identification used by `iteratedWeilPullbackModel`;
  no comparison is chosen or postulated. The composed map is H(phi^[r]) tau^r.
- The helper `compactWeilCocycleEndomorphism ... r hr` defines exactly U_r for
  `hr : 1 ≤ r`. Its return type is `End (H.obj K.obj.carrier)`.
- The first conjunct is the equality U_1 = tau_c followed by H(phi), using
  `frobeniusCompactTransportFinite` for the actual degree-one transport and
  `strictWeilFrobenius` for phi.
- The second conjunct quantifies over every `r : ℕ` with `hr : 1 ≤ r` and states
  `U_(r+1) = U_r ≫ U_1`. Since Lean's `≫` traverses its left arrow first,
  this is precisely the node's `U_(r+1) = U_1 ∘ U_r`.
- Every power uses `compactPowerTransport`, the direct power-square recipe;
  none is defined by repeating the degree-one transport. No homology functor
  occurs in either conjunct. There is no stronger power formula or extra clause.

Dependency declarations read and used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, its constructor,
  coefficient ring, derived pullback and bounded constructible finite-Tor data.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.finiteDerivedPullback`, used by the recorded power pullbacks.
- `WeilConjectures.Compactification.RefinementCategory`:
  the existing `AlgebraicGeometry.Compactification` and refinement category;
  the compactification is the binder c₀. No duplicate notion is introduced.
- `Sheaf.TraceFormula.CompactFrobeniusTransportComposition`:
  `WeilConjectures.compactPowerCohomology`, `compactPowerTransport`,
  `compactPowerPullback`, `compactPowerPullbackStep` and
  `compact_frobenius_transport_composition` (the last two are the proof plan).
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `WeilConjectures.frobeniusCompactTransportFinite` and its base-changed
  compactification, also used by the recorded power transport.
- `Sheaf.Paper.TraceFormulaStrictWeilComplex`:
  `WeilConjectures.TraceFormulaCoefficientConventions.strictWeilComplex` and
  `strictWeilFrobenius`.
- `Sheaf.Paper.IteratedWeilMap`:
  `WeilConjectures.TraceFormulaCoefficientConventions.iteratedWeilIsomorphism`
  and its canonical comparison conventions.
- `Sheaf.Paper.IteratedWeilCocycle`:
  `WeilConjectures.TraceFormulaCoefficientConventions.iterated_weil_cocycle`,
  imported privately as a proof dependency.
- The comparison helper `WeilConjectures.pointPowerPullbackModel` is already
  exposed by the transport-composition module (from
  `Sheaf.TraceFormula.PointTransportComposition`); it is not redefined.

Edge cases checked before writing: n=0 is the first finite coefficient level,
so exponent 1 is included. r=1 gives U_2 = U_1 squared with the correct order
of composition; r=0 is excluded exactly as in the node. K=0 and the empty
scheme give zero compact-support complexes and remain admissible. On a point
with constant free coefficients, the formula becomes B^(r+1)=B B^r for the
Weil automorphism. No extra finite-type, properness, pullback stability or
universe equality hypothesis is imposed. Scheme and coefficient sizes follow
the recorded arbitrary universe u and its existing ULift point-fibre convention.

Searches made for an exact existing statement:

- `msearch.py leanfinder`: "A strict Weil complex and direct compact support
  Frobenius transports induce derived endomorphisms satisfying U r plus one
  equals U one composed with U r". Eight hits: ring Frobenius iteration,
  purely inseparable iteration, and Dold-Kan; no matching assertion.
- `msearch.py loogle`: `"NatTrans", "iterate"`; zero hits.
- `msearch.py grep`: `compact.*[Ff]robenius|[Ww]eil.*[Cc]ocycle`; zero Mathlib hits.
- `msearch.py leansearch`: "Naturality of compact support transport and the Weil
  cocycle give a recurrence on derived coefficient endomorphisms". Eight hits
  about analytic compact support, group cohomology and comonad transport;
  no matching assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for compact recurrence,
  cocycle endomorphism and the exact node id found no matching declaration.
  The parent `frobenius_operator_compact_description` has a different statement
  (a power formula, identification with repeated transport, and invertibility).
  Its docstring paragraph (4) supplies this node's proof calculation, not an
  existing theorem of the recurrence. It is not imported, avoiding the parent
  proof-dependency cycle.
- The proposed declaration names were searched in Mathlib, WeilConjectures
  and Sheaf; neither already exists.

Read the node, all eight statement-dependency records and their applicable
signatures/docstrings, the source blueprint proof, and the parent Lean docstring.
The live L/Q142 passing review is stage 1, not a stage-2 Lean attachment.
The earlier worker's stage-1 live-wins concern does not prevent this statement.
No statement correction, disputed statement, new node or dependency repair is
needed. The sandbox node changes only `lean`.

Validation: prescribed `scompile.py` passed both the sandbox and the actual
library module, with no errors or unexpected warnings (30.1 s and 41.9 s).

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
