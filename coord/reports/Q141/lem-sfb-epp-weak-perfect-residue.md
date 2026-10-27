## Worker report

Delivered module: `Sheaf.RingTheory.EppWeakPerfectResidue`.
Declaration: `IsDiscreteValuationRing.exists_epp_weak_perfect_residue`.
This is a statement only, with its one proof `sorry`; there are no new definitions,
auxiliary postponed theorems, new DAG nodes, dependency repairs or statement corrections.
The original natural-language node and its dependencies are unchanged.

Source read: `literature/stacks-project/more-algebra.tex`, the entire theorem and proof
of `theorem-epp` (Tag 09F9), `definition-solution`, and the statement and relevant proof
of `proposition-epp-essentially-finite-type` (Tag 09II). The perfect-residue specialization
is the node's statement, not the stronger essentially-finite-type/stable theorem.
The module docstring carries the six steps of the node's proof and names every input.

Clause-by-clause correspondence:

- A and B are arbitrary commutative DVR domains: the explicit `CommRing`, `IsDomain`
  and `IsDiscreteValuationRing` binders on each. These use Mathlib's non-field DVR class.
- The injective local map is `algebraMap A B`, with `hinj : Function.Injective ...`
  and `[IsLocalHom (algebraMap A B)]`. Mathlib localness reflects units; for local rings
  it is equivalent to contraction of the maximal ideal being the maximal ideal.
- K and L are fraction fields: `[Field K] [Algebra A K] [IsFractionRing A K]` and the
  corresponding binders for B and L. `[Algebra A L] [Algebra K L]` and the two
  `IsScalarTower` binders express compatibility with the specified inclusion A -> B.
  They describe the induced fraction-field map, adding no finiteness or separability.
- The lower residue field is `IsLocalRing.ResidueField A`, the actual quotient by
  its maximal ideal. `[PerfectField ...]` means perfect in all characteristics;
  Mathlib includes characteristic zero and the surjective-Frobenius characterization
  in positive characteristic.
- Finite generation of B's residue as a field is
  `(top : IntermediateField (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField B)).FG`, spelled with `⊤` in the Lean source.
  The residue algebra is Mathlib's canonical quotient algebra for the local map.
  The definition of `IntermediateField.FG` asks for a finite set whose field adjoin
  is the whole field. It imposes no finite-dimensionality on this residue extension.
- The conclusion existentially supplies a field N and `Algebra K N`, with
  `Module.Finite K N`. This is exactly finite-dimensionality over K. The accompanying
  `Algebra A N` and tower are existential data, allowing the induced composite
  algebra; no extra assumption on the input is imposed.
- `R_N` is literally `integralClosure A N`; `C_N` is literally
  `integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N))`. The quotient is by all
  nilpotents, so inseparable tensor products and multiple factors are included.
- The normalization homomorphism is constructed inline: second-factor
  `Algebra.TensorProduct.includeRight`, composition with `Ideal.Quotient.mkₐ K`,
  `restrictScalars A`, composition with `(integralClosure A N).val`, and
  `codRestrict` to the integral closure over B. Membership follows from the input's
  integrality using `IsIntegral.map` and `IsIntegral.tower_top`. These are actual
  Mathlib proofs inside a map construction, not a new theorem or postponed data.
  The lambda `fun f => ...` is applied to precisely that constructed map; it only
  binds repeated occurrences and beta-reduces. There is no arbitrary map parameter,
  choice, `let`, hidden `have`, private definition or duplicate named construction.
- Every maximal upper ideal is quantified as `(q : Ideal C_N) [q.IsMaximal]`.
  Its contraction is `q.comap f` and the first conjunct asserts it is maximal.
- The next two conjuncts existentially provide `IsDomain` of the actual localizations
  `Localization.AtPrime (q.comap f)` and `Localization.AtPrime q` together with
  `@IsDiscreteValuationRing ... _ hdom`. Existential domain evidence is needed
  because Mathlib's DVR predicate takes its domain evidence as an explicit parameter.
  Primality of the contraction is already available by comap from q's primality.
- The final equality extends `q.comap f` along the composite `R_N -> C_N -> (C_N)_q`
  using `Ideal.map`, and equates it with q extended along `C_N -> (C_N)_q`.
  This is exactly `n(C_N)_q = q(C_N)_q`, including the same canonical map.
- There is no completeness, essential finite type, separability of N/K, or
  persistence after further extensions hypothesis or conclusion.

Recorded statement dependencies used, with their source signatures/docstrings read:

- `def-sc-discrete-valuation-ring`: Mathlib `IsDiscreteValuationRing`, module
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (class extending local PID,
  with maximal ideal nonzero). Its `mathlib_match` is the dependency declaration.
- `def-pc-field-extension`: `Algebra`, module `Mathlib.Algebra.Algebra.Defs`.
  With Field binders this is exactly a field extension. Fraction fields use
  `IsFractionRing` from `Mathlib.RingTheory.Localization.FractionRing`.
- `def-weil-pbc-integral-closure`: `integralClosure`, module
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, with carrier `IsIntegral`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, module
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with algebra and quotient support
  from `Mathlib.RingTheory.TensorProduct.Quotient`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`, module
  `Mathlib.RingTheory.Localization.AtPrime.Basic`.
  The local residue quotient and its canonical algebra are supplied by
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`.

Additional standard Mathlib notions used are `PerfectField` from
`Mathlib.FieldTheory.Perfect`, `IntermediateField.FG` from
`Mathlib.FieldTheory.IntermediateField.Adjoin.Defs`, `Module.Finite` from the
finiteness API, and ideal map/comap and nilradical quotient operations.
The recorded proof dependency
`AlgebraicGeometry.Scheme.dvr_uniformizer_root_algebra` is imported privately from
`WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra`.
The unit-times-uniformizer-power proof dependency is already in the public DVR import;
the integral-closure proof dependency is already imported publicly for the statement.
The other six non-Mathlib proof nodes have no Lean binding in the read DAG, so there
is no module to import for them yet: `lem-sfb-dvr-algebraic-normalization-structure`,
`lem-sfb-abhyankar-arbitrary-dvr-branches`,
`lem-sfb-finitely-generated-residue-perfect-core`,
`lem-sfb-epp-strict-complete-reduction`,
`lem-sfb-epp-compatible-coefficient-dvrs`, and `lem-sfb-epp-finite-coefficient-triple`.
They are only proof prerequisites, not missing notions needed by this statement.

Edge cases checked before writing:

- A = B and K = L allow N = K and equality of the unchanged maximal ideals.
- An identity/degree-one extension is not excluded: `Module.Finite` has no degree bound.
- Residue characteristic zero, equal characteristic p and mixed characteristic all
  typecheck in the same statement. No positive-characteristic parameter is required.
- Transcendental finitely generated residue extensions, such as k(t)/k, are permitted:
  the hypothesis uses field adjoin, not finite type as an algebra or module finiteness.
- N/K can be inseparable; no reducedness assumption is made before quotienting.
  Multiple tensor factors and all their maximal ideals remain in the conclusion.
- Input types use independent universes u,v,w,x; the finite witness is in their maximum.
  Finite extensions admit a representative there. There is no test-algebra universe
  whose size could make a universally quantified hypothesis vacuous.
- Field rings are not accidentally allowed as DVRs, because Mathlib's class excludes them.
- The ideal equality uses the upper localization, not the lower localization or an
  unlocalized ideal equality, and the lower DVR clause is present separately.

Searches for existing statements and constructions:

- `msearch.py`, leanfinder: "Epp elimination of ramification for local maps of discrete
  valuation rings with perfect residue field". Eight hits, led by
  `Algebra.FormallyUnramified.of_map_maximalIdeal` and its converse, ramification-index
  localization and residue-field unramifiedness. None constructs an eliminating field.
- `msearch.py`, loogle: `IsDiscreteValuationRing, Ideal.ramificationIdx`.
  Successful search, zero hits.
- `msearch.py`, grep: `Epp|eliminat.*ramification|weak.*solution`, subdirectory RingTheory.
  Four false-positive `ePp` hits in Smooth/Fiber and Flat/Equalizer; no Epp theorem.
- `msearch.py`, leansearch: "A finite extension of the lower fraction field eliminates
  ramification for a local inclusion of DVRs with perfect residue field and finitely
  generated residue extension". Eight hits on ramification degree bounds, inertia,
  integral-closure fraction fields and unramified residues. No matching existence theorem.
- `rg` over project `lean/Sheaf` and `lean/WeilConjectures` for Epp/epp,
  elimination of ramification and weak solutions, and exact declaration/module names.
  The existing `Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits` has a DIFFERENT theorem:
  complete lower DVR, essential finite type, and stability for every further finite
  extension. It cannot be recorded as this node's declaration.
- `rg` and `grep -rn` for the exact node id in `lean/WeilConjectures`: no declaration.
  Exact new name lookup in project sources and `dag/lean_names_upstream.json`: absent.
- Inspected `eppReducedTensor`, `eppUpperClosure`, and `eppNormalizationMap` in the
  downstream EppEssentiallyFiniteTypeTraits module. Reused the underlying Mathlib
  objects directly; no new copy of any of those named definitions is made.
  Importing that module would prevent the downstream theorem from importing its
  proof prerequisite here. The inline canonical restriction avoids that import cycle.

Validation: `scompile.py Q141 lem-sfb-epp-weak-perfect-residue` compiled both sandbox
and library module modes successfully (4.4 seconds and 2.1 seconds respectively), with
no errors or warnings. All universes and variables are explicit; maximum line width 99.
There is exactly one `sorry`, the assigned theorem. No disputed statement or node fault.
Independent review is the maintainer's, as the dispatcher brief specifies; no subagent
was started and no second-reader authorship is claimed.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
