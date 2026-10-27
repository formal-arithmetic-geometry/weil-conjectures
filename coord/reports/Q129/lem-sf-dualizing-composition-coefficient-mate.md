## Worker report

The module `Sheaf.Paper.DualizingCompositionCoefficientMate` states the normalized
composition mate at all four coefficient stages and the coefficient equation.
Its only postponed proofs are `WeilConjectures.dualizingComposition_normalized`
and `WeilConjectures.dualizingComposition_coefficient`. Every definition has real
data. No statement, dependency, proof plan, or other node field changes.

Hypotheses and clauses:

- The primes p, ell, positive exponent a, q = p^a, k0 and its algebraic closure k
  are the fields of `D : FiniteFieldDatum` and `C : D.CoefficientDatum`; `C.different`
  records ell != p. `E`, its field and Padic-algebra instances, and
  `[FiniteDimensional (Padic C.l) E]` are explicit binders. The actual integral ring,
  uniformizer and level n quotient are the existing Padic constructions in the
  datum. `n` and `hn : 1 ≤ n` include exactly the positive finite levels.
- `S : SixFunctorDatum D C E n hn` is the recorded six-functor datum. Its
  `finiteCoherence`, `integralCoherence`, `rationalCoherence`, and `commonCoherence`
  use the exact finite-Tor predicates, completed integral operations, rationalized
  operations, and common-stage operations. The main theorem asserts the four
  clauses together; no coefficient stage is dropped.
- `X Y : SixFunctorSpace D` are the recorded finite-type schemes over k.
  `IsSeparated X.obj.hom` and `IsSeparated Y.obj.hom` impose separatedness over k.
  The binders on `f` are `IsSeparated f.hom.left`, `LocallyOfFiniteType f.hom.left`,
  and `QuasiCompact f.hom.left`. They spell out separated finite type.
- The point s is `sixFunctorPoint D`; a_Y is `sixFunctorStructure Y`;
  a_X is literally `f ≫ sixFunctorStructure Y`, the composite named in the node.
  Compactifications cf, cg, cfg merely choose presentations already required by
  the supplied operations. They quantify over every presentation.
- `dualizingCompositionExceptional` restricts S.exceptional using exactly
  `SixFunctorCoherentStage.exceptionalDomain` and `ObjectProperty.lift`.
  Thus the categories in the uniqueness assertion are full finite-Tor categories.
- `dualizingCompositionMate` restricts the inverse of the already recorded
  `sixFunctorExceptionalComposition`. That definition is the unique right-adjoint
  comparison of the pasted A1 adjunction with the A4 compositor, not a freely
  chosen isomorphism. Restriction constructs a genuine natural isomorphism,
  including its inverse, by `NatIso.ofComponents` and `ObjectProperty.isoMk`.
- `DualizingCompositionHomFormula` quantifies over every K, L and morphism t.
  The left side is postcomposition by c. The right side first uses the inverse
  Hom bijections for f and a_Y, then precomposes by
  `(S.composition f g cf cg cfg).hom.app K.obj`, then applies the Hom bijection
  for a_X. This is exactly the node's displayed Hom chain, in its stated direction.
- `DualizingCompositionNormalized` asserts that the concrete mate has this formula
  and that every natural isomorphism having the formula equals it. Existence is
  the real construction; uniqueness is an explicit quantified conclusion.
  The inverse component of `sixFunctorExceptionalComposition` at the coefficient
  unit, explicitly constructed as `dualizingCompositionUnitIso`, is the
  isomorphism f^! omega_Y -> omega_X: the dependency's
  `SixFunctorDualityData.dualizing` is by definition exceptional image of that unit.
- The coefficient theorem uses `SixFunctorCoefficientComparison S S' T`, precisely
  the existing A5 interface. Its `supportAdjunction` fields are the prescribed
  adjunction comparisons, including both the unit and counit equations, and its
  `composition` field is the compositor compatibility. Its stage parameters allow
  insertion of the finite/integral, rationalization, finite-field scalar-transition,
  and common-stage comparisons already supplied by the datum. The assertion is
  conditional on that supplied comparison; it constructs no comparison between
  coefficient stages where none is defined.
- `one`, `one'`, and `unit : (T s).obj one ≅ one'` render the specified coefficient
  units and their comparison. The formal equation is natural in this supplied
  isomorphism; no identification of objects by an arbitrary equality is used.
- `dualizingCompositionKappa A a ca unit` is exactly beta_a at one followed by
  exceptional inverse image of unit. The coefficient theorem's left side is
  `T_X(c_f) ≫ kappa_X.hom`; its right side is `beta_f ≫ f'^!(kappa_Y) ≫ c'_f`.
  Lean composes from left to right, giving exactly the displayed node equality.
  This equality is written after the faithful full-category inclusion; morphisms
  in the finite-Tor full subcategory are the same ambient morphisms.
- No exceptional adjoint on an ambient unbounded derived category is introduced.
  Only the recorded bounded constructible stages and their finite-Tor restrictions
  occur. The proof plans use A1, A4, A5; they never invoke A6 or biduality.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public imports:
  the coefficient-extension ring, integral ring and chosen uniformizer; positive
  level finiteness remains the dependency's `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  `SixFunctorCoherentStage`, `sixFunctorExceptionalComposition`.
- `Sheaf.Paper.SixFunctorOperationDatumStages`, publicly imported by that datum:
  `SixFunctorSpace`, `sixFunctorPoint`, `sixFunctorStructure`, `SixFunctorPushStage`,
  `SixFunctorDualityData.dualizing`, `SixFunctorCoefficientComparison`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and `Sheaf.Paper.FiniteTorAmplitude`:
  `finiteTorConstructible`, `finiteTorConstructibleIntegral`,
  `finiteTorFieldCoefficientCategory`, used via the datum's actual predicates.
- `Sheaf.Paper.SixFunctorDualNotation`: the recorded coefficient-dual notation;
  its module explicitly identifies the dualizing notation with the operation
  datum's dualizing objects. No second dualizing object is defined here.
- The scheme-morphism-properties dependency is a convention node: its recorded
  declarations are Mathlib `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
- Mathlib `CategoryTheory.Adjunction.comp`, `conjugateEquiv`, `conjugateIsoEquiv`,
  `mateEquiv`, `mateEquiv_hcomp`, `mateEquiv_conjugateEquiv_vcomp`, and
  `conjugateEquiv_mateEquiv_vcomp` are the proof-dependency records. Their defining
  modules are imported; the theorem docstrings give the step-by-step proof plan.

Edge cases checked: identity f and the identity coefficient comparison have the
same Hom normalization; the empty scheme and zero objects are retained since no
nonempty or nonzero hypothesis occurs. Level n=1 is allowed. All four coefficient
stages occur, and no reduction from field coefficients to finite coefficients is
asserted. The comparison T is not required to be faithful or an equivalence; only
its recorded A5 adjunction and compositor compatibilities are used. Object and
morphism universes v,w and v',w' of the two coefficient stages are independent.

Searches made:

- LeanFinder: “The composition isomorphism of exceptional inverse image with a
  dualizing complex is the adjunction mate of compact support composition and
  commutes with coefficient change”. Eight generic sheaf-adjunction hits, none
  the full constructible dualizing statement.
- Loogle: `Adjunction.rightAdjointUniq, conjugateIsoEquiv`. Zero hits because the
  service did not recognize the first identifier. Direct Mathlib source search
  below resolved the ingredients; this service response is not a blocker.
- Mathlib grep: `rightAdjointUniq|conjugateIsoEquiv` in CategoryTheory/Adjunction.
  Fourteen hits in CompositionIso, Unique, Mates, Opposites and Triple. Read the
  signatures and definitions of the conjugation, uniqueness, and composition APIs.
  They supply ingredients, not this node's normalization and coefficient equation.
- LeanSearch: “Exceptional inverse image composition mate on constructible finite
  Tor categories commutes with allowed coefficient comparisons and the coefficient
  unit”. Eight hits, including mateEquiv and module pseudofunctor formulas; no full
  match.
- rg of WeilConjectures for the exact node ID: no hits. Concept search
  `dualizing.*composition|composition.*dualizing` found the smooth purity
  multiplicativity result, which concerns smooth maps and omits this coefficient
  normalization. rg of Sheaf found the existing stage comparison and adjunction
  definitions used above, but no theorem for the entire statement. Exact-name
  searches in Mathlib, WeilConjectures and Sheaf found no declaration collision.

Validation: the module was compiled using scompile.py against the live published
server build, without errors or warnings. The first compile diagnostics were
repaired by explicitly supplying the ObjectProperty to isoMk/hom_ext and applying
Hom equivalences to their objects before taking the inverse. No statement
correction, new node, or dependency repair was required.

The preserved sandbox contained only launcher brief markers, no previous delivery.
The earlier worker reported a gate refusal based on the stage-1 review. The live
item indeed has a stage-1 review, no Lean record, and no repair note; this delivery
adds only its missing stage-2 Lean record. It does not alter review metadata or
invent a repair note. The prescribed dry run determines whether that previous
refusal persists for a stage-2 packet.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
