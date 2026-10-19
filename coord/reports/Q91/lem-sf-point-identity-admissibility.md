## Worker report

The module `Sheaf.Paper.PointIdentityAdmissibility` states
`WeilConjectures.point_identity_admissibility`, with its sole proof `sorry`.
The node's natural statement, statement dependencies, proof and proof dependencies
are unchanged. The four other declarations are owning-node helpers permitted by
the missing-helper rule: structures that package this assertion's witnesses,
a predicate spelling out its coefficient equation, and an instance using the
already recorded finite-ring theorem. No data are constructed with `sorry` and
no theorem is proved in this delivery.

Hypotheses and clauses, checked against the node and the source:

- The global tuple is `(D : FiniteFieldDatum.{u})`, importing
  `Sheaf.Paper.FiniteFieldFiber`; this retains `p`, positive `a`, `q = p^a`,
  the finite field of cardinality `q`, its algebraic closure and inclusion.
- `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` retains the coefficient prime and
  its distinctness from the geometric characteristic. It is not replaced by an
  assumption of invertibility. The conclusion supplies `hS`, invertibility in
  every stalk of the point, for the published admissibility predicates.
- `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]` retains the chosen algebraic closure of coefficients.
  Its universe is independent of the geometric universe. The finite extensions
  are quantified as `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Any finite subextension in Ω is included
  through its small field model; the published algebraically closed predicate
  uses exactly `Padic.FiniteCoefficientFields l Ω` and `Shrink`.
  Quantification over field models does not identify the coefficient stages.
- All positive finite levels are indexed by `n : ℕ` with exponent `n+1`, and
  positivity is `Nat.le_add_left 1 n`. Thus this includes every integer exponent
  at least one, without an extra lower bound or omission of the first stage.
  The ring is exactly `Padic.coefficientExtensionRing l E (n+1)`, whose ideal
  is the power of the recorded chosen uniformizer. The small pro-etale categories
  are the dependency's `proEtaleDerivedCategory` of intrinsic constant-ring
  module sheaves, without a replacement category or a point-evaluation shortcut.
- `s` is always `Spec (.of D.k)` and `a_s` is `𝟙 s`. The compactification is
  `Compactification.ofIsProper (𝟙 s)`: its ambient scheme, open immersion and
  proper morphism are respectively `s`, `𝟙 s`, `𝟙 s`. The scheme base is also
  `s`, using the canonical self-over structure. Identity morphisms provide the
  required separated, finite-type, proper and open-immersion instances.
- The existential family `M`, with one `PointIdentityFiniteSystem` at each field,
  gives the actual `SfAmbientExceptionalRightAdjointDatum` at every positive
  exponent. Its `fullCD_zero` is precisely
  `sfFullCohomologicalDimension (𝟙 s) A 0`. This includes BOTH defining clauses:
  all original module sheaves and their pullbacks to every pro-etale site object,
  with no constructibility or finite-type restriction on that object. The
  datum's distinguished compactification has the same identity proper part.
- `preserves_zero` is `ExceptionalAdjointPreserves ... G 0 0`, using the SAME
  right adjoint as the model's datum. Its first clause quantifies over all
  signed integer intervals `a ≤ b` and constructible objects; its second clause
  preserves the published finite-Tor constructible predicate. This gives
  `c_f^- = c_f^+ = 0`, including negative endpoints.
- `PointIdentityAdjunctionModel.leftIso d` identifies the actual ambient
  `sfAmbientCompactSupportCandidate A d` with the identity, and `rightIso d`
  identifies its chosen right adjoint with the identity, for EVERY
  compactification, including the distinguished identity compactification.
  No arbitrary support candidate or arbitrary coefficient-change functor is input.
- `unit_identity` states componentwise
  `η_K ≫ G.map (β_K) ≫ α_K = 𝟙 K`; `counit_identity` states
  `ε_K = F.map (α_K) ≫ β_K`. These are exactly the identity unit and counit
  after transport by `β : F ≅ id` and `α : G ≅ id`, rather than literal equality
  between independently chosen functor models.
- `left_refinement` states `θ_r.hom ≫ β_e.hom = β_d.hom` and
  `right_refinement` states `ρ_r.hom ≫ α_d.hom = α_e.hom` for EVERY refinement.
  The underlying datum already includes both unit/counit compatibility equations,
  identity comparisons and composition comparisons. Consequently the whole
  adjunction datum agrees under the identity identifications, not just its objects.
- `PointIdentityCoefficientComparison φ MA MB` uses the published
  `exceptionalFiniteRightCoefficientMap φ ... MA.datum MB.datum` and the actual
  `exceptionalCoefficientExtension φ s`. It states the component equation
  `T.map (α_A.inv.app K) ≫ γ.app K ≫ α_B.hom.app (T.obj K) = 𝟙 (T.obj K)`.
  Thus it identifies the actual right-adjoint mate with the identity transformation
  of `T`, rather than merely asserting invertibility or supplying another map.
- `reduction_identity` applies that equation to every actual quotient factor map
  for `m ≤ n`, including equal exponents. The scalar clause in the main theorem
  applies the SAME equation to `integralScalarQuotientMap l E L ι n` for all finite
  extensions and algebra embeddings, including the identity embedding, at each
  positive exponent. All comparisons use the models from the SINGLE family `M`.
- The zeros in `fullCD_zero` and `preserves_zero` are outside all field/exponent
  choices: bounds are uniform in both. The remaining conclusion explicitly names
  `IsExceptionalAdjointAdmissibleAtFiniteStage` for every positive stage,
  `IsExceptionalAdjointAdmissibleAtIntegral`,
  `IsExceptionalAdjointAdmissibleAtRational`, and
  `IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed l Ω`. The last three are
  the dependency's finite-system criteria; they retain canonical finite reduction
  and scalar maps, without replacing integral completeness, raw rationalization
  or common-stage algebraically closed coefficients by a naive module category.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imported
  `CoefficientExtension`: `Padic.finite_coefficientExtensionRing`,
  `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionIdeal`.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`:
  `ExceptionalAdjointPreserves`, `exceptionalCoefficientExtension`,
  `exceptionalFiniteRightCoefficientMap`, and all four
  `IsExceptionalAdjointAdmissibleAt*` declarations.
- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`:
  `SfAmbientExceptionalRightAdjointDatum`, `sfAmbientCompactSupportCandidate`,
  including every refinement/adjunction field.
- `Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension`:
  `AlgebraicGeometry.Scheme.sfFullCohomologicalDimension`, both clauses.
- `WeilConjectures.Compactification.Refinement` and its imported `Defs`:
  `Compactification.Refinement`, its category and `Compactification.ofIsProper`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`; and
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.
- `Sheaf.Paper.FiniteCoefficientPoint`: read `pointQbarFibre` and its docstring,
  and the four-stage conventions; retained as a proof-only import. No fibre
  equivalence or point-evaluation equivalence is used to assume ambient admissibility.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`:
  `integralScalarQuotientMap`, already imported by the admissibility interface.

The intrinsic direct-image, derived-image and extension-by-zero modules and the
intrinsic constructible-interval/Tor predicates are already in the public import
closure of the recorded admissibility/ambient modules. Proof-only imports retain
the scheme section lemma (`Mathlib.AlgebraicGeometry.Morphisms.Separated`),
right-adjoint uniqueness (`Mathlib.CategoryTheory.Adjunction.Unique`) and the generic
unbounded right-derived compositor
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`).
The separately recorded `Sheaf.Paper.FiniteDirectImageComposition`,
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`, and fixed-scalar
interval/Tor presentations belong to the legacy fixed-scalar framework; this file
uses the intrinsic interfaces already used by its admissibility dependency.
It does not mix in a second support or constructibility presentation. The proof
plan in the theorem records all eight steps of the DAG, including the clopen-section
argument and the ambient scope of the composition/refinement comparisons.

Edge cases checked: the first level (`n=0` means exponent 1); equal-level reductions;
nonflat reductions such as a square-level quotient onto its residue quotient;
identity scalar embeddings; all signed interval endpoints; zero objects and arbitrary
unbounded complexes; site objects not finite type; arbitrary compactifications such
as `s` disjoint union a proper curve, where no FullCD bound is imposed on that other
compactification's proper part. FullCD is required only for the chosen identity
proper part, and the normalized comparison exists on the whole ambient category.

Searches for duplication (2026-10-17):

- `msearch.py` LeanFinder, query “Identity compactification gives exceptional-adjoint
  admissibility with zero cohomological bounds and identity coefficient comparisons”:
  eight unrelated admissible-simplex results; no matching scheme theorem.
- `msearch.py` Loogle, `CategoryTheory.Adjunction.id`: twelve results, including
  the identity adjunction, its unit/counit and mate identities; none supplies
  exceptional admissibility, FullCD or the compactification/coefficient equations.
- `msearch.py` LeanSearch, “The identity scheme morphism has exceptional adjoint
  identity with zero full cohomological dimension”: eight elementary identity-map
  results, no matching theorem.
- `msearch.py` grep, `identity.*[Aa]dmissib|[Aa]dmissib.*identity|pointIdentity`:
  zero matches. Direct `rg` of both upstream `WeilConjectures` and side `lean/Sheaf`
  for those patterns and the blueprint id found no existing theorem (two unrelated
  comments in the side project). The new declaration names do not occur there.

No statement dispute, correction, new independent definition node or dependency-record
repair is needed. Compilation is through the prescribed `scompile.py`, file only;
no library or global build is requested. The sole new postponed theorem has the
matching item and the complete eight-step natural-language proof in its docstring.

Validation: the final file, including the finite-point and proof-only imports, passed
`scompile.py Q91 lem-sf-point-identity-admissibility` with no errors or warnings.
The server's separate sandbox and module checks took 37.3 s and 9.9 s respectively,
within the unchanged 60 s per-file limit. The node differs from the base only in
`lean`; the recorded signature is verbatim; maximum Lean line length is 94;
there is exactly one explicit `sorry`, for the item's theorem.

## Second reading by Q91

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
