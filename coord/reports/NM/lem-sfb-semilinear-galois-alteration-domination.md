## Worker report

The module states `AlgebraicGeometry.exists_semilinear_galois_alteration_domination`, with
one theorem and one `sorry`. It defines no objects or helper predicates. The live node's
statement, fifteen reviewed proof steps, proof dependencies and review are preserved.
The previous attempt confused a completed stage-1 split with completion of stage 2;
the live node had neither `lean` nor `reviewed_lean`. No split is changed here.

Source read: all fifteen live proof steps; de Jong, Families of curves and alterations,
https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, Sections 2.10 and 3.2 (p.605),
3.8 (p.608), and Situation 5.3 (p.613). Section 3.2 explicitly retains the original
possibly nonfaithful group via a fibre product, 3.8 dominates by a normal equivariant
modification, and 5.3 specifies the surjection and purely inseparable invariants.
The full node proof, including its inseparable extension of this construction, is in
the declaration docstring. No change of the mathematical statement is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| k a field | `(k : Type u) [Field k]` |
| S integral | `(S : Scheme.{u}) [IsIntegral S]` |
| S normal | `hnormal`, requiring domain and integrally closed structure-sheaf stalks at every point |
| S projective finite type over k | `pS : S ⟶ Spec (.of k)`, `IsHProjective pS`, `LocallyOfFiniteType pS`, `QuasiCompact pS` |
| H finite group | `(H : Type v) [Group H] [Finite H]` |
| actions on S and k compatible | `σS : H →* Aut S`, `σk : H →* (k ≃+* k)`, and `hsemilinear`; the inverse in Spec is necessary for contravariance |
| r:T→S an alteration, T integral | `[IsIntegral T]`, `r`, `[IsProper r]`, `[Surjective r]`, and `hrfinite`, finite over a dense open |
| finite J and surjection ρ:J→H | existential `J : Type (max u v)`, `Group J`, `Finite J`, `ρ : J →* H`, `Function.Surjective ρ` |
| W normal integral projective finite type over k | existential `W`, `IsIntegral W`, `pW`, and the explicit stalk, H-projectivity and finite-type clauses |
| semilinear J action on W through ρ | `σW : J →* Aut W` and the displayed scalar compatibility for every j |
| b equivariant over S and k | `b ≫ pS = pW` and `(σW j).hom ≫ b = b ≫ (σS (ρ j)).hom` |
| b H-projective alteration | `IsHProjective b`, `IsProper b`, existential instance `Surjective b`, and finiteness over a dense open |
| t an S-morphism W→T, rt=b | `t : W ⟶ T` and `t ≫ r = b`; with T's induced k-structure, this also implies t is over k |
| k(W)/k(S) the actual function-field extension | algebra A with `A = b.dominantFunctionFieldAlgebra`; this rules out an arbitrary field embedding |
| k(W)/k(S) finite | `Module.Finite S.functionField W.functionField` |
| N=ker ρ and k(W)^N | `K : IntermediateField S.functionField W.functionField` with membership iff every `j : ρ.ker` fixes z via `Scheme.functionFieldAut (σW j.val)` |
| k(W)^N/k(S) finite purely inseparable | `Module.Finite S.functionField K ∧ IsPurelyInseparable S.functionField K` |
| separable input permits separable W and fixed field equal k(S) | implication whose premise is `@Algebra.IsSeparable ... r.dominantFunctionFieldAlgebra` and conclusion is `Algebra.IsSeparable S.functionField W.functionField ∧ K = ⊥` |
| no action on T required | the input contains no action on T and the conclusion imposes none |

The separable branch is an implication inside the same existential witness. This says
exactly that a separable choice can be made when the input is separable: when it is not,
the implication is vacuous, leaving the general existence assertion. It adds no
separability hypothesis to the main theorem. In the output algebra, bottom is precisely
the image of k(S), so `K = ⊥` is the claimed equality of embedded fields.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (the def-weil-field Mathlib leaf).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (with separated and universally
  closed parents); properness also supplies finite type/quasi-compactness.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; together with
  `QuasiCompact` this is exactly finite type.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral` and its
  public imported geometric-property classes. This dependency supplies vocabulary
  mentioned in the node's explanatory paragraph; no geometric-integrality hypothesis is added.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, the actual
  closed finite-projective-space embedding convention, unrelated to the group name H.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; `IsIntegralHom` belongs to
  the same recorded dependency but is not needed in the signature.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded component-product
  definition; its integral clause explicitly reuses `Scheme.functionField` from Mathlib,
  the generic stalk. The signature uses precisely that integral clause.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra` and `algebraMap`.
- `Sheaf.FieldTheory.FieldTower`: the module documents its finite, separable and purely
  inseparable clauses as existing `Module.Finite`, `Algebra.IsSeparable` and
  `IsPurelyInseparable`, respectively. These existing definitions are used directly.
- `Sheaf.TraceFormula.LocalDimensionFormula`:
  `AlgebraicGeometry.Scheme.Hom.dominantFunctionFieldAlgebra`, the recorded declaration of
  the already landed `def-sfb-dominant-function-field-map`. Its full body was read: it
  proves the generic-point equality from dominance, takes `functionFieldMap`, then
  `RingHom.toAlgebra`. This existing definition node is added to stmt_deps.
- `WeilConjectures.AlgebraicGeometry.StalkAut`: `Scheme.functionFieldAut`, whose body is
  the automorphism of the generic stalk. Fixed elements for direct pullbacks are exactly
  the fixed elements for inverse pullbacks, so no new group-action helper is needed.

The input and output alteration conditions are written using their constituent recorded
notions, with no duplicate definition. The general `Orgogozo.IsAlteration` found in
`Sheaf.Paper.OrgogozoInductionData` also covers reducible schemes and has a component
dominance clause; here both schemes are integral and surjectivity gives that clause.
The dense-open finiteness is stated by `IsFinite (r ∣_ U)`, as in landed sibling modules.

All recorded project proof-dependency modules that have Lean declarations are imported
privately, except the retired duplicate `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`:
the public canonical upstream projectivity module already supplies its exact instance
`IsHProjective.isProper`. Public statement imports and private proof imports were tested
together in module mode. No import cycle or duplicate-declaration failure occurred.

Edge cases checked: the empty S or T is excluded by integrality, not by an extra
hypothesis; dimensions zero and higher are unrestricted; identity alterations and the
trivial group are included; neither action is required to be faithful; no action on T
is required; characteristic zero and positive characteristic both use Mathlib's
`IsPurelyInseparable`; separability is conditional only. The group may live in any
universe v and the enlarged group in max u v, allowing pairs with field automorphisms
without forcing H into the field's universe. No finite group is excluded by this size
choice. The algebra A is uniquely specified, not an arbitrary choice.

Searches actually run:

- msearch leanfinder: "A semilinear finite group action on a normal projective scheme
  admits a normal projective Galois alteration dominating any alteration": eight hits,
  abstract Galois category and Galois fraction-ring results, no matching scheme theorem.
- msearch loogle: "AlgebraicGeometry.IsAlteration, AlgebraicGeometry.IsHProjective,
  FixedPoints.intermediateField": zero hits, unknown identifier IsAlteration.
- msearch grep: "IsAlteration|galois.*dominat|semilinear.*alteration", AlgebraicGeometry:
  zero Mathlib hits.
- msearch leansearch: "A normal projective scheme with a finite semilinear group action
  has a Galois alteration dominating any integral alteration": eight constituent
  fixed-field/Galois and normalization hits, no match for this theorem.
- Project rg for `IsAlteration`, `functionFieldMap`, `functionFieldAut`, and
  `dominantFunctionFieldAlgebra`: found the general Orgogozo predicate, the canonical
  field-map algebra in LocalDimensionFormula, the map in Curve.DivisorPullback and
  generic-stalk automorphisms in StalkAut. No semilinear domination theorem found.
- Project rg for this exact blueprint id: only its use in the proof docstring of
  EquivariantSingleCurveNodalReduction, no declaration stating it.
- DAG search found `def-sfb-dominant-function-field-map`, whose existing record is used.

Validation: prescribed scompile.py compiled the file in both sandbox and library
module modes, cleanly (3.0 s and 3.1 s), with no errors or warnings.

## Second reading by NM

A separate source-to-signature rereading was performed by this worker; no other agent
was started, as the dispatch brief explicitly prohibits it. The maintainer supplies
the independent review. I checked the field-algebra equality, the kernel fixed-field
membership equivalence and bottom-field equality against the node, rather than only
checking compilation. I also checked that the t-map has no equivariance assumption,
that the scalar action uses ρ followed by the original k-action, and that normality is
on all local rings. No hypothesis or conclusion was changed in this rereading.
There are no new definition nodes, dependency repairs or statement corrections.
