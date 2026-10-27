## Worker report

The item is stated by `AlgebraicGeometry.TorusEulerCharacter.torus_coherent_fixed_point_formula`
in `Sheaf.AlgebraicGeometry.TorusCoherentFixedPointFormula`. Its only postponed proof is
that theorem, with all six DAG proof steps reproduced in its docstring. The auxiliary
module `Sheaf.AlgebraicGeometry.TorusEulerCharacterData` contains real definitions and
operation predicates only. No statement correction, disputed statement, or dependency
repair is needed.

Hypothesis and clause correspondence:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- `H : ProperPushforwardData.Group F` is precisely an affine finite-type group scheme:
  its fields are the scheme over Spec F, `GrpObj`, `IsAffine`, `LocallyOfFiniteType`
  and `QuasiCompact`.
- `T : ClosedSubgroup F H` retains the actual closed immersion and `IsMonHom`.
  `r : ℕ` and `hsplit` give an isomorphism of group schemes with the existing
  `MultiplicativeType.splitTorus F r`, including rank zero.
- `Z : Space F H` retains the actual algebraic action `ModObj`.
  `[Smooth Z.scheme.hom] [IsProjective Z.scheme.hom]` are the recorded smoothness
  and projectivity notions. No connectedness, equidimensionality or characteristic
  hypothesis is added.
- `P`, the closed inclusion `i`, and `hP : Nonempty (IsColimit (Cofan.mk P p))`
  say P is the finite disjoint union of n copies of Spec F as an F-scheme. The
  indexing type is `Fin n`, with no `Nonempty` constraint. A finite union can always
  be enumerated this way, independently of the field/scheme universe.
- `hfixed` identifies the subfunctor represented by P with fixed points after EVERY
  F-algebra extension `A ⟶ B`. It uses the actual H-action composed with `T.map`.
  Closed immersion ensures uniqueness of lifts; hence the existence condition is
  representability of the fixed subfunctor, not a statement about rational points only.
- `D : ActionGroupoidModel H.scheme Z.scheme` and `E : Coherent D` use the shared
  coherent groupoid-module linearization. Its composition is required on every test
  scheme to be the given group multiplication. `hE` says the underlying sheaf is
  locally free. Since smooth projective schemes over a field are Noetherian and E
  is coherent, this is exactly locally finite free, including rank zero. Conversely
  every vector bundle here is coherent and carries this standard sheaf linearization.
  This is the usual equivalent encoding of the linear total-space action in the node.
- For EVERY finite-dimensional rational T-module V, the first conjunction asserts
  `DirectSum.IsInternal (weightSpace ... V)` and finiteness of the nonzero-weight
  support. `RationalModule.finite` supplies finite dimensionality. `weightSpace`
  is the linear equalizer `c(v) = v ⊗ χ`, using the actual universal coordinate of χ.
  Internal direct sum includes existence AND uniqueness of finite weight expansions.
- The conclusion supplies `R : RestrictedSpace F T Z`, DT and ET with
  `ProperPushforwardData.IsRestriction F R E DT ET`. This retains the same sheaf
  and specifies the subgroup-restricted linearization using normalized pullback
  compositors; there is no independent arbitrary T-action.
- `V : ℕ → Representation F H.scheme` and
  `IsCohomologyRepresentation H Z E q (V q)` specify the rational H-action on
  cohomology. Each V is associated to a coherent point sheaf whose underlying
  object is the EXISTING Zariski higher direct image of E. Its action satisfies
  `IsHigherPushforward`, including the canonical base-change exchanges in every
  degree; this prevents choosing an unrelated representation of the same dimension.
  The predicate also records the isomorphism with `cohomologyVector`, the existing
  Zariski `Scheme.Modules.H`. Representations are determined up to equivariant
  isomorphism by the associated-bundle and canonical-image conditions; characters
  are insensitive to that presentation. The vector-space isomorphism only records
  the usual identification with H^q; it does not define the action.
- `W q` is the actual restricted representation, specified coefficient by coefficient
  by `IsRestrictedRepresentation T (V q) (W q)`. Counit and coassociativity are
  fields of both rational modules. `∀ q, b < q → Subsingleton (V q).space` is
  eventual vanishing. Together with rational-module finiteness this yields the
  finite alternating cohomology sum through b.
- `IsFixedFibrePair ... (p j ≫ i) (B j) (N j)` uses the existing equivariant ideal
  of the point and its equivariant pullback, as well as the equivariant pullback of
  ET. The first associated rational module is E|p; the second is I_p tensor k =
  m_p/m_p². The ideal's induced forward linearization is the dual derivative
  action on functions, so this is the COTANGENT representation in the question.
  The existential `IsModHom` is a conclusion forced by fixedness, not an added
  input assumption. Both pullbacks use the shared `IsPullback`, and the point
  representation uses the shared `IsAssociated`, with their normalized formulas.
- `weightSpace ... (N j) 0 = ⊥` says no cotangent weight is zero.
- `Character` and `CharacterRing` are reused from `TrivialTorusCoherentData`:
  the former is Additive of group-scheme homomorphisms to G_m, and the latter is
  `AddMonoidAlgebra ℤ`, so its multiplication is e^χ e^ψ = e^(χ+ψ).
  `formalCharacter` sums the INTEGER `Module.finrank` of the actual weight spaces.
  Its `finsum` is finite by the first conclusion, rather than by a new hypothesis.
- `eulerSystem` is the submonoid generated by all `1 - single χ 1`, χ nonzero;
  `LocalizedRing` is the actual Mathlib `Localization` at that submonoid.
  `eulerFactor N` multiplies `(1-e^χ)^(dim N_χ)` over characters, which is precisely
  the product over weights counted with multiplicity. It includes χ=0 with
  exponent zero, so its contribution is 1. Finiteness and the asserted absence
  of zero weights make this denominator a unit in the localization. `Ring.inverse`
  is therefore its unit inverse; it is not a fraction-field operation.
- The final equality is in that localization. Its left side is the finite alternating
  sum of the restricted cohomology characters; its right side is the sum over the
  fixed points of fibre character times inverse cotangent Euler factor. Every
  coefficient lies in ℤ, with no map to F and no reduction in characteristic p.

Dependency declarations read and used:

- Mathlib: `Field`, `IsAlgClosed`, `Scheme`, `GrpObj`, `Smooth`; read their full
  declarations and docstrings in Algebra/Field/Defs, FieldTheory/IsAlgClosed/Basic,
  AlgebraicGeometry/Scheme, CategoryTheory/Monoidal/Grp and Morphisms/Smooth.
  The algebraic-closure leaf explicitly lists `IsAlgClosed` as the relevant clause.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective`,
  `IsHProjective`, `IsHProjective.isProper`; read the projectivity convention node
  referenced by def-pc-morphism-conventions, and its full source. ProjectiveSpace
  is imported for the recorded projective-proper proof input.
- `Sheaf.AlgebraicGeometry.TrivialTorusCoherentData`: `Character`, `CharacterRing`,
  `characterValue`; `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `splitTorus`.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGZero`: `ActionGroupoidModel`,
  `Coherent`, `underlying`, `IsPullback`, `IsIdeal`, with the normalized maps they use.
- `Sheaf.AlgebraicGeometry.RationalRepresentationGZero`: `Representation`,
  `RationalModule`, `IsAssociated`, including their coaction and constant-section laws.
- `Sheaf.AlgebraicGeometry.EquivariantCoherentGroups`: `Group`, `Space`,
  `ClosedSubgroup`, `RestrictedSpace`, `IsRestriction`, `point`, `higher`,
  `cohomologyVector`. Its companion proper-pushforward module supplies
  `IsHigherPushforward`, read together with the all-degree exchange formula.
- Proof imports: `Sheaf.AlgebraicGeometry.SmoothSectionRegularImmersion`,
  `Sheaf.AlgebraicGeometry.EquivariantRegularSelfIntersection`,
  `Sheaf.AlgebraicGeometry.EquivariantCoherentProperPushforward`, and
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`. The recorded weight-decomposition
  and concentration nodes have no Lean record yet, so there is no module to import.
  Their mathematical statements are preserved and cited in the theorem's proof docstring.

Edge cases checked before writing:

1. n=0: the colimit is the empty scheme and the final RHS is the empty sum. No
   fixed point is selected and no inverse of a zero cotangent factor is assumed.
2. r=0: every point is fixed, so hfixed and hP force Z to be the same finite reduced
   point union. Cotangent modules vanish, all denominators are 1, and the identity
   is ordinary additivity of dimensions of fibres.
3. Empty scheme and zero bundle: all cohomology characters vanish. No rank, field
   characteristic or nonempty-scheme hypothesis prevents either case.
4. Dimension zero: the empty weight product is 1. For any zero representation all
   weight spaces vanish, so formal character is 0 and its Euler factor is 1.
5. P¹ sign check: for t acting by z ↦ t z, tangent weight at 0 is +1 and the ideal
   linearization gives cotangent weight -1. For O the terms 1/(1-e^-1) and
   1/(1-e^1) sum to 1. Thus the chosen conormal convention has the required sign.
6. Arbitrary characteristic: group-scheme characters, not differentiated Lie algebra
   weights, distinguish p-multiples of characters. All multiplicities remain integers.
7. Uniform universe u for F, schemes and their F-algebras is the existing site and
   group-scheme convention; no independent smaller test-algebra universe is used.

Searches performed:

- LeanFinder: “For a smooth projective scheme with split torus action and finite
  reduced fixed scheme, the integral coherent Euler character is the sum of fibre
  characters divided by cotangent Euler factors”: eight hits, including
  `IncidenceAlgebra.eulerChar_prod`, finite-group character averaging/orthogonality,
  Hilbert 90 and Lie trace formulas; none state the formula.
- Loogle: `"character", "fixed"`: exactly the characteristic-subgroup fixedness
  lemmas `AddSubgroup.Characteristic.fixed` and `Subgroup.Characteristic.fixed`.
- Mathlib grep: `Lefschetz.*coherent|coherent.*Lefschetz|cotangent.*character`: zero hits.
- LeanSearch for integral formal characters and localization: eight hits including
  `CharacterModule.int`, `LieModule.weightSpace`, generalized Lie weights and
  `FDRep.char_one`; none are group-scheme formal characters over ℤ.
- LeanFinder for the comodule character equalizer/formal character: eight hits,
  all Lie-module weight-space constructions; no exact match.
- Mathlib grep `formalCharacter|characterCoefficient|eulerSystem|IsFixedFibrePair`:
  zero hits. The same name/concept searches in WeilConjectures and Sheaf gave no
  existing general-character formula. Existing character rings, coordinate
  comodules, ordinary localization and equivariant operations were reused.
- Read `GmRepresentation.weightSpace`: it has integer index and a LaurentPolynomial
  coaction, so is only the rank-one special case, not an interface for a general
  group-scheme character. No private replacement for the existing CharacterRing
  or Representation was introduced.
- DAG and `tools/blueprint_refs.py search 'formal character'` checked before adding
  the new definition. No definition node owns these missing formal-character and
  realization predicates. The statement node has no blueprint ancestor. Read the
  current blueprint/latest tree and the item provenance; this is an agent supporting
  statement, not the statement of its inherited blueprint unit.

Read Milne PDF printed p.480 (PDF p.492): Theorem 22.50 reduces to Nielsen's general
fixed-point theorem and Iversen 9.4 exactly as the node says. Those missing works are
already marked WANTED in the node; this delivery changes neither the supporting
statement nor its accepted integral proof route.

Validation: scompile.py compiled both modules, individually in dependency order,
against current server sources in 2.4 and 3.1 seconds, with no errors or warnings.
The wrapper reported a local-cache disk-space error and successfully used its prescribed
server-confirmation path; no compiler setting or tool was modified. Delivery preflight
and final compilation are run after the packet is assembled.

## New nodes

`def-sfb-torus-euler-character-data` owns `Sheaf.AlgebraicGeometry.TorusEulerCharacterData`.
It introduces only the missing general-character comodule equalizer, integer formal
character, Euler product, specified character localization, coefficientwise representation
restriction, and normalized geometric realization predicates. It builds on the existing
character ring, rational modules, coherent linearizations, associated bundles, and
pullback/ideal/higher-image constructions listed above. Its source is Milne Example
22.36 and the Section 22d supporting fixed-point input, with Stacks 03LF and 02O6 for
linearization and higher-image terminology. Its three required search kinds and the
project/DAG searches are recorded in its JSON. No existence theorem or choice of data
is hidden in a definition, and every declaration has its own source/blueprint docstring.

## Delivery tool failure

Two prescribed `deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push`
attempts failed before preflight or push. Both report the same compiler failure:

```text
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
```

The two modules had already passed scompile.py server confirmation together, and
the metadata signature was repaired to include the entire theorem through the final
Euler-factor expression before retrying. No delivery push occurred. The disk-space
failure is in the prescribed compilation/delivery tool; no launcher script, server
cache, live source, or shared checkout was modified to work around it.

Retry on 2026-10-24: retained the saved packet and ran the required dry run first.
Both that dry run and a second `deliver2.py --no-push` attempt failed with the same
`sandbox Sheaf.Stage2.Sandbox0` disk-space error quoted above. A fresh prescribed
`scompile.py` call with both delivery modules also returned that exact error.
The wrappers supplied no Lean elaboration diagnostic to repair. No push occurred;
the packet is retained pending repair of the compilation tool's storage failure.

Retry on 2026-10-24 at 10:39 UTC: inspected the retained worker report and ran
`deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push` first.
It again exited 1 during compilation, before preflight or push. A subsequent
`scompile.py Q54 lem-sfb-torus-coherent-fixed-point-formula` invocation supplying
both saved modules reproduced the same failure:

```text
private overlay Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
preliminary Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
[9.2 s]
```

There is no Lean elaboration diagnostic to repair. The saved Lean and node files
remain intact, and nothing was pushed. No launcher scripts or shared repository
files were edited; compiler storage repair remains outside this worker's scope.

Retry on 2026-10-24 at 10:42 UTC: inspected the retained report and ran the
required `deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push`
first. It exited 1 before preflight or push with the same storage failure.
Read both saved Lean modules and the saved item record; retained their contents.
A fresh prescribed `scompile.py` invocation supplying both delivery modules
also exited 1 with:

```text
private overlay Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
preliminary Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
[9.2 s]
```

Neither wrapper supplied a Lean elaboration diagnostic. No push occurred, and
no shared repository, launcher script or server cache was modified. The packet
is retained for retry after the compilation tool's storage failure is repaired.

Retry on 2026-10-24 at 10:45 UTC: read the saved worker report and ran the required
`deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push`
first. It exited 1 during compilation, before preflight or push. A subsequent
prescribed `scompile.py` call with both saved delivery modules also exited 1,
reproducing the same diagnostic:

```text
private overlay Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
preliminary Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
[9.2 s]
```

Neither wrapper supplied a Lean elaboration diagnostic to repair. The saved
Lean modules and node records are retained unchanged. Nothing was pushed;
no launcher script, shared repository file, or compiler cache was modified.

Retry on 2026-10-24 at 10:47 UTC: inspected the saved report and ran the required
`deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push` first.
It exited 1 during compilation, before preflight or push. The prescribed
`scompile.py` invocation with both retained delivery modules also exited 1 with:

```text
private overlay Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
preliminary Sheaf.AlgebraicGeometry.TorusEulerCharacterData
[10.5 s]
sandbox Sheaf.Stage2.Sandbox0
resource exhausted (error code: 28, no space left on device)
[9.2 s]
```

No Lean elaboration diagnostic was returned. The Lean modules and node records
are retained unchanged, and nothing was pushed. No launcher script, shared
repository file, or compiler cache was modified.
Retry on 2026-10-24 at 10:50 UTC: inspected the saved report and ran the required
`deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push` first.
It exited 1 before preflight or push. The prescribed `scompile.py` invocation
with both retained delivery modules also exited 1 with the identical diagnostic:
`sandbox Sheaf.Stage2.Sandbox0: resource exhausted (error code: 28, no space left on device)`.
Neither wrapper returned a Lean elaboration diagnostic to repair. The saved
Lean modules and node records remain unchanged; nothing was pushed. No shared
repository file, launcher script, or compiler cache was modified.

Retry on 2026-10-24 at 10:55 UTC: inspected the retained report and ran the
required `deliver2.py Q54 lem-sfb-torus-coherent-fixed-point-formula --no-push`
first. It exited 1 during compilation, before preflight or push. A fresh
`scompile.py` invocation supplying both saved modules also exited 1 with
`sandbox Sheaf.Stage2.Sandbox0: resource exhausted (error code: 28, no space left on device)`.
Neither wrapper returned a Lean elaboration diagnostic to repair. The saved
Lean and node files are retained unchanged; nothing was pushed. No launcher
script, shared repository file, or compiler cache was modified.


## Successful retry validation

On 2026-10-24 at 11:00 UTC, the required first dry run passed with
`OK (dry run): commit 5b0bff9f9b7 passes the preflight and compiles; nothing pushed`.
The earlier storage failure did not recur. Both retained modules compiled through
the prescribed wrapper. The self-check read both saved modules and the current
item and dependency records: the item changes only `lean` and adds the new
definition node to `stmt_deps`; the recorded theorem signature matches the file
verbatim. The theorem, helper definitions and node statements are retained.
The empty fixed locus, rank-zero torus, zero bundle, integer coefficients, and
cotangent-weight convention remain represented as described above.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
