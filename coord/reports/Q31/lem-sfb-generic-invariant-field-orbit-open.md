## Worker report

Repair of returned immutable head `16bd1acd4b10`. The old Lean statement was mathematically
incorrect; its claimed clause correspondence and second reading were also incorrect. The
DAG's mathematical statement is unchanged. The sandbox node was compared to the current
read-only base: before this repair only `lean` differed. This delivery rebuilds its record
from the current base, changes `lean`, and adds the already-landed definition node
`def-sfb-dominant-function-field-map` to `stmt_deps`. The delivery wrapper supplies the
current-base commit and rebase bookkeeping. No direct Git operation was used.

The replacement module is `Sheaf.AlgebraicGeometry.GenericInvariantFieldOrbitOpen`, with
one theorem `AlgebraicGeometry.generic_invariant_field_orbit_open` and proof `sorry`.
There are no new definitions, helper theorems, assumptions on normality, or assumptions
on faithfulness/freeness. Every universe and binder is explicit; `autoImplicit` is false.

Sources read: the node's full eleven-step proof; ILO, Travaux de Gabber, X Lemma 2.2(iii),
printed pp. 149–150 (PDF pages 155–156); Stacks `groupoids.tex`, `lemma-points` (03BL),
and its surrounding invariant-ring construction. ILO states the quotient's universal
homeomorphism on a dense open; this DAG node isolates the generic invariant-field
spreading argument, without ILO's additional smoothness, étaleness or faithful-action
hypotheses. The replacement follows that isolated argument, not the stronger ILO package.

Hypothesis correspondence:

* `k : Type u`, `[Field k]`: the base field.
* Integral schemes `W`, `X`: `[IsIntegral W] [IsIntegral X]`.
* Their k-structures are the explicit maps `pW : W ⟶ Spec (.of k)` and
  `pX : X ⟶ Spec (.of k)`. Each has both `LocallyOfFiniteType` and `QuasiCompact`,
  exactly the recorded finite-type convention. Explicit structure maps allow the
  compatibility of the several morphisms over the base to be stated.
* The given map is `a : W ⟶ X`, with `[IsHProjective a] [Surjective a]` and
  `ha : a ≫ pX = pW`. Dominance is inferred from surjectivity; it is not an additional
  hypothesis (`UnderlyingMap.lean`, instance at line 226).
* Its induced finite field extension is `hfinite`: `RingHom.Finite` of the algebra map
  obtained by explicitly passing `a.dominantFunctionFieldAlgebra`. There is no free
  `Algebra X.functionField W.functionField` binder. The existing definition is the
  generic stalk map, not a chosen embedding.
* `N : Type v`, `[Group N] [Finite N]`, `act : N →* Aut W`: the finite group action.
  `hk` says each automorphism is over k; `hinv` says `a` is invariant.
* `hpure` tests precisely the elements fixed by
  `(Scheme.functionFieldAut (act g)).hom`. For each such `z`, a power with exponent
  `(ringExpChar k)^n` lies in the image of the same induced base function-field map.
  This is the power criterion for pure inseparability. The exponential characteristic
  is p in characteristic p and 1 in characteristic zero; the latter really says that
  every fixed field element comes from the base, rather than allowing a zeroth power.

Conclusion correspondence:

* `U`, `hU : IsAffineOpen U`, `Dense`, and `Set.Nonempty` give the dense nonempty affine
  open. `hV : IsAffineOpen (a ⁻¹ᵁ U)` gives its affine inverse image.
  `hη` locates the source generic point in that nonempty open so the actual germ map
  can be written without a chosen fraction-field identification.
* `R` and `S` are not binders: throughout the signature they are respectively
  `Γ(X,U)` and `Γ(W,a ⁻¹ᵁ U)`. `IsFinite (a ∣_ U)` and `Surjective (a ∣_ U)` occur once.
* `S^N` is the existing `finiteQuotientInvariantSections act (a ⁻¹ᵁ U)`. Its definition
  is the subring of sections whose pullbacks and restrictions agree on all overlaps.
  Since `hinv` makes the inverse image invariant, these are exactly the fixed sections.
* The quotient target is literally `Spec (.of (finiteQuotientInvariantSections ...))`.
  The map `q` is fixed by the equation
  `q = hV.isoSpec.hom ≫ Spec.map (.ofHom (S^N).subtype)`. It is the affine quotient,
  not an arbitrary morphism. `IsFinite q ∧ Surjective q` supplies its claimed properties.
* `r : Γ(X,U) →+* S^N` is fixed by `subtype.comp r = (a.app U).hom`. Inclusion of the
  fixed ring is injective, so this equation uniquely specifies the base-map corestriction.
  The equation `b = Spec.map (.ofHom r) ≫ hU.isoSpec.inv` uniquely specifies the residual
  map, and `q ≫ b = a ∣_ U` identifies the factorization. Its properties are all present:
  `IsFinite b ∧ UniversallyInjective b ∧ Surjective b`.
* For every algebraically closed `Ω : Type u` and `t : Spec Ω ⟶ Spec(S^N)`, the scheme
  `pullback q t` is nonempty. For any of its two points `x,y`, the displayed `g,l`
  witness `l x = y`; the first projection composed with the open immersion into W
  intertwines `l` with `(act g).hom`, and the second projection stays fixed. The open
  immersion is a monomorphism, so these two equations determine the induced group map
  on the pullback uniquely. Thus `g` is essential and `l` is not an unconstrained map.
* The fraction-field biconditional is inside `W.functionField`, canonically the fraction
  field of the nonempty affine source open. Its right side says `z` is a quotient of
  two elements of `S^N`, with the denominator germ nonzero. It is precisely
  `Frac(S^N) = Frac(S)^N` under the injective germ embedding. There is no occurrence
  of `X.functionField` in this conclusion, and it does not assert equality with k(X).
* A separate clause gives nonemptiness and the same two-projection action equations
  for `pullback (a ∣_ U) t` for every `t : Spec Ω ⟶ U.toScheme`. This supplies the
  previously missing assertion for the fibres of the original restricted morphism.
* For prime `p` with `CharP k p`, the power condition quantifies only over `t : S^N`.
  It says the underlying section raised to `p^m` belongs to `Set.range (a.app U).hom`.
  The prime condition states positive characteristic and excludes the characteristic-zero
  `CharP k 0` instance. The common exponent can be zero.
* The characteristic-zero clause is equality of subrings of S:
  `(a.app U).hom.range = S^N`. This expresses `S^N=R` using the actual inclusion into S;
  it is neither equality of the carriers S and R nor a type equality.

Dependency declarations and source signatures inspected:

* `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `IsHProjective`:
  finite projective-space closed-immersion factorization, lines 30–40.
* `Mathlib.AlgebraicGeometry.Properties`, `IsIntegral`: nonempty scheme whose section
  rings on nonempty opens are domains, lines 238–247.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, lines 39–47;
  `Morphisms.QuasiCompact`, `QuasiCompact`, lines 38–47.
* `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective`, lines 56–67.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `IsFinite`, lines 34–41;
  `Morphisms.UniversallyInjective`, `UniversallyInjective`, lines 42–49 (Stacks 01S4).
* `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, lines 95–116.
  These are the actual scheme pullbacks, using `Mathlib.AlgebraicGeometry.Limits`.
* The integral clause of `def-sc-function-field` is Mathlib `Scheme.functionField`,
  the generic stalk; its signature, germ map, algebra instance and field instance were
  read in `Mathlib.AlgebraicGeometry.FunctionField`, lines 34–52. The recorded owner
  `WeilConjectures.AlgebraicGeometry.FunctionField` is publicly imported too.
* `def-sfb-dominant-function-field-map` records
  `Scheme.Hom.dominantFunctionFieldAlgebra`, in
  `Sheaf.TraceFormula.LocalDimensionFormula`, lines 37–55: its real body constructs the
  generic-point equality and applies `functionFieldMap`, then `RingHom.toAlgebra`.
* `WeilConjectures.AlgebraicGeometry.StalkAut`, `Scheme.functionFieldAut`, lines 87–105:
  the canonical stalk automorphism at the fixed generic point.
* `Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient`,
  `finiteQuotientInvariantSections`, lines 55–64, and
  `exists_admissible_finite_type_field_quotient`, lines 120–153. The former is directly
  used in the statement; the latter is the existing proof dependency.
* `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap`, lines 95–103, and
  `RingHom.toAlgebra`: the induced field extension convention. `RingHom.Finite` was
  read at `Mathlib.RingTheory.Finiteness.Defs`, lines 168–171.
  `Sheaf.FieldTheory.FieldTower` documents this finite-extension convention as well as
  the Mathlib pure-inseparability convention. The power criterion is written explicitly,
  with `ringExpChar` read in `Mathlib.Algebra.CharP.Defs`, lines 387–397 and 434–444.

The proof imports `GenericFiniteOpenNeighborhood` and `ProjectiveImpliesProper` remain
plain imports because their recorded statements are used in the eleven-step proof plan.
Both formerly flagged imports now supply declarations actually used in the signature:
`dominantFunctionFieldAlgebra` and `finiteQuotientInvariantSections`.

Searches performed in the initial delivery: LeanFinder for projective generically finite
maps with purely inseparable fixed field and geometric orbit fibres (eight unrelated
Galois-category hits); Loogle for `UniversallyInjective, IsFinite` (no hits); Mathlib grep
for `FixedPoints|fixedField|functionFieldMap` in AlgebraicGeometry (no hits); project `rg`
for the item id and invariant-field/orbit terminology (no exact statement).
Repair searches: LeanFinder for canonical finite invariant affine quotient with purely
inseparable invariant function field (eight arithmetic-Frobenius and Galois invariant
hits, no exact statement); Loogle for `AlgebraicGeometry.Scheme.functionFieldAut`
(unknown identifier in its Mathlib index); Mathlib grep for the item declaration,
`functionFieldAut`, and `finiteQuotientInvariantSections` (zero hits). Project `rg` found
`Scheme.functionFieldAut` in the upstream `StalkAut` module and its existing consumers;
DAG `rg` found the already-landed `def-sfb-dominant-function-field-map`, which is reused.
No new notion or duplicate declaration was introduced.

Edge cases and counterexamples checked on the repaired formula:

* Trivial N and Frobenius `A¹_k → A¹_k` in characteristic p: S^N=S, the invariant
  function field may be a nontrivial purely inseparable extension. The fraction clause
  says Frac(S)=Frac(S), and does not incorrectly identify it with the base field.
  The common p-power lands in the actual base image.
* In characteristic zero, `k[t]` with involution `t ↦ -t` over `k[t²]`: S^N is the
  base image but S is larger. The repaired characteristic-zero clause states precisely
  that image equality, and the positive-characteristic clause is inapplicable.
* With a nontrivial action in characteristic p (e.g. Artin–Schreier translation), only
  invariant sections have the uniform-power requirement; arbitrary sections are not
  erroneously required to become base sections by a p-power.
* A nonfaithful action has the same fixed ring and orbits as its image; no faithful or
  free action binder has been added. A group is nonempty (the previous report's “empty
  group” edge case was invalid). Integral schemes are nonempty, while each geometric
  fibre's nonemptiness is stated explicitly. Exponent m=0 is allowed.
* No normality is used: the norm-denominator calculation works in every domain; a
  characteristic-zero nonnormal birational finite map can become an isomorphism after
  shrinking, as the source proof requires.

## Repair of the return

H3: every listed defect is removed. The base structures and finite-type binders are
present; the field algebra is the canonical one; `ρ` was removed in favour of
`functionFieldAut (act g)`; the fraction-field equality uses invariant numerators and
nonzero denominators in the actual source section ring; R,S,φ and Q are no longer
arbitrary; q,r,b are specified by canonical formulas; both fibre clauses constrain the
first projection by `act g` and the second by the identity; the characteristic-p clause
ranges over S^N; the characteristic-zero clause is subring-image equality; `IsFinite b`
and the original-map geometric orbit clause are present; duplicates are removed.
H4: `dominantFunctionFieldAlgebra` is now explicitly used for both hfinite and hpure,
and its already-landed definition node was added to stmt_deps.
H9: the two formerly unused imports now provide the invariant ring and canonical field
algebra directly used by the statement. Imports serving only the proof plan are plain.
H11: the former second reading was wrong. It has been replaced below by a concrete
clause-by-clause repair audit. No independent reviewer is claimed: the dispatcher forbids
starting other agents and the maintainer supplies the independent reading.

## Second reading by Q31

This is the dispatched worker's second pass through the repaired file, not an independent
agent review. I compared the old signature retained in the sandbox's returned lean record
with the current DAG and replacement signature. The old file's unrelated k, free algebra,
free ρ, arbitrary R/S/φ/Q, false fixed-field equality, unconstrained l, and type equality
are all absent. I checked the following against the actual signature:

1. `pW,pX,ha,hk` tie all three k-maps to the same base, and both finite-type conjunctions
   are present. `hfinite,hpure` explicitly instantiate the induced field algebra.
2. Every fixed-element test uses `Scheme.functionFieldAut (act g)`; no independent
   action or free field embedding appears.
3. All coordinate elements and base images use Γ(W,a⁻¹U), Γ(X,U), and `(a.app U).hom`.
   The quotient target contains the fixed subring in its type. Its map q and the
   residual map b are each equated to their canonical affine-spectrum formulas.
4. Each orbit clause contains a nonempty actual pullback and two projection equations;
   `g` appears in the first equation. Since the open immersion is mono, those equations
   determine the lifted action, including for infinitesimal finite fibres.
5. The fixed-fraction biconditional has no k(X) on its right and requires a nonzero
   denominator. Both characteristic clauses use S^N, while the zero-characteristic
   equality compares subrings of the same ring S. `IsFinite b` occurs once.
6. No theorem is proved; the only proof is `sorry`. All declarations and universes are
   explicit and every Lean line has at most 100 characters.

Validation: the replacement compiled cleanly through scompile.py as both a sandbox probe
and its library module. Final compile and delivery preflight results are recorded by the
prescribed wrappers; no local lake/global build was run in this repair.
