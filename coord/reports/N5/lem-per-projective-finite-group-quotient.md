## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient` states
`AlgebraicGeometry.exists_finiteGroup_quotient_of_quasiProjective`, with its entire proof
`sorry`. It states the node without changing its natural statement, dependencies or proof.
The module docstring identifies the source; the theorem docstring reproduces the nine
natural-language DAG proof steps and names their inputs. There are no new definitions,
instances, helper theorems or nodes, and no dependency repairs.

Hypotheses, individually:

- `B V : Scheme.{u}` are the base and source schemes. `[IsNoetherian B]` is the
  Noetherian-base hypothesis, including quasi-compactness, not merely local Noetherianness.
- `hB` gives a Noetherian commutative ring `R`, a base map `b : B ⟶ Spec (.of R)`, a
  finite coordinate type, and an immersion `j` into its projective space, with composite
  equal to `b`. Every affine Noetherian scheme is the spectrum of such a ring, so this
  renders exactly the affine Noetherian base in the statement. Neither `b` nor `j` is
  arbitrary data replacing the hypothesis: their existence is required by `hB`.
- `f : V ⟶ B` is the given structural morphism. `[LocallyOfFiniteType f]` and
  `[QuasiCompact f]` are exactly finite type, per def-weil-finite-type-morphism.
- `hV` asserts an immersion into projective space over B, with finitely many coordinates,
  and requires its composite with the projection to be `f`. This is the node's explicit
  relative quasi-projectivity convention. Mathlib `IsImmersion` means locally closed
  immersion. No field restriction or ample-line-bundle convention is substituted.
- `H : Type v`, `[Group H]`, `[Finite H]`, `a : H →* Aut V` are a finite group and its
  scheme action; `ha` requires every automorphism to preserve `f`, so it acts over B.
  The group universe is independent of the scheme universe. No faithful-action or
  invertible-group-order assumption is present.

Conclusions, individually:

- `∃ Q q g` provides the scheme quotient and the descended structural morphism;
  `q ≫ g = f` specifies it lies over B.
- `IsFinite q` and `Surjective q` render finiteness and surjectivity.
- `∀ h, (a h).hom ≫ q = q` is invariance of the quotient map.
- `Topology.IsQuotientMap q` states the quotient topology, part of “geometric quotient”.
  Together with the finite-map condition it is equivalent to the topology supplied by
  the node, rather than a supplementary geometric hypothesis.
- For each algebraically closed field `Ω : Type u`, surjectivity of `x ↦ x ≫ q`
  says that geometric points lift, and the displayed equivalence for every `x y`
  says their images agree exactly when an element of H carries x to y. These are the
  geometric orbit fibres. Schemes and geometric test spectra use the common universe u;
  no independent smaller test-field universe is introduced.
- For every open `W` of Q, injectivity of `(q.app W).hom` and its range characterization
  identify `Γ(Q,W)` canonically with the invariant subring of `Γ(V,q⁻¹W)`. Invariance
  compares the actual pullback `appLE` and presheaf restriction on every open `T`
  contained in both domains. Since the quotient map is invariant, these domains agree;
  the test at the whole domain recovers the ordinary invariant condition. Conversely,
  restriction of an invariant section gives each of the tested equalities. This
  avoids arbitrary sheaf identifications and gives exactly the sheaf equality in
  the node, since the ring maps are the canonical section maps for every open.
- For every `Z : Scheme.{u}` and invariant `t : V ⟶ Z`, `∃! d : Q ⟶ Z, q ≫ d = t`
  is categorical uniqueness and existence in schemes, not just B-schemes or affines.
- The existential immersion `Q ⟶ ℙ(ι;B)` is relative quasi-projectivity, and the
  `LocallyOfFiniteType g` and `QuasiCompact g` clauses assert finite type of Q over B.
- `IsHProjective f → IsHProjective g` uses exactly the recorded finite projective-space
  convention in def-kun-projective, not merely properness or local projectivity.
- `IsIntegral V → IsIntegral Q` is precisely preservation of integrality, including
  nonemptiness through the recorded Mathlib definition.
- Given any open `U` with `hU : ∀ h, U ≤ (a h).hom ⁻¹ᵁ U`, the final clause provides an
  open W with `q ⁻¹ᵁ W = U` and a finite surjective restricted quotient `qU`, satisfying
  `qU ≫ W.ι = U.ι ≫ q`. The inverse group element makes this one-sided inclusion
  equivalent to invariance. The induced automorphism on U is the existing canonical
  `(a h).hom.resLE U U (hU h)`. Its invariant morphisms factor uniquely through qU.
  W is exactly the corresponding image open because q is surjective. The geometric
  orbit fibres, quotient topology and invariant structure sheaf restrict from the
  already stated global properties to this saturated open; therefore these clauses
  and categorical factorization say precisely that the restriction gives its quotient.

Dependency declarations used:

- def-kun-projective: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective`. The recorded module is absent in the older local
  checkout, so I read its live source with `scompile.py --source`. Its actual field is
  the finite-coordinate closed-immersion factorization used here. Empty coordinate
  types force an empty source, which also embeds in projective zero-space; otherwise
  finite coordinates can be reindexed by `Fin (N+1)`.
- def-pc-integral-scheme: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`, with nonempty and domain-of-sections fields.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite`, whose fields assert affine and finite section maps.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; `IsNoetherian` extends it and compactness.

Every currently recorded proof-dependency module is imported privately. Mathlib
proof inputs include Artin--Tate, proper Proj, proper and closed immersion facts,
finite-type and Noetherian permanence and base change. The stated project inputs
are GradedPrimeAvoidance, ProjStandardOpenBasis, AffineGroupoidOrbitFibres,
ProjQcOpenTwistAmple, AmpleImmersionAffineBase and ProjectiveImpliesProper.
The following proof dependencies have no recorded statement or Mathlib match yet,
so no import for them can be written: lem-per-quasiprojective-affine-composition,
lem-per-equivariant-projective-envelope, lem-per-finite-graded-proj-morphism and
lem-per-admissible-quotient-affine-integral-charts. They are proof inputs only;
the present statement requires none of their objects or declarations.

Edge cases checked before writing: V empty gives Q empty and retains the unique
categorical factorization and the empty invariant-open case; B empty also forces
V empty. The trivial group and arbitrary trivial actions give the identity
quotient, so no faithfulness condition is needed. U empty and U all of V both
satisfy the restriction clause. Integrality is conditional and excludes the empty
case only when that antecedent holds. Arbitrary characteristics, including those
dividing the group order, are allowed: the proof plan uses orbit polynomials,
not averaging. Projective zero-space and empty finite coordinate types are covered.
Non-affine invariant opens are quantified, not merely invariant affine charts.

Searches made:

- `msearch.py ... leanfinder "A finite group acting on a quasi projective scheme admits
  a finite geometric categorical quotient which is quasi projective"`: eight hits,
  concerning pre-Galois categories, action quotients and projectivization, no scheme
  quotient theorem matching this statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsHProjective,
  AlgebraicGeometry.IsQuasiProjective"`: zero hits; unknown IsHProjective in Mathlib.
- `msearch.py ... grep "quotient|QuasiProjective" AlgebraicGeometry`: 25 unrelated
  hits; no matching theorem.
- `rg` for QuasiProjective, categorical/geometric quotient and invariant sections in
  Mathlib AlgebraicGeometry, upstream WeilConjectures and shared lean/Sheaf found
  the upstream field-only `IsQuasiProjective` and the project's
  `IsAdmissibleFiniteSchemeQuotient`. The former does not accept general B; the latter
  includes an admissibility hypothesis and does not encode this theorem's categorical,
  relative-projectivity, or invariant-open conclusions. Neither is an exact match.
  The latter's canonical appLE formulation was read as an example of the already
  available section maps, rather than copied as a new definition.
- DAG statement search found def-sc-quasi-projective is likewise field-only, and no
  existing exact statement for this item. Relative quasi-projectivity is spelled out
  directly as the item already defines it, following the landed
  NormalProjectiveCompactification module's convention; no duplicate predicate is added.
- `rg -n lem-per-projective-finite-group-quotient` in upstream WeilConjectures found
  no declaration. The recorded dependency signatures and docstrings were read in their
  source files, using live source resolution for the missing/stale upstream module.

Source checked online: [Rydh, arXiv:0708.3333v2](https://arxiv.org/pdf/0708.3333),
Theorem 4.4, Proposition 4.7, Remark 4.9, printed pp. 20--23, states the scheme-quotient
existence and preservation of (quasi-)projectivity under the Noetherian hypotheses.
The stronger finite-coordinate convention is justified by the node's own detailed
homogeneous-coordinate proof, retained verbatim in the docstring. No source or node
fault, and no STATEMENT-DISPUTED flag.

Validation: scompile.py compiled the sandbox and the actual library-path module,
separately, in 2.0 s and 2.1 s with no errors or warnings. The first pass identified
a privately imported IsAlgClosed; an explicit public import fixed it. All variables
and universes are explicitly bound, with `autoImplicit false` in the file.

## Second reading by N5

I reopened the completed file and the node for a separate clause-by-clause reread.
This is the dispatcher's single-worker delivery; no other agent was started or
claimed as an independent reader. The maintainer performs the independent delivery
review specified in the worker brief.

The reread checked hB's Noetherian affine spectrum, the two finite-type hypotheses,
the actual projective-space factorization equations for B, V and Q, and the action's
B-invariance. It checked that categorical targets are arbitrary schemes, both
geometric-point surjectivity and the orbit equivalence are present, and the canonical
section map's injectivity accompanies its invariant-image condition. For the last
clause, `hU` implies equality using the inverse group element; resLE is the actual
restricted action, and surjectivity plus the inverse-image equality identifies W
with the image of U. The restricted map is finite and categorical, and the global
geometric data restrict to it. Finally the projective and integral conclusions are
implications using the existing definitions. No missing clause or added hypothesis
was found. There is only the item's one named postponed theorem.
