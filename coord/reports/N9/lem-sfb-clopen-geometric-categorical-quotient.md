## Worker report

The module `Sheaf.AlgebraicGeometry.ClopenGeometricCategoricalQuotient` states
`AlgebraicGeometry.clopen_geometric_categorical_quotient`, with its sole proof `sorry`.
It constructs no replacement quotient, open subscheme, section subring, or action notion.
The original node statement, proof and statement dependencies are unchanged.
Both invariant-section conditions are written inline in the form of the last clause of
`IsAdmissibleFiniteSchemeQuotient`; no quotient-existence theorem is imported or cited.

Hypotheses, in order:

- A finite group acting on V: `{H : Type v} [Group H] [Finite H]`, schemes
  `{V X : Scheme.{u}}`, and `(a : H →* Aut V)`. The group universe is independent.
- An invariant finite surjective morphism: `(q : V ⟶ X) [IsFinite q] [Surjective q]`
  and `hinv : ∀ h, (a h).hom ≫ q = q`. Surjectivity is on underlying scheme points.
- Every algebraically closed field: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
  `hpoints` asserts surjectivity of `x ↦ x ≫ q` on actual scheme morphisms from
  `Spec (.of Ω)` and the equivalence between equal images and existence of an h
  with `x ≫ (a h).hom = y`. No geometric-point action is replaced by underlying points.
- The canonical invariant-section identification on every open: `hsections` asserts
  injectivity of `(q.app W).hom` and, for every `s : Γ(V, q ⁻¹ᵁ W)`, an iff between
  `s ∈ Set.range (q.app W).hom` and invariance. The invariance formula compares
  `((a h).hom.appLE (q ⁻¹ᵁ W) O hOh).hom s` with
  `(V.presheaf.map (homOfLE hO).op).hom s` for every h and common subopen O.
  This is exactly the last clause of the recorded admissible-quotient definition.
  Injectivity and this image characterization retain the canonical ring-map identification.
- Categorical quotient for every scheme target: `hcategorical` quantifies over all
  `T : Scheme.{u}` and all invariant `f : V ⟶ T`, with `∃! g, q ≫ g = f`.
  Targets are unrestricted schemes, without a field structure or separation requirement.
- Open and closed U: `(U : X.Opens) (hU : IsClopen (U : Set X))`.

Conclusion clauses, in order:

- V_U is the actual open subscheme `(q ⁻¹ᵁ U).toScheme`, and
  `IsClopen (q ⁻¹ᵁ U : Set V)` records closedness as well as openness.
- The existential `aU : H →* Aut (q ⁻¹ᵁ U).toScheme` and the equations
  `(aU h).hom ≫ (q ⁻¹ᵁ U).ι = (q ⁻¹ᵁ U).ι ≫ (a h).hom`
  give precisely the induced action. The inclusion is a monomorphism, so these equations
  uniquely determine it and express H-invariance of the inverse-image subscheme.
- The canonical q_U is `morphismRestrict q U`, and its `IsFinite` and `Surjective`
  predicates occur explicitly in the conclusion.
- The next conjunct repeats surjectivity and the orbit-fibre equivalence for actual
  Ω-points of V_U and U, with the same induced action `aU`.
- Every `W : U.toScheme.Opens` has injective canonical q_U section map. For every
  section s on its inverse image, membership in the range is equivalent to equality
  of action pullback and restriction on every common subopen O, using `aU`,
  `appLE`, and the presheaf of `(q ⁻¹ᵁ U).toScheme`. This is the same inline
  invariance formula as in the hypothesis, with the actual restricted objects.
- Every invariant `f : (q ⁻¹ᵁ U).toScheme ⟶ T` uniquely descends to U via q_U.
- The final implication uses the recorded `IsAdmissibleFiniteSchemeQuotient` on both
  the original and induced actions, without weakening its orbit-affine, quotient-topology,
  underlying-orbit, finiteness, or invariant-section conditions.

Dependencies read and used:

- `Mathlib.Data.Finite.Defs`: `Set.Finite`, `Set.Infinite` (recorded finite-set node);
  the corresponding type-level predicate `[Finite H]` expresses finite H.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  also read the companion `IsIntegralHom` signature in `Morphisms.Integral`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and the recorded
  proof interface `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`.
- `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`:
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`, read in full.
- `Mathlib.AlgebraicGeometry.Restrict`: `morphismRestrict`, `morphismRestrict_ι`.
- Proof imports give `Limits.pullback` and its universal property, scheme coproducts
  and their disjoint open coprojections (`Mathlib.AlgebraicGeometry.Limits`),
  `Scheme.Cover.glueMorphisms` and uniqueness (`Mathlib.AlgebraicGeometry.Gluing`),
  and `Scheme.isBasis_affineOpens` (`Mathlib.AlgebraicGeometry.AffineScheme`).
  Finite base-change and affine-source interfaces are available through the finite import.

Source checked: the local ILO PDF, extracted into the sandbox scratchpad, IX 1.4 at
printed pp. 132--133 and X 2.3 Step 2, diagram (2.c), at printed p. 151. The node is
explicitly an agent-formulated general clopen lemma serving that diagram; it does not
inherit the field or finiteness-of-type assumptions of the alteration setting. Its
seven-step proof, including descent to T coproduct (X minus U), is reproduced in the
theorem docstring with its DAG interfaces. The example CompactObject module is now
withdrawn; its node records the upstream replacement, and the module header follows
current live stage-2 module-mode conventions instead.

Edge cases: U empty gives empty source and target restrictions; maps from the empty scheme
remain unique even for T empty. U equal to X recovers q up to the canonical open isomorphisms.
If X is empty then V is empty; if V is empty, the assumed underlying surjectivity forces X
empty. No nonempty scheme or nonempty open hypothesis is imposed. A trivial H, nonfaithful
H-actions, nonreduced schemes, and nonseparated schemes are included. The proof of affine
orbit neighbourhoods uses inverse images of affine target opens under the finite q_U,
so it does not use affineness of intersections in a nonseparated source. All fields and
schemes are quantified in the common scheme universe u; the action group has arbitrary
universe v. Every variable is explicitly bound, with `autoImplicit false`.

Searches (the wrapper also logs the exact queries and results in `searches.jsonl`):

- LeanFinder: "Restriction of a finite geometric and categorical quotient of a scheme by
  a finite group to an open and closed subscheme is a quotient". Eight results, including
  `IsFinite.instMorphismRestrict` and abstract Galois-category quotient results; none
  states the geometric, invariant-section and categorical restriction clauses together.
- Loogle: `AlgebraicGeometry.morphismRestrict, AlgebraicGeometry.IsOpenImmersion.lift`.
  Zero results for the combined query. Direct source reads locate both component APIs.
- Mathlib grep: `categorical.*[Qq]uotient|[Qq]uotient.*[Cc]lopen|[Gg]eometric.*[Qq]uotient`
  under AlgebraicGeometry: zero hits.
- LeanSearch: "An invariant finite surjective scheme quotient remains geometric and
  categorical when restricted to a clopen target". Eight hits: restriction of finiteness,
  properness, integrality, quasi-compactness, topology and flat quotient maps; no full match.
- `rg` of project and upstream AlgebraicGeometry found the existing section-subring helper
  and `FiniteQuotientNormalProper`, which assumes a field structure and normal proper
  source and concludes normality/properness, not this clopen theorem. The quotient-existence
  theorem in `AdmissibleFiniteTypeFieldQuotient` assumes a separated scheme over a field
  locally of finite type, so its invariant-open clause cannot supply this general theorem.
- `rg` of upstream for this node id and of upstream/project/Mathlib and upstream declaration
  index for `clopen_geometric_categorical_quotient` found no prior declaration.

## Repair of returned delivery d11b5dce7b9f

H2: removed `lem-sfb-admissible-finite-type-field-quotient` from `stmt_deps` and removed
`Sheaf.AlgebraicGeometry.AdmissibleFiniteTypeFieldQuotient` from the module imports.
The plain section-subring helper was not theorem-dependent data, so the theorem node
was not a valid statement dependency. Both section clauses now state injectivity and
membership in the canonical map's image iff the action pullback equals restriction on
every common subopen, following the last clause of `IsAdmissibleFiniteSchemeQuotient`.
The `lean.statement` field is extracted verbatim from the repaired declaration.
The node copy was refreshed from current main and only its `lean` record is changed.
All other hypothesis and conclusion clauses, the seven-step proof docstring and the
sole `sorry` proof remain as reviewed. No new definition node or statement correction
is needed, and the empty/full open and empty scheme edge cases remain included.

Validation: the prescribed server `scompile.py` compiled the repaired file cleanly in both
sandbox and library module contexts (1.7 seconds each). The delivery dry run runs preflight
and repeats the per-file server compilation before the final delivery.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
