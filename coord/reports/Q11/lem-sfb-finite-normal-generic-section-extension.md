## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteNormalGenericSectionExtension` states
`AlgebraicGeometry.finite_normal_generic_section_extension`. Its proof is `sorry`;
no definition or mathematical lemma is proved in this stage. The node is unchanged
apart from its `lean` field. No missing notion, dependency repair, statement correction,
or statement dispute was needed.

Clause-by-clause correspondence:

- The integral scheme S is `{S X : Scheme.{u}} [IsIntegral S]`. Mathlib's integral
  scheme is nonempty and has domain section rings on every nonempty open; this
  agrees with the recorded dependency's equivalent definition.
- All local rings of S are normal domains: the binder
  `hS : ∀ x : S, IsDomain (S.presheaf.stalk x) ∧
  IsIntegrallyClosed (S.presheaf.stalk x)` uses exactly the normal-domain inline
  form recorded by def-weil-pbc-normal-ring. The first conjunct is automatic
  for an integral scheme but is retained to make the stated hypothesis explicit;
  the substantive normality condition is not automatic.
- The generic point η is Mathlib's canonical `genericPoint S`. The field
  K = O_(S,η) is `S.functionField`, definitionally the stalk at that point,
  with the existing integral-scheme field instance. This is the arbitrary
  integral-scheme clause of def-sc-function-field, not its component-product
  construction for general curves.
- The canonical j is `S.fromSpecStalk (genericPoint S)`. Its definition restricts
  the structure sheaf to the generic stalk and applies Spec; the source is
  definitionally `Spec S.functionField`. It is not an arbitrary morphism.
- The arbitrary finite morphism is `(f : X ⟶ S) [IsFinite f]`.
- The global-section set is `{s : S ⟶ X // s ≫ f = 𝟙 S}`.
  The generic-section set is
  `{a : Spec S.functionField ⟶ X // a ≫ f = S.fromSpecStalk (genericPoint S)}`.
  In Lean composition `s ≫ f` denotes the node's `f ∘ s`.
- The displayed function sends a section s to `j ≫ s.1`, with its equation
  over S supplied by associativity and the section equation. This small proof
  merely certifies that the explicit restriction function has the stated codomain.
- `Function.Bijective` of that very function is the stated restriction bijection.
  Surjectivity supplies every prescribed extension; injectivity gives exactly
  one. Both directions are asserted, including an empty generic-section set.
- There are no properties on X, no Noetherian hypothesis on S, and no base field
  or finite-type-over-a-field restriction. One explicit universe u is used for
  arbitrary schemes, as in Mathlib's category of schemes; no dimension or size
  restriction beyond that category is introduced. Auto-implicit binding is disabled
  for the declaration, and all variables and the universe are explicit.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`
  (together with the core `IsDomain`), using the recorded normal-domain form.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: its docstring explicitly
  assigns the arbitrary integral-scheme case to Mathlib's `Scheme.functionField`;
  this recorded module is publicly imported, rather than copying the notion.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField` and its
  field instance; `functionField_isFractionRing_of_isAffineOpen` for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- The existing canonical map is `Scheme.fromSpecStalk` in
  `Mathlib.AlgebraicGeometry.Stalk`; its full definition and independence of
  affine neighborhood were read. No helper definition is necessary.

Proof dependency modules are private imports: `Mathlib.AlgebraicGeometry.AffineScheme`
(affine open basis and stalk localization), `Mathlib.AlgebraicGeometry.Scheme`
(Spec and germ/stalk compatibility), `Mathlib.AlgebraicGeometry.Gluing`
(`Scheme.Cover.glueMorphisms` and `hom_ext`),
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (`Algebra.IsIntegral.of_finite`),
and `Mathlib.RingTheory.LocalProperties.IntegrallyClosed`
(`IsIntegrallyClosed.of_localization_maximal`). The normal-domain and
finite-morphism modules are already public imports. Their existing Mathlib matches
are used; no duplicate DAG theorem is introduced. The docstring follows all five
node proof steps and names their dependency nodes.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-finite-birational-over-normal` (Tag 0AB1), including its affine normality
argument. The node expressly adapts that argument to the image of a generic
section. The proof docstring uses the direct affine image argument, so it never
assumes X integral to invoke 0AB1 on X itself.

Edge cases checked before drafting:

- S cannot be empty because integrality includes nonemptiness, exactly as the node.
- X may be empty. Both section sets are then empty; bijectivity still expresses
  the correct assertion without assuming a prescribed section exists.
- A finite closed subscheme supported away from η has no generic section and no
  global section; the statement does not accidentally assert unconditional existence.
- Nonreduced X is allowed: over A, the finite algebra A[ε]/(ε²) has the unique
  generic section ε ↦ 0, which extends. Uniqueness uses the base domain, not
  reducedness of the source algebra B.
- Disconnected finite schemes, multiple generic sections, nonflat finite algebras,
  and non-Noetherian normal integral bases remain within the binders.
- If S is Spec of a field, the canonical generic map is an isomorphism and the
  displayed restriction is the expected bijection.
- Normality is essential: for the cusp A = k[t²,t³] and its finite normalization
  k[t], the identity generic map cannot extend to a retraction k[t] → A.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder "Restriction of sections of a finite morphism over a
  normal integral scheme to its function field is bijective"`: eight hits,
  including `Scheme.RationalMap.fromFunctionField_ofFunctionField`, normalization
  maps, and `Scheme.SpecToEquivOfField`. They concern spreading, normalization,
  or field-valued points and do not assert the required finite-section bijection.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.fromSpecStalk,
  AlgebraicGeometry.Scheme.functionField"`: three rational-map hits. The
  `equivFunctionField` result only relates generic morphisms to rational maps;
  extension over all of a normal base is not its statement.
- `msearch.py ... grep "generic.*[Ss]ection|[Ss]ection.*generic|finite.*normal"
  AlgebraicGeometry`: five Zariski-main-theorem hits, none exact.
- Direct rg in Mathlib AlgebraicGeometry, and in the project's WeilConjectures
  and Sheaf trees for generic/section and finite/normal patterns, found related
  finite-etale generic full faithfulness and normal semiabelian extension, not
  this theorem for arbitrary finite X. The upstream
  `Scheme.finiteEtale_normalIntegral_generic_hom_full` requires both covers
  finite etale and thus is not this statement.
- Searching the exact node id in WeilConjectures and Sheaf found only a proof-plan
  citation in `NormalSemiabelianHomExtension.lean`, no declaration of this node.
- The provided CompactObject example has been withdrawn; its recorded upstream
  replacement was read through its node record. Current module-mode conventions
  from brief-stage2 are followed.

Validation: the initial concrete restriction statement passed `scompile.py`.
The final module includes the expanded five-step proof plan and all available
proof-dependency imports, and is validated again with the prescribed wrapper.
The delivery dry run and final delivery run perform the required preflight and
server compile. The maintainer performs the independent statement review.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
