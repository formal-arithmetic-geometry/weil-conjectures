## Worker report

Item: `lem-sfb-coefficient-cocone-comparison-agreement`.
The module `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` states
`AlgebraicGeometry.ProEtale.finiteCoefficient_cocone_comparison_agreement`.
Its sole proof is `sorry`, as required for stage 2. No definition, dependency record,
new node, or natural-language statement is changed. The node copy changes only `lean`.

### Hypotheses and clauses

- “A prime ℓ”: `(ℓ : ℕ) [Fact ℓ.Prime]`. Primality is neither omitted nor replaced
  by an assumption on the characteristic of X.
- “X any scheme”: `(X : Scheme.{u})`, with explicit universe `u`. There is no
  Noetherianity, nonemptiness, properness, or size equality hypothesis.
- “E ⊆ H ⊆ Ω finite intermediate extensions”: `{E H :
  PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ H)`. This existing subtype gives
  finite intermediate fields of ℚ_[ℓ] inside `PadicAlgCl ℓ`, with its fixed topology.
- “Use the internal coefficient rings, canonical extensions, restrictions,
  adjunctions and tensor comparison”: the left side of the first equality is the
  recorded `finiteCoefficientDerivedTensorCompIso X ℓ h`, with its fixed data, not
  an arbitrary natural isomorphism or a hypothesis asserting its existence.
  Its source and target are the derived categories of internal module objects in
  `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}` over the prescribed coefficient rings.
  Restrictions and adjunctions are the existing accompanying constructions of
  `CondensedDerivedTensorComparison`, not additional inputs to this theorem.
- “Ω consists of continuous functions with image in one finite subfield”:
  `finiteCoefficientDerivedToAlgCl` uses `padicAlgClRingObj X ℓ`, defined using
  `Profinite.padicAlgClRingObj ℓ`. The inclusion's actual implementation is
  `padicSubfieldToPadicAlgClRingPresheaf`, whose codomain is
  `PadicAlgCl.finiteIntermediateFieldValued`. Thus this is the specified ring,
  rather than all continuous closure-valued functions.
- “Identify the finite and closure extension functors”: these are definitional
  identifications. `finiteCoefficientDerivedExtension` and
  `derivedExtendScalarsSubfield` unfold to the same `leftDerivedFunctor` of
  `Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)`. Likewise
  `finiteCoefficientDerivedToAlgCl` and `derivedExtendScalarsToPadicAlgCl`
  use `padicSubfieldRingObjToPadicAlgCl X ℓ E` (or H). Consequently the first
  equality is homogeneous equality between the specified natural isomorphisms,
  with identical endpoint functors, and uses no chosen transport.
- “The fixed θ is the canonical derived comparison”: the first conjunct is
  `finiteCoefficientDerivedTensorCompIso X ℓ h = derivedExtendScalarsCompIso X ℓ h`.
  This is equality of the complete isomorphisms, hence also of both ambient
  natural transformations and their components at every ambient derived object.
- “On the bounded constructible full subcategories”: `∀ K :
  PadicSubfieldConstructible X ℓ E`. This is exactly the existing full subcategory
  of objects with bounded, constructible cohomology, not a bounded-below variant.
- “The forward components are the ambient arrows”: the second conjunct's first
  equality is `((constructibleToPadicAlgClCompIso X ℓ h).hom.app K).hom =
  (finiteCoefficientDerivedTensorCompIso X ℓ h).hom.app K.obj`.
  The outer `.hom` is the actual ambient arrow of a full-subcategory morphism.
- “The inverse components are the ambient arrows”: the paired equality uses
  `.inv.app K` and `.inv.app K.obj` with the same orientation. Both equalities
  refer to the fixed restricted comparison, with no independently chosen inverse.

### Dependency declarations and sources read

Read each statement-dependency node in full, its recorded binding, and the full
signature and docstring of each bound declaration.

- `def-weil-pbc-finite-derived-tensor-comparison`:
  `Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison`,
  `AlgebraicGeometry.ProEtale.finiteCoefficientDerivedTensorCompIso`, together with
  `finiteCoefficientDerivedExtension`, `finiteCoefficientDerivedToAlgCl`, and the
  restriction/adjunction/Hom-equivalence constructions in that module.
- `def-sfb-derived-extend-subfield`, `def-sfb-derived-extend-to-qlbar`,
  `def-sfb-derived-extend-comp-iso`, and `def-sfb-constructible-extend-comp-iso`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, respectively
  `AlgebraicGeometry.ProEtale.derivedExtendScalarsSubfield`,
  `derivedExtendScalarsToPadicAlgCl`, `derivedExtendScalarsCompIso`, and
  `constructibleToPadicAlgClCompIso` in the same namespace.
- Proof dependencies `def-sfb-dcons-subfield` and `def-sfb-dcons-qlbar` use
  `PadicSubfieldConstructible` and `PadicAlgClConstructible` from the same module.
- The Mathlib proof leaf `lem-weil-pbc-conjugate-iso-unit-equation` records
  `CategoryTheory.unit_conjugateEquiv_symm` in
  `Mathlib.CategoryTheory.Adjunction.Mates`, explicitly imported for the proof plan.
  Its uniqueness explanation is the adjunction Hom bijection; the ordinary
  extension comparison uses `Adjunction.leftAdjointUniq`.

The two project modules used by the statement are public imports; the Mathlib
proof-only module is an ordinary import. All other recorded proof-dependency
modules coincide with those imports, so none is missing and no import cycle is added.

The current server `TwoColimit` source was read using `scompile.py --source`.
Unlike the older attachment notes describing abbreviations through the finite
coefficient names, it currently writes the two extensions and comparison out
explicitly. These bodies still coincide with the finite coefficient definitions:
both comparison bodies are the inverse `leftDerivedFunctorCompIso`, followed by
`leftDerivedFunctorNatIso` of the same inverse `Mod.extendScalarsComp` and
`Mod.extendScalarsIsoOfEq` of `padicSubfieldRingObjMap_comp_toPadicAlgCl`.
The constructible comparison is the full-faithful cancellation of that ambient
comparison whiskered by the source inclusion. No dependency repair is needed.

Read the current blueprint source and the two construction proof files named in
the node, plus the existing `boundedConstructible` definition, coefficient maps,
finite-subfield-valued inclusion, and `Mod.extendScalarsComp` implementation.
The theorem docstring supplies the node's four proof steps, including unit
compatibility, equality of inverse components, and the restriction calculation.

### Searches and reuse

Searches were run through the prescribed `msearch.py`; exact queries/results are
also recorded in `searches.jsonl` in the sandbox.

- LeanFinder: “The canonical finite coefficient derived tensor comparison equals
  the scalar extension cocone comparison, including its forward and inverse
  components on bounded constructible subcategories”. Eight hits concerned
  light condensed internal projectivity and tensor direct limits; none states
  this agreement.
- Loogle: `CategoryTheory.Functor.fullyFaithfulCancelRight,
  CategoryTheory.Adjunction.leftAdjointUniq`. No hits for the combined query.
- LeanSearch: “The restriction of a natural isomorphism to a full subcategory
  has the same forward and inverse component morphisms”. Eight generic hits,
  including `ObjectProperty.isoMk`, `Adjunction.restrictFullyFaithful`,
  `NatIso.ofComponents.app`, and component-isomorphism results; no exact statement.
- Mathlib grep through `msearch.py`: `fullyFaithfulCancelRight|leftDerivedFunctorCompIso`
  in `CategoryTheory`. Ten hits include `Functor.fullyFaithfulCancelRight` and
  its `hom_app`/`inv_app` lemmas. These are the generic restriction proof tools,
  not equality of the two specified project comparisons.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `coefficient.*[Cc]ocone|finiteCoefficientDerivedTensorCompIso|derivedExtendScalarsCompIso|constructibleToPadicAlgClCompIso`
  found the recorded constructions and consumers. In particular,
  `Sheaf.Paper.CoefficientFiniteDescentHom` has private `tensorComp_hom` and
  `tensorComp_inv` lemmas giving the separate restricted equalities; neither
  declares the ambient equality or the complete node statement. Their private
  names are not a reusable public interface for this node. The archived
  `Sheaf/UpstreamExtra/.../TwoColimit.lean` also contains private versions.
- `rg` for the item id in `lean/WeilConjectures` found no declaration.
  `rg` for the proposed declaration name and comparison-agreement phrases in
  Mathlib/project name records and project source found no conflicting name.

No existing public declaration states this complete node; all existing notions
and maps are used directly. No private copy or helper notion is introduced.

### Edge cases and validation

Checked the statement and actual constructions for E = H (h may be reflexive),
E the base field, X empty, a zero complex, and a zero constructible object.
None requires a strict field inclusion, a nonzero object, or a nonempty scheme.
No chosen cohomological degree or amplitude truncation excludes shifts or the
zero case. The ambient equality applies to every unbounded derived object;
the restricted equalities quantify over every bounded constructible object.
The scheme universe is arbitrary `u`, and the sheaf coefficient universe remains
`u + 1` as in the dependency signatures. Every universe and variable is explicitly
bound; there are no local notations, local instances, auxiliary proofs, or definitions.

The prescribed server `scompile.py` compiled the sandbox and library module
successfully (6.2 s and 6.1 s respectively), with no errors or warnings.
There are no disputed statements, missing hypotheses, node faults, or statement
corrections. Delivery preflight is run after this report is written.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
