## Worker report

Bind the node to the existing definition
`AlgebraicGeometry.ProEtale.CondensedRing.openImmersionShriekIso` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`, lines 279–289.
No Lean module, new node, dependency repair, or statement correction is needed.
The live server source was read using `scompile.py --source` and agrees with the read clone.
The definition has real data, constructed by conjugation, with no `sorry` in its body.
This is a statement attachment, not a claim that its upstream dependencies are proved.

Source checked: the entire current blueprint node
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/` +
`sk-def-sfb-coefficient-comparisons/def-sfb-open-immersion-shriek-iso.md`.
Its statement agrees verbatim with the DAG statement. No repair note exists for this item.

Hypotheses and clauses, matched individually:

- The commutative condensed rings Λ and Λ' are
  `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}`, with
  `[MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']` in the upstream section.
  These are commutative ring objects in abelian condensed sheaves, as in the dependencies.
- The arbitrary coefficient-ring morphism is `(a : Λ ⟶ Λ') [IsMonHom a]`.
  There is no flatness, invertibility, finite-generation, or exactness assumption on a.
- The schemes and open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)` and
  `[IsOpenImmersion j]`. No separatedness, finiteness, or compactification is required.
- The coefficient changes a_X and a_U are `coefficientMap a X` and `coefficientMap a U`;
  the upstream definition is `(upperStarFromPoint X).map a`, respectively at U.
- The left functor `Ext_{a_X} ∘ j_!` is
  `(j)_!open⟦Λ⟧ ⋙ Mod.extendScalars (coefficientMap a X)`.
  Lean's `⋙` applies its left argument first.
- The right functor `j_! ∘ Ext_{a_U}` is
  `Mod.extendScalars (coefficientMap a U) ⋙ (j)_!open⟦Λ'⟧`.
- The source is exactly
  `Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)`;
  the target is exactly
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)`.
  These follow from the actual signatures of extension by zero and extension of scalars.
- The natural isomorphism is the `≅` between these functors, not merely an objectwise
  equivalence or an arbitrary chosen comparison.
- The input is precisely `comapUpperStarIso a j`, of type
  `(j)^*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a U) ≅`
  `Mod.comap (coefficientMap a X) ⋙ (j)^*⟦Λ⟧`.
  Thus it is `Res_{a_U} ∘ j^* ≅ j^* ∘ Res_{a_X}` in the node's orientation.
- The defining body is `(conjugateIsoEquiv adj₁ adj₂).symm (comapUpperStarIso a j)`.
  Here adj₁ is `(Mod.extendRestrictAdjunction (coefficientMap a U)).comp`
  `(openImmersionLowerShriekUpperStarAdjunction Λ' j)`; adj₂ is
  `(openImmersionLowerShriekUpperStarAdjunction Λ j).comp`
  `(Mod.extendRestrictAdjunction (coefficientMap a X))`.
  The two composite adjunctions have exactly the right-adjoint composites of the input
  and left-adjoint composites of the result. This matches the specified conjugate,
  including its direction and all four prescribed adjunctions.

Dependency declarations read and used:

- `sk-def-sfb-coefficient-change`: `AlgebraicGeometry.ProEtale.coefficientMap` and its
  section binders/docstring, in the same `ChangeOfCoefficients` module.
- `def-sfb-conjugate-pull-iso`: the recorded Mathlib match
  `CategoryTheory.conjugateIsoEquiv`, in `Mathlib.CategoryTheory.Adjunction.Mates`,
  including its `(L₂ ≅ L₁) ≃ (R₁ ≅ R₂)` signature and inverse construction.
- `def-sfb-comap-upper-star-iso`:
  `AlgebraicGeometry.ProEtale.CondensedRing.comapUpperStarIso`, in the same
  `ChangeOfCoefficients` module. Read its full signature, coefficient-square construction,
  and docstring; specialization to j gives exactly the conjugation input.
- `sk-def-sfb-module-lower-shriek`: in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, read the primary
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerShriek` and the relevant recorded
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction`.
  The open functor is the specified restriction along α_j followed by linear extension
  by zero; its adjunction is to the recorded module-object pullback.
- `sk-def-sfb-change-of-scalars`: `CategoryTheory.Mod.extendScalars` and
  `CategoryTheory.Mod.extendRestrictAdjunction`, in
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
  Read their full signatures, construction and docstrings: extension is the relative
  coequalizer/tensor and its adjoint is `Mod.comap`. No ordinary `ModuleCat` replacement.

Edge cases checked mathematically against the signature and construction: identity j,
identity a, empty U (including empty X), zero modules and the zero coefficient ring all
remain admitted. Arbitrary non-flat coefficient maps are admitted, e.g. the constant
condensed map Z → Z/2; the construction uses underived adjunctions and requires no flatness.
The universe u is arbitrary and the `Ab.{u + 1}` / `Scheme.{u}` convention is the same as
all recorded dependency interfaces; no extra equality of site universes is introduced.

Searches made on 2026-10-21:

- `msearch.py ... leansearch "Extension of scalars commutes with extension by zero for
  sheaves of modules"`: eight hits, ordinary ModuleCat extension/adjunction and
  SheafOfModules sheafification/restriction lemmas; no full project-specific comparison.
- `msearch.py ... leanfinder "Extension of scalars commutes with extension by zero along
  an open immersion for condensed module sheaves"`: eight hits, including
  `LightCondensed.free`, internal-Hom and Scheme.Modules restriction lemmas; no full match.
- `msearch.py ... loogle "CategoryTheory.conjugateIsoEquiv"`: five hits, the conjugation
  equivalence and its hom/inv equations; these supply the generic dependency only.
- `msearch.py ... grep "openImmersionShriekIso|extendScalars.*[Ss]hriek|[Ss]hriek.*extendScalars"`:
  zero Mathlib hits.
- `rg` of that same pattern in `lean/WeilConjectures` and `lean/Sheaf`: exact definition
  found at ChangeOfCoefficients.lean:281, alongside its documentation and existing
  consumers; the derived sibling has a different statement. The Sheaf consumers use
  this upstream name, confirming that no second definition should be introduced.
- `rg -n "def-sfb-open-immersion-shriek-iso" lean/WeilConjectures`: no blueprint-ID hits;
  the exact declaration is found by name as above.

No statement dispute or node fault was found. Only the item's `lean` field is changed.
Server compilation of the existing declaration is performed by deliver2.py's generated
`#check @AlgebraicGeometry.ProEtale.CondensedRing.openImmersionShriekIso` probe.

## Second reading by Q133

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
