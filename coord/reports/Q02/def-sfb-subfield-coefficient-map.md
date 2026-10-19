## Worker report

Recorded the exact existing declaration
`AlgebraicGeometry.ProEtale.padicSubfieldRingObjMap` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
No module is delivered: the existing definition has real data and must not be duplicated.
Only the item's `lean` field changes. No new nodes, dependency repairs, or statement
corrections are needed. No repair note exists for this item.

Source: current blueprint `main-20261015`, chapter `sec-proetale-coefficients`, unit
`sk-prop-sfb-cartesian-coefficients`, file `def-sfb-subfield-coefficient-map.md`.
I read the complete node and all three statement dependencies, their recorded bindings
or closed upstream audit, and the actual declarations and docstrings. The 51-module
framework described in `coord/pefw-upstream-framework.md` supplies the source missing
from the older local slopmaster2 checkout. I also used `scompile.py --source` to read
the current published Compatibility, ChangeOfCoefficients, Basic, and
Condensed.FiniteSubextension modules. The relevant construction is unchanged there.

Hypothesis and clause correspondence:

- A prime ell is the section parameter `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite extensions E and F of Q_ell inside its algebraic closure are
  `{E F : PadicAlgCl.FiniteIntermediateField ℓ}`. In RingObjects.EllAdic this type
  is `{E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) // FiniteDimensional ℚ_[ℓ] E}`.
  Thus finiteness and the fixed embeddings are actual data in the parameter type.
- Inclusion E ≤ F is `(h : E ≤ F)`, using the inherited intermediate-field order.
- An arbitrary scheme X is the section parameter `(X : Scheme.{u})`; `universe u`
  is explicit in the source. There is no condition on its characteristic, size,
  connectedness, nonemptiness, or properness.
- The source E_X and target F_X are exactly
  `padicSubfieldRingObj X ℓ E` and `padicSubfieldRingObj X ℓ F`.
  Each is an abbreviation of `condensedRingObj (Profinite.continuousMapRingObj E) X`
  (respectively F), hence `(upperStarFromPoint X).obj` of the condensed field.
- The map is exactly `coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X`,
  the full body of the existing abbreviation. The latter point map is the
  underlying abelian-sheaf arrow of `padicSubfieldCondensedRingMap ℓ h`, defined
  using `IntermediateField.inclusion h` and postcomposition of continuous maps.
- `coefficientMap a X` is exactly `(upperStarFromPoint X).map a`. Thus the
  definition applies p_X^* to the specified inclusion, not an arbitrary arrow.
- This is a morphism of ring objects: the condensed inclusion has `IsMonHom`;
  Mathlib's `CategoryTheory.Functor.map.instIsMonHom` preserves it under the
  monoidal inverse image. The transported structures are the same structures
  supplied by the dependency `coefficientRing` through `Functor.mapMon`, whose
  underlying map is `F.map f.hom`. The unbundled encoding is used by the existing
  coefficient-map dependency. Opening its `CategoryTheory.Obj` and
  `CategoryTheory.Functor` scopes exposes the required structures to synthesis.

Dependencies used:

- `def-sfb-coefficient-map`: `AlgebraicGeometry.ProEtale.coefficientMap`, module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.
- `sk-def-sfb-pulled-back-coefficients`: `AlgebraicGeometry.ProEtale.coefficientRing`,
  `condensedRingObj`, and `isCommMonObj_condensedRingObj`, module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `def-sfb-qlbar-subextension-map`: `Profinite.padicSubfieldRingObjMap`, module
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`.
  This dependency has no `lean` record, but its closed slopmaster2 audit names
  this exact declaration; no duplicate or dependency-record change is needed.

Edge cases checked before recording: E = F is allowed, and the point inclusion
is the identity (`Profinite.padicSubfieldRingObjMap_id`); inverse image preserves
that identity (`coefficientMap_id`). For E ≤ F ≤ H, the point inclusions and
coefficient change are functorial (`Profinite.padicSubfieldRingObjMap_comp`,
`coefficientMap_comp`). These checks verify the canonical direction and choice
of map. The bottom intermediate field Q_ell is a finite intermediate field.
The empty scheme is admitted because X has no extra hypothesis; every scheme
characteristic is admitted, independently of ell. The result lives in
`Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}`, matching the dependency convention.

Searches actually run via `msearch.py` (complete outputs are in searches.jsonl):

- LeanFinder: "Pull back the condensed ring inclusion between finite p-adic
  subextensions to coefficient rings on the pro-etale site of a scheme".
  Eight hits: BDeRhamPlus, BDeRham, Condensed.profiniteSolid, a transition-limit
  construction, and etale-category declarations; none define this coefficient map.
- Loogle: `"padicSubfieldRingObjMap"`; successful search, zero hits.
- Mathlib grep: `padicSubfieldRingObjMap|padic.*[Ss]ubfield|coefficientMap`;
  successful search, zero hits.
- LeanSearch: "Pullback of condensed ring inclusion for finite extensions of
  p-adic numbers on a pro-etale scheme". Eight hits on scheme pullbacks,
  PadicInt.Coe.ringHom, ring pullbacks and RingCon.comap; none match the node.
- `rg -n 'padicSubfieldRingObjMap'` and the requested node-id grep in the older
  slopmaster2 WeilConjectures source: no hits. The upstream-name table also has
  no hit. In the published side framework, Compatibility.lean contains the
  exact declaration (section RingObj); I read its entire signature and body.
- `rg` in `lean/Sheaf` found consumers in CondensedCoefficientComparisons and
  CondensedFlatCoefficientCalculus, not a competing definition. Their uses
  confirm that the canonical map is the published upstream construction.

Validation uses only the authorized scompile.py wrapper. A scratch-only probe
imports the existing Compatibility module, checks the fully parameterized arrow
and its exact condensedRingObj endpoints, synthesizes its IsMonHom structure,
and checks the existing identity/composition signatures. The first probe omitted
the source's scoped instances and failed MonObj synthesis; I added the source's
`open scoped CategoryTheory.Obj CategoryTheory.Functor` and reran it. No live
source or dependency was changed. The corrected probe passed both wrapper checks
(sandbox 3.2 seconds, library check 2.2 seconds), without errors or warnings.
The probe is not a delivered module.

No statement is disputed. The open upstream proof frontier remains open;
recording this real definition does not claim that its dependencies are proved.

## Second reading by Q02

I reread the node against the published declaration and all relevant section
parameters. This is a worker self-check; the dispatcher forbids spawning another
agent, and the maintainer supplies the independent review after delivery.

The source takes exactly X, ell with primality, finite subfields E and F, and
an inclusion h. Its endpoints are exactly the pulled-back condensed rings and
its body is exactly coefficientMap of their condensed inclusion. The ring-object
clause is present through the existing scoped MonObj/IsMonHom instances, not an
extra hypothesis. No hypothesis or clause is missing or strengthened. The source
and target abbreviations expand to the dependency definitions. I kept the
signature verbatim, including its line break and implicit E/F binders; section
parameters are documented in lean.note. No mismatch was found and no natural
statement changed. The scratch probe's missing scoped imports were corrected.
