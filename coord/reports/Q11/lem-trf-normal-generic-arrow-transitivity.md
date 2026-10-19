## Worker report

Item: `lem-trf-normal-generic-arrow-transitivity`. Delivery contains one module,
`Sheaf.TraceFormula.NormalGenericArrowTransitivity`, one node copy changed only in `lean`,
and this report. The natural-language statement, dependencies and reviewed stage-1 split
are unchanged. The earlier worker's “assignment superseded” referred to the stage-1 split;
this delivery supplies its missing stage-2 statement and does not split the reviewed node.
No repair note for this item exists in `coord/repair-notes`.

The module provides one canonical helper,
`AlgebraicGeometry.Scheme.genericGeometricPointDirectImage`, and one postponed theorem,
`AlgebraicGeometry.Scheme.normal_generic_arrow_transitivity`. The helper has actual data:
the residue-field embedding gives the scheme map
`Spec.map (CommRingCat.ofHom (algebraMap (N.residueField η) Ω)) ≫ N.fromSpecResidueField η`,
and `pointSmallEtale` followed by Mathlib's `skyscraperSheafFunctor` supplies its direct
image. This merely names the canonical expression belonging to this item's geometric
generic point; it introduces no independent notion. In particular it does not choose an
arbitrary geometric morphism or a right adjoint from an existence theorem. Its two public
declarations are listed in `lean.declarations`.

Clause-by-clause comparison:

| Node clause | Lean rendering |
| --- | --- |
| Integral scheme N, with no finiteness assumption | `{N : Scheme.{u}} [IsIntegral N]` |
| Every local ring is an integrally closed domain | `hN : ∀ x : N, IsDomain (N.presheaf.stalk x) ∧ IsIntegrallyClosed (N.presheaf.stalk x)` |
| η is its generic point | `(η : N) (hη : IsGenericPoint η Set.univ)` |
| K is κ(η) | Every occurrence is literally `N.residueField η`; no independent or unrelated field K is introduced |
| Choose any algebraic closure with its specified field embedding | `(Ωη : Type u) [Field Ωη] [IsAlgClosed Ωη] [Algebra (N.residueField η) Ωη] [Algebra.IsAlgebraic (N.residueField η) Ωη]` |
| The resulting geometric generic point | The spectrum of that algebra map followed by `N.fromSpecResidueField η`, inside `genericGeometricPointDirectImage N η Ωη` |
| Any geometric point n | `{Ωn : Type u} [Field Ωn] [IsAlgClosed Ωn] (n : Spec (.of Ωn) ⟶ N)`; Ωn need not be algebraic over its residue field |
| Points of the small étale topos | `pointSmallEtale` on those two scheme maps, with sheaves on `N.smallEtaleTopology` |
| Arrows defined on direct images | Natural transformations between their `skyscraperSheafFunctor (A := Type (u + 1))` right adjoints |
| The Hom set is nonempty | First conjunct `Nonempty (genericGeometricPointDirectImage N η Ωη ⟶ (pointSmallEtale n).skyscraperSheafFunctor ...)` |
| Every pair of arrows a,b is conjugate by a source automorphism | Second conjunct `∀ (a b : ...), ∃ σ : Aut (genericGeometricPointDirectImage N η Ωη), a = σ.hom ≫ b` |
| Right action is precomposition, target fixed | For an arrow a and automorphism σ, the action is `σ.hom ≫ a`; `≫` writes categorical composition in diagrammatic order, so the asserted equation is precisely a = b ∘ σ |
| No uniqueness or free-action assertion | `∃ σ`, not `∃! σ`; no injectivity or freeness hypothesis/conclusion |
| No Noetherian hypothesis | No Noetherian, quasi-compactness, separatedness, finite-type or excellence binder |

The right-action identity and associativity are already the categorical identity and
associativity laws for these natural transformations. With the usual `Aut` multiplication,
`(σ * τ).hom = τ.hom ≫ σ.hom`, so `(a · σ) · τ = a · (σ * τ)` for this convention.
No separate action structure with a different multiplication is substituted.

Dependency declarations read and used:

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsIntegral`. Its nonempty/domain-on-nonempty-opens definition is used.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`, meaning
  `closure {η} = Set.univ` here. The generic point is explicitly quantified.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField`, `Scheme.fromSpecResidueField` and `Scheme.SpecToEquivOfField`.
  The helper uses the latter equivalence's actual inverse formula, read in its source.
- `def-weil-algebraic-closure`: its Mathlib match includes
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed` and `IsAlgClosure`.
  The two properties of `IsAlgClosure` are spelled out as algebraic closedness and
  `Algebra.IsAlgebraic`. This allows every chosen closure, not just `AlgebraicClosure K`.
- `def-weil-geometric-point`: the recorded inline algebraically closed field and spectrum
  map, as above, using `IsAlgClosed` and the scheme residue-field API.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `Scheme.smallEtaleTopology` and `Scheme.Etale`, exposed by `Sites.EtalePoint`.
- `def-trf-geometric-morphism`: `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`, whose `direct` is a functor and whose 2-morphisms
  are natural transformations. Mathlib's
  `CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction` identifies the
  actual direct images used here as right adjoints to the corresponding geometric stalks.

The module imports the recorded, stated proof dependencies privately, including the
strict-henselization, étale-triples, normal local-colimit, ind-étale, and residue-separability
modules. The Mathlib algebraic-embedding match `IsAlgClosed.lift` is supplied by the already
public algebraic-closedness import. `lem-trf-point-arrows-strict-local-lifts` has no Lean
record yet and therefore has no proof-only import: its statement is not needed to type
this theorem. The declaration docstring preserves every one of the seven node proof
steps, including the injectivity and finite-root-set surjectivity arguments and the
strict-local arrow correspondence, so stage 3 retains that prerequisite. No incomplete
auxiliary theorem is delivered, and no dependency wait is introduced.

Source check: opened Orgogozo's PDF at the source URL in the node, PDF page index 17,
printed p. 18, Lemma 8.3.2 and its proof. The normal-base assertion is transitivity of
Aut(s′) on Hom(s′,t′), with the generic source fixed as in the node. Also read the local
Stacks `etale-cohomology.tex`, section `section-specialization` (Tag 0GJ2), for the
direction of the stalk mate. No statement fault or correction is needed.

Edge cases checked mathematically:

- The empty scheme is excluded exactly by `IsIntegral`; it is not an omitted allowed case.
- For N = Spec K, geometric point arrows are the expected field-point specializations;
  the generic source need not have a uniquely acting automorphism.
- The target may lie over η, a closed point, or any intermediate point, and may use an
  arbitrarily large algebraically closed residue-field extension within the ambient
  scheme universe; there is no Ωn/κ(n) algebraicity condition.
- For a normal trait the stabilizer can be nontrivial, so replacing the existential
  automorphism by a unique one would be wrong. No such replacement is made.
- Positive characteristic, inseparable minimal polynomials, and non-Noetherian normal
  domains are all retained. The proof plan uses distinct roots, not separability, in its
  automorphism-surjectivity step.
- Universe `u` is explicit and arbitrary; geometric fields and schemes share the ambient
  universe as in the recorded geometric-point and small-étale-site APIs. Set sheaves use
  `Type (u + 1)` and the full natural-transformation Hom, not a finite-étale subcategory.

Searches made in this work:

- `msearch.py`, leanfinder: “On a normal integral scheme automorphisms of the geometric
  generic topos point act transitively on specialization arrows to a fixed geometric
  point”. Eight hits: ordinary Zariski specialization/range-from-stalk facts,
  `Scheme.SpecToEquivOfField`, and the integral-scheme order-top instance. No theorem of
  transitivity on étale topos point arrows.
- `msearch.py`, loogle: `"pointSmallEtale", "skyscraperSheafFunctor"`. Zero hits.
- `msearch.py`, grep in AlgebraicGeometry:
  `generic.*transitiv|transitiv.*generic|normal_generic_arrow_transitivity`. Zero hits.
- `rg` of the upstream source, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `genericGeometricPointDirectImage|normal_generic_arrow_transitivity`: zero hits.
  Earlier searches for `etaleGeometricPoint` returned only the unrelated
  `etaleGeometricPointSectionsStalkNatural` and its consumer.
- `grep -rn` of upstream `WeilConjectures` for this item's DAG id: zero hits.
- Read Mathlib `Sites/EtalePoint.lean` and `Sites/Point/Skyscraper.lean` directly.
  They already supply the geometric point, canonical right adjoint, and adjunction;
  those constructions are reused, not recreated.

Validation: the prescribed `scompile.py Q11 lem-trf-normal-generic-arrow-transitivity`
compiled the one delivered module at both the sandbox and final library paths, with exit
code 0 and no diagnostics. The declaration proof is exactly `sorry`; the helper has real
data, no auto-bound variables or universes, and every line is at most 100 characters.
The final dry run and push use `deliver2.py`. No independent worker is claimed to have
reviewed this delivery; the maintainer's independent review follows direct delivery.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
