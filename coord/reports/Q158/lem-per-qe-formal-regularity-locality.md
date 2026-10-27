## Worker report

The module `Sheaf.AlgebraicGeometry.QEFormalRegularityLocality` states the nine parts of
`lem-per-qe-formal-regularity-locality`. Every theorem has proof `by sorry`; no mathematics
is proved and no definition is added. Its principal declaration is
`AlgebraicGeometry.qeFormal_regularity_locality`.

Source checked: Temkin, *Functorial desingularization of quasi-excellent schemes in
characteristic zero: the non-embedded case*,
https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf,
§§2.4.3, 2.4.9, 2.4.12, Lemma 2.4.6 and §§3.1.1, 3.1.4 (printed pp.14–18).
The current blueprint ancestor is `lem-per-artin-gabber-affine-curve`, reached through
the formal-resolution branch specified in the item's blueprint record.

Hypotheses and clauses, read against the node:

- A Noetherian adic formal scheme is the existing `IsNoetherianAdicFormalScheme X`:
  a finite cover by `IsAdicFormalAffineOpen X U`, whose coordinate ring is Noetherian,
  complete and separated for a finitely generated ideal. `adicFormalSpec` constructs
  the spectrum from the inverse system of infinitesimal closed thickenings. The points,
  inverse-limit sheaf and completed principal restrictions are the existing framework,
  not new data or a new formal-spectrum definition.
- Work over Q is `_qX : X ⟶ (Spec (CommRingCat.of (ULift.{u} ℚ))).toRingedSpace`,
  and similarly for Y and Z. A morphism need not be specified over Q or compatible with
  chosen coefficient fields; those compatibility assumptions are not introduced.
- Quasi-excellent chart rings use `IsQuasiExcellentAdicFormalScheme X`, defined with the
  dependency's `IsQuasiExcellent`. `quasiExcellentAdicFormal_cover_iff` says this can be
  checked on any formal open cover `U : ι → Opens X`, `iSup U = top`. The indexing
  universe v is independent of u: arbitrary covers, including the empty cover, are allowed.
- Reduced complete chart rings use `IsReducedAdicFormalScheme`. Regular complete chart
  rings use the existing Mathlib `IsRegularRing` under universal quantification over
  `IsAdicFormalAffineOpen`. Both cover-independence equivalences are in
  `qeFormal_reduced_regular_cover_iff`. The local rings are not substituted for complete
  chart rings.
- The radical nonregular ideal is the existing `absoluteSingularIdeal A`, the vanishing
  ideal of primes at which `Localization.AtPrime` is not `IsRegularLocalRing`.
  `qeFormal_affine_restriction` states both regularity of the actual sheaf restriction
  ring hom and `Ideal.map restriction (absoluteSingularIdeal A) = absoluteSingularIdeal B`.
  Thus it states compatibility of ideals, not only equality of their zero sets.
- `qeFormal_singularIdeal_gluing` asserts a unique `J : FormalIdeal X` with `J.IsCoherent`
  and its exact completed-ideal identification on every complete Noetherian chart,
  transported by the chart isomorphism and the canonical open immersion. The RHS is
  `completedFormalIdeal (Spec A) (affineFormalIdeal A K)
  (affineFormalIdeal A (absoluteSingularIdeal A))`. No arbitrary ideal or map stands in
  for the actual completed singular ideal. Finite generation of K follows from
  Noetherianity. Uniqueness is of the ideal, not of the coherence proof.
- Regular morphisms use `IsRegularOnAdicFormalAffines f` and the existing
  `adicFormalAppLE f U V e`. Its regular ring map predicate `RingHom.IsRegular` is
  precisely flatness with Noetherian geometrically regular residue-field fibres.
  `qeFormal_regularity_locality` equates this all-affine-pairs condition with existence,
  about every source point, of a compatible regular affine pair. This is equivalent to
  the covering definition and gives locality on source and target. For an empty source,
  the covering criterion is vacuous, as it should be; unused target charts can be added.
  `_hf` requires local stalk maps: the node says morphism of formal schemes, not an
  arbitrary ringed-space map. This is part of the meaning of that object. Continuity
  in the ideal topologies is automatic here: at every formal point, locality sends
  target topologically nilpotent elements into the source prime. Hence the image of
  an ideal of definition is in the radical of a source ideal of definition, and finite
  generation gives a power containment. This imposes neither adicity nor finite type.
- `qeFormal_openImmersion_regular` uses `SheafedSpace.IsOpenImmersion` and concludes the
  all-affine-pairs regularity predicate. `qeFormal_regular_comp` states the same for
  `g ≫ f`. The local-stalk hypotheses on f and g express formal morphisms as above.
- `qeFormal_regular_finite_disjoint_union` describes actual finite unions by open
  embeddings a, b with disjoint covering images and component squares
  `b i ≫ f = g i ≫ a i`. Regularity of every g i implies regularity of f.
  The number n may be zero, so the empty union is included. No selected coproduct
  object or noncanonical map is substituted for f.
- For a reduced formal pair, `qeFormal_open_subpair` uses the existing
  `NoetherianAdicFormalScheme`, its distinguished `ideal`, `ideal.IsInvertible`,
  `IsReducedAdicFormalScheme`, and chartwise positive-power containment in
  `absoluteSingularIdeal`. Invertibility means local generation by a non-zero-divisor,
  not merely by an arbitrary principal element.
- Every `U : Opens X.space` yields a Noetherian formal pair Y and an isomorphism to the
  actual open restriction. Its ideal is exactly the extension along that inclusion.
  It is reduced, quasi-excellent, invertible and has the same positive-power singular
  containment on every chart. Its coherent distinguished ideal and ideal-of-definition
  condition are fields of the returned `NoetherianAdicFormalScheme`.
- The last implication in that theorem says `IsCompact U` and
  `HasFormalVarietyClosedFibre X.space X.ideal` imply the same predicate for Y. That
  existing predicate means an actual reduced closed-fibre scheme, with homeomorphic
  underlying space, surjective stalk maps and radical kernel, and a structure morphism
  to a characteristic-zero field that is `LocallyOfFiniteType` and `QuasiCompact`.
  It therefore renders exactly the finite-type reduced-closed-fibre clause.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, `IsExcellent`; the former is
  Noetherian plus G-ring plus J-2. No duplicate excellent-ring definition.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  with ring clauses furnished by Mathlib `IsRegularLocalRing`, `IsRegularRing` as the
  dependency's record specifies. The present theorem uses those ring clauses.
- `WeilConjectures.RingTheory.GRing`: `Algebra.IsGeometricallyRegular`,
  `RingHom.IsRegular`, `IsGRing`, including the Noetherian fibre condition.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- Added existing statement dependencies `def-per-adic-formal-geometry`,
  `def-per-formal-completion-geometry`, `def-per-rig-regular-formal-pair-geometry`:
  their modules are `Sheaf.AlgebraicGeometry.AdicFormalGeometry`,
  `Sheaf.AlgebraicGeometry.FormalCompletionGeometry`, and
  `Sheaf.AlgebraicGeometry.RigRegularFormalGeometry`. Their signatures and full docstrings
  were opened. They supply all formal spaces, maps, singular ideals, formal ideals,
  distinguished pairs, charts and reduced-closed-fibre predicates used above. These are
  already landed nodes, so no new notion or dependency repair is needed. A dependency
  traversal checked that adding them creates no cycle.

All currently recorded proof-dependency modules are imported without `public`.
The Mathlib leaves have their corresponding Mathlib imports. The genuine theorem
`lem-per-gabber-adic-quasi-excellence` has no Lean record or Mathlib match in the read
repository, so it has no import to add; it is a proof dependency only and not needed to
state this item. No import of an unstated theorem or private restatement was introduced.

Edge cases checked before writing: empty formal scheme; empty cover; empty open; n=0
finite unions; K=0 (ordinary schemes); K=top (complete ring must be zero); nilpotent
ideals of definition; field charts (unit singular ideal, empty singular locus); regular charts with empty
singular locus; nonprincipal invertible ideals (no global generator is required);
formal morphisms not of finite type and not adic; open subpairs without a chosen field;
arbitrarily large open-cover indexing universe. All remain in the statements.

Searches for an existing statement:

- msearch LeanSearch, `Quasi excellent adic formal schemes regular morphisms affine covers
  singular ideals`: eight hits on ordinary affine covers and scheme quasi-separatedness;
  no formal regularity locality or singular-ideal gluing theorem.
- msearch LeanFinder, `regular morphisms quasi excellent adic formal schemes singular ideal
  locality`: eight hits on smooth/etale loci and ordinary smooth morphisms; none matches.
- msearch Loogle, `IsRegularOnAdicFormalAffines, IsQuasiExcellent, RingHom.IsRegular`:
  zero hits, unknown identifier `IsRegularOnAdicFormalAffines` in its Mathlib index.
- msearch grep, `FormalScheme|formal spectrum|IsRegularOnAdic`, AlgebraicGeometry:
  zero hits in Mathlib. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` found the
  existing formal definitions listed above and regularity of completed ordinary
  morphisms, but not this general locality theorem. Direct search for the item's id
  and every proposed theorem name in both roots and `dag/lean_names_upstream.json`
  found no duplicate declaration. Blueprint search `formal regularity` found no unit.

No statement correction and no disputed statement. Only lean and the authorized
addition of already landed notion nodes to stmt_deps are changed.

## Second reading by Q158

Read the item and finished Lean file again within this worker session; the dispatcher
forbids starting another agent, so this is a separate self-review, not a claimed
independent agent review. The maintainer performs the independent delivery review.
Matched each clause with the declarations above. The first draft indexed covers by
`Type u`; changed to independent `Type v` so no indexing case is excluded. Verified
that the singular gluing conclusion identifies ideals on every chart, that the
regularity criterion is pointwise in both source and target, that local stalk maps
are part of formal morphisms rather than an adicity restriction, and that the open
subpair returns the actual restricted ideal. Read the finite-type fibre predicate's
surjective-stalk and radical-kernel conditions, rather than treating it as an arbitrary
finite-type scheme. There is no hollow definition, additional finite-type morphism
hypothesis, or global generator requirement. Each theorem docstring contains its
corresponding steps of the node's ten-step proof. Every variable and universe is
explicitly bound; autoImplicit and relaxedAutoImplicit are disabled.

Validation: scompile.py compiled the file both under its sandbox name and its library
module name, with no errors or warnings. Delivery dry-run and final push follow.
