## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.LocalProjIsomorphismCompatibility`.
There are four named theorems, each with its whole proof postponed by `sorry` and
with the relevant natural-language DAG proof in its docstring. The three helper
definitions contain actual expressions and no postponed data. No statement
correction or dependency repair was needed. The item's only changes are its
`lean` record and the added statement dependency named below.

Hypotheses and clauses, matched against the node:

- A scheme S is the explicitly universe-bound `S : Scheme.{u}`. The two
  commutative unital graded quasi-coherent algebra sheaves are
  `A B : RelativeProjAlgebra S`. This is the retained sheaf input of the
  relative-Proj dependency, containing the underlying `QuasiCoherentAlgebra`,
  homogeneous module sheaves, `GradedSheafAlgebra` and the compatible direct-sum
  identification. In particular A_0 is not required to equal O_S.
- The relative Proj schemes, structure maps and specified i_U are
  `A.realization.proj`, `A.realization.π` and `A.realization.restrictionIso U`,
  and similarly for B. The realization is the existing explicit bridge to
  `A.affineData.relProj` and `relProjHom`; it chooses no extra gluing datum.
- An affine U is `U : S.affineOpens`. A graded O_U-algebra isomorphism beta is
  `β : LocalGradedIso A B U`, recording its inverse graded section maps on
  every affine refinement of U. It is local on U; no global algebra
  isomorphism on S is assumed. The actual section rings are `A.sections U`
  and `B.sections U`; their gradings are `sectionGrade`.
- `exists_unique_localProjComparison` asserts unique existence (`∃!`) of the
  scheme isomorphism between the inverse-image open subschemes of the two
  canonical relative Proj schemes. `IsLocalProjComparison` states all its
  defining properties. `localProjChartMap` conjugates its hom by the specified
  i_U. The first conjunct, `localProjChartMap r ≫ A.localBase U = B.localBase U`,
  makes it a U-isomorphism under those identifications.
- For every `d`, `f`, `hf : f ∈ A.sectionGrade U d`, `0 < d`, the second
  conjunct is the precise inverse-image equality of D_+(f) with D_+(beta(f)).
  The third conjunct says the map on the affine charts is
  `Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ... f))`,
  using `Proj.awayι` for the standard affine identifications. Thus the chart
  ring is the dependency's actual `HomogeneousLocalization.Away`.
- The last conjunct of `IsLocalProjComparison` takes the supremum of the
  inverse-image standard opens over all positive-degree homogeneous f and
  asserts it equals top. This is exactly the required cover.
- The final conjunct of `exists_unique_localProjComparison` gives the
  fraction formula explicitly using `Away.mk` and `Away.map`: a/f^m goes to
  beta(a)/beta(f)^m. For natural-number grading, `m • d` is `m*d`. Its
  positivity hypothesis matches the chart clause; m is unrestricted.
- `localProjComparison_inverse` says the inverse scheme isomorphism satisfies
  the same complete chart specification for `β.symm`. Combined with the
  unique-existence theorem applied to B,A this says precisely that its inverse
  is the comparison of beta-inverse.
- `localProjComparison_restrict` quantifies every affine `V` and `h : V ≤ U`.
  For any chart-specified r and rV (the latter for `β.restrict V h`), its first
  two equations state compatibility with the actual open-subscheme inclusions
  in both directions. Its last equation is coefficient restriction of each
  beta(a)/beta(f)^m to rho_B(beta(a))/rho_B(beta(f))^m. The identification with
  beta_V(rho_A(a))/beta_V(rho_A(f))^m is the `hom_naturality` field of beta;
  inverse naturality is recorded as well. V=U is retained.
- `localProjComparison_degreewise_unit` takes an actual base unit
  `v : Γ(S,U.1)ˣ`, a second local graded algebra isomorphism beta', and exactly
  the degreewise relation for every k ≥ 0 and a in degree k. The base unit is
  mapped by the structural `algebraMap` into B, rather than identifying B_0
  with the base. Its first equations are equality of r',r and their inverses;
  its next clause is equality of the common D_+ charts.
- The next clause supplies the actual canonical ring equivalence `e` between
  the two degree-zero homogeneous chart rings. Its value on every fraction
  b/beta'(f)^m is specified by `unitAdjustedChartFraction` in the ordinary
  localization at beta(f). Thus the map is determined on all elements; no
  arbitrary comparison is chosen. The equality of ring homomorphisms
  `e.toRingHom.comp (Away.map beta' f) = Away.map beta f` states equality
  of the chart maps under this precise identification.
- Its last two equalities are the specified three-term fraction calculation
  on the common chart. `unitAdjustedChartFraction B U v d m b g` represents
  b/(v^d*g)^m in the ordinary localization B_g using the inverse
  v^(-d)*g^(-1). Substitute b=beta'(a), then b=v^(m*d)*beta(a), and obtain the
  value of `Away.map beta f (Away.mk ... a ...)`. The homogeneous localization
  embeds injectively into this ordinary localization (`val_injective`), so
  this is equality of the chart's degree-zero fractions, not a comparison in
  a quotient that loses information. There is no inverse or cancellation
  assumption on f; its image is inverted only by localization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`.
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`:
  `GradedSheafAlgebra`, including the multiplication, restriction, unit and
  associativity/commutativity laws, through `RelativeProjAlgebra.graded`.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `Scheme.IsQuasiCoherentAlgebra`, `QuasiCoherentAlgebra`, through
  `RelativeProjAlgebra.algebra`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`:
  `Scheme.GradedAlgebraData`, its `Hom`, `relProj`, `relProjHom`, `relProjι`,
  `relProjRestrictIso`, and the affine restriction naturality equations.
- `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction`:
  `RelativeProjAlgebra.affineData`, `gradeIso`, `affineRestrictionIso`,
  `realization`, and the existing `RelativeProjAlgebra`/`RelativeProjData`
  interfaces it publicly imports. These are the multiple modules recorded
  by the relative-Proj dependency, rather than a private construction.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `Away`, `Away.map`, `Away.mk`, `Away.map_mk`, `Away.mk_surjective` and
  `val_injective`. `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` and
  `Functor`: `Proj`, `Proj.basicOpen`, `Proj.awayι`, `Proj.basicOpenIsoSpec`.
- Proof imports are the recorded scalar-extension theorem
  `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension` and Mathlib
  scheme gluing (`Scheme.OpenCover.glueMorphisms`, `hom_ext`). The other
  recorded proof dependencies' modules are already public statement imports.

Edge cases checked before and after writing:

- Empty S or U, zero algebra sheaves, no positive components: the Proj is
  empty, the supremum is bottom=top on that empty scheme, and the unique
  empty-scheme isomorphism is admitted. No nonempty or nontrivial binder.
- f=0 and nilpotent f give zero localization rings/empty charts. The chart
  formulas still make sense. For f=2x in (Z/6)[x], the denominator is a zero
  divisor; every expression still uses ordinary localization, never ring
  cancellation. Numerator 0 and exponent m=0 remain allowed.
- u=1 and degree k=0 give the expected identity factors. For the degreewise
  scaling check, m*d=d*m and (u^d)^m=u^(d*m), so only unit powers cancel.
- Nontrivial A_0 over the base, e.g. R[t] placed in degree zero with a
  positive polynomial generator, is admitted. No finite generation,
  degree-one generation, integrality, reducedness or separatedness condition.
- Affine V=U and arbitrary affine V≤U are both admitted. The local-isomorphism
  interface never assumes intersections of affine opens are affine. The
  source and coefficient rings all live in the scheme's ordinary universe u;
  there is no equality imposed on independent site universes.

Searches for an existing item statement:

- `msearch.py leanfinder`: “A graded algebra sheaf isomorphism gives inverse
  relative Proj maps compatible with affine restriction and unchanged by
  multiplying degree k by a base unit to the kth power”. Eight hits, including
  `projIsoSpec`, `basicOpenIsoSpec_inv_ι`, and pullback chart lemmas. None
  includes local graded sheaf isomorphisms and degreewise unit invariance.
- `msearch.py loogle`: `AlgebraicGeometry.Proj.map`. Nine hits including
  `map_comp`, `map_preimage_basicOpen`, `awayι_comp_map` and `ι_comp_map`;
  all are used by or support the chart construction, but none is this result.
- `msearch.py leansearch`: “Local Proj isomorphisms commute with restrictions
  and degreewise unit rescaling”. Eight hits, mostly the Proj affine charts,
  with no full match.
- `msearch.py grep`: `Proj.*(unit|scal|restrict)|(unit|scal|restrict).*Proj`
  in `AlgebraicGeometry/ProjectiveSpectrum` returned five lines in Scheme.lean
  about restrictions. Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf`
  found no occurrence of this item id. Concept searches found and led me to
  read `RelativeProj/Functoriality.lean`: its existing `relProjIsoOfIso` is
  global on S, not the local-U statement with unit invariance. The
  `def-sfb-relative-proj-iso-of-graded-iso` node binds that global definition;
  it does not supply this theorem. No existing declaration was duplicated.

Validation: both delivered modules have compiled separately, in dependency
order, through `scompile.py` against the live published library. Final dry-run
and delivery results are recorded by the delivery wrapper. All theorem proofs
are `sorry`; definitions contain real data. There is no statement dispute.

## New nodes

`def-trf-local-graded-algebra-iso` owns
`Sheaf.AlgebraicGeometry.LocalGradedAlgebraIso`, with the structure
`RelativeProjAlgebra.LocalGradedIso`, its explicit inverse `symm`, and affine
`restrict`. Source: Stacks Constructions Tags 01MY and 02NC, the local graded
algebra identifications and their restrictions used before gluing Proj maps.
It is an isomorphism of the restricted sheaves given on the affine basis;
the forward and backward maps are the actual section-ring maps, each graded,
base-linear and natural, with mutually inverse composites. Restriction only
keeps the components indexed below V, and inverse exchanges the two maps.
There is no choice or postponed proof in these definitions.

`tools/blueprint_refs.py search 'graded algebra isomorphism'` returned zero
blueprint nodes. DAG concept searches found the global functoriality node and
the scalar-extension node but no interface for an isomorphism only on U.
`msearch.py leansearch` with the exact affine-refinement description returned
eight hits, led by `GradedObject.isoMk` and `Scheme.Modules.inv_app`; these are
not graded algebra maps with units and base linearity. `msearch.py loogle`
`GradedRingHom, RingEquiv` returned zero. `msearch.py grep`
`LocalGradedIso|Graded.*Iso|Iso.*Graded` in RingTheory/GradedAlgebra returned two
comments in Basic.lean about an algebra's graded direct-sum identification.
Direct source and Sheaf searches `LocalGradedIso|localGradedIso` found nothing;
the global affine-basis `GradedAlgebraData.Hom` was read, but does not encode
restriction of a fixed pair of sheaves to one base open. These real search
records, including tool result digests, are in the new node's mathlib_searches.
The item cites the new node directly. All its other original statement
and proof dependencies, and its mathematical statement, are preserved.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
