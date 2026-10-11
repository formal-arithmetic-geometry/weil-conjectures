## Worker report

The item is stated by `AlgebraicGeometry.localizedCohomology_mayerVietoris` in
`lean/Sheaf/Paper/LocalizedCohomologyMayerVietoris.lean`. Its only proof is `sorry`.
The auxiliary module contains actual definitions, with no postponed data or proofs.
Both modules compiled together on the server without errors or warnings (3.6 seconds).

Source read: Stacks Project Tag 09MR, especially its displayed Mayer--Vietoris ladder
and the immediately following intersection/union identities, at
https://stacks.math.columbia.edu/tag/09MR . The local Stacks checkout is absent on this
machine, so the source was read from the Stacks website. The shared module
`Sheaf.Topology.ModuleMayerVietoris` was read in full, including its source and proof
for Tag 01EB. No change to the item's mathematical statement is proposed.

Hypotheses and objects, in the order of the node:

- `X : Scheme.{uMV}` is the scheme Y; `[CompactSpace X]` is quasi-compactness,
  with no Hausdorff condition; `[QuasiSeparatedSpace X]` is scheme quasi-separatedness.
- `L F : X.Modules`, `[L.IsInvertible]`, and `[F.IsQuasicoherent]` are respectively
  the invertible module and quasi-coherent module. The invertibility predicate is
  the recorded `Scheme.Modules.IsInvertible`, not a new local predicate.
- `s : L.val.presheaf.obj (Opposite.op ⊤)` is precisely a global section of L.
- `U V : X.Opens`, `_hU : IsCompact (U : Set X)`, and `_hV : IsAffineOpen V`
  retain the quasi-compact-open and affine-open assumptions. They are genuine
  assumptions even though the diagram construction works more generally.
- `p : ℕ` handles every nonnegative cohomological degree. No characteristic or
  nonemptiness assumption is imposed. Every universe and variable is explicit.
- The module tensor product is the source monoidal structure on `X.Modules`, and
  the nonnegative powers are the source `Scheme.Modules.tensorPow`.
- `twistCohomology L F W p n` is definitionally
  `(RingedSpace.openModuleCohomology X.toRingedSpace p W).obj
  (F ⊗ L.tensorPow n : X.Modules)`. Thus it uses the established right-derived
  sections cohomology, including restriction, rather than the different abelian-
  sheaf Ext encoding `Scheme.Modules.H`.

Rendering of every conclusion and of the maps that specify the diagram:

- The existential open `S` has underlying set `nonvanishingLocus L s`, the recorded
  nonvanishing locus from `Sheaf.AlgebraicGeometry.Ample`. Hence `W ⊓ S` is W_s.
- The next two equalities give exactly U_s intersect V_s = (U intersect V)_s
  and U_s union V_s = (U union V)_s.
- `TwistedCohomologyFractions L F s W p` is the additive degree-zero localization,
  in its generators-and-relations presentation (see New nodes below).
- `e W p n` is multiplication by s^n on the localized open. Its displayed equation
  identifies its forward map with the map on cohomology of `twistSectionPower`;
  it is not an arbitrary chosen cohomology isomorphism. The inverse in the next
  formula therefore means division by s^n. These witnesses introduce the
  trivializations used in defining the comparison, not an extra hypothesis.
- `c W p` is an additive homomorphism, and the formula on every `twistFraction`
  is exactly xi/s^n -> restriction(xi)/s^n. The fractions generate the quotient,
  so this determines the comparison map completely.
- `δ` is explicitly equated with `Classical.choose
  (RingedSpace.module_mayerVietoris X.toRingedSpace)`. The imported theorem states
  that these transformations, the restriction pair, and the difference of
  restrictions form the exact Mayer--Vietoris sequence, for every pair of opens
  and every module; its last clause gives naturality on intersecting a cover
  with an open. Thus the lower row is the shared Mayer--Vietoris sequence of F
  on U_s and V_s, with exactness supplied by that theorem, not unspecified maps.
- `a p`, `b p`, `d p` are the upper restriction pair, difference of restrictions,
  and connecting map. Their four equations on fraction generators identify them
  with localization of the same maps for each twist. In particular the equation
  for `d` uses the same `δ` evaluated on `F ⊗ L.tensorPow n`, so the connecting
  square is not omitted or replaced by a freely chosen exact sequence.
- `Function.Injective (a 0)` records the initial zero term (H^(-1) = 0).
  For every p, `Function.Exact (a p) (b p)`, `Function.Exact (b p) (d p)`, and
  `Function.Exact (d p) (a (p+1))` record all repeating exactness positions in the
  upper long sequence. The finite product is the binary direct sum of groups.
- The final three conjuncts are the restriction-pair square (both components),
  the difference square, and the connecting square. The connecting square uses
  the restriction identifications from `inf_sup_right` and
  `inf_inf_distrib_right` to identify the lower union/intersection with the
  corresponding intersections with S. These are canonical identity-on-open
  restrictions, not additional comparison maps.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Scheme.Opens`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, `tensorPow` and its monoidal
  module structure. Its full class signature and docstring were read.
- `Sheaf.AlgebraicGeometry.Coherent`: its docstring identifies the quasi-coherent
  clause with Mathlib `SheafOfModules.IsQuasicoherent`; `RingedSpace.IsCoherent`
  is not used because coherence is not assumed here.
- `Sheaf.Paper.PQFCohomology`: the recorded theorem
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` was read in full. Its
  cohomology notion is `RingedSpace.moduleCohomology`; its higher-direct-image
  clause is irrelevant here. We use the established open version through
  `Sheaf.Topology.OpenModuleCohomology`, `RingedSpace.openModuleCohomology` and
  `openModuleCohomologyRestriction`, as required by the shared conventions.
- `Sheaf.AlgebraicGeometry.Ample`: `Scheme.Modules.nonvanishingLocus`, and the
  recorded tensor powers. `IsAmple` itself is not assumed.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (definition read); the scheme
  conventions node supplies no declaration of its own and points to the
  corresponding Mathlib properties. Scheme quasi-separatedness is
  `QuasiSeparatedSpace X`.
- `Sheaf.Topology.ModuleMayerVietoris`: `RingedSpace.module_mayerVietoris`.
  This existing landed node and the open-cohomology definition are added to the
  item's statement dependencies, since their recorded declarations occur in
  the statement. There is no dependency replacement.
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`:
  `Scheme.Modules.homOfGlobalSection`, used to construct multiplication by s.

Edge cases checked mathematically before writing:

- At n=0, `twistSectionPower` is the inverse right unitor; the formula for c is
  ordinary restriction followed by this canonical identification.
- At p=0 the initial injectivity is present, without interpreting natural
  subtraction as H^(-1). For p+1 the connecting square covers all subsequent
  terms.
- For s=0, the quotient relations kill every summand (the transition is zero),
  S is empty and both rows are zero. There is no nonzero-section assumption.
- For a nilpotent section the iterated transitions kill each element, again
  giving zero localization, as required.
- Empty X, empty U or V, and F=0 are allowed. Cohomology of an empty open is
  zero; the powers and quotient are defined without a nonempty carrier.
- Negative twists in the full graded sum do not exclude any cases: a
  degree-zero fraction has denominator s^n for n>=0, so its homogeneous numerator
  has degree n>=0. Taking degree zero therefore has the nonnegative-twist
  quotient presentation used here, even though the full graded module has all
  integer components. No boundedness assumption on p or on the twists is made.

Searches performed (actual tool results are in searches.jsonl):

- msearch LeanFinder: `Mayer Vietoris diagram localization graded sheaf cohomology
  invertible module section` returned generic site MayerVietorisSquare short
  complexes, not this diagram.
- msearch Loogle: `LocalizedModule, DirectSum, RingedSpace.openModuleCohomology`
  returned no hits and an unknown-identifier notice for the project declaration.
- msearch grep: `MayerVietoris|gradedCohomology|sectionRing`, subdirectory
  AlgebraicGeometry, returned no hits.
- msearch LeanSearch: `degree zero localization graded sheaf cohomology as quotient
  direct sum tensor powers transition multiplication section` was unavailable
  (Internal Server Error), not treated as evidence of absence.
- msearch LeanFinder: `degree zero localized twisted sheaf cohomology quotient
  direct sum relations multiplication section` returned Tilde.const and generic
  sheaf presentation APIs, not localized twisted cohomology.
- msearch grep: `twistCohomology|TwistedCohomologyFractions|twistFraction|twistSectionStep`
  in AlgebraicGeometry returned no hits. The same identifiers were searched
  throughout WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json with
  no hits. A search for the item id in WeilConjectures also returned no hits.
- DAG concept search found the existing `def-sc-invertible-section-ring`; its
  statement and record were read. It defines the section ring, not its graded
  cohomology modules or this localization. That ring is not duplicated here.
  Existing `LocalizedModule.homogeneousPieceAway` was read: it requires an
  already constructed ring/module action, and does not define twisted sheaf
  cohomology or its section multiplication.
- `blueprint_refs.py search 'localization cohomology'` returned zero matches;
  `search 'graded cohomology'` returned the unrelated prop-weight-purity.
  `blueprint_refs.py ancestor` confirmed lem-sc-pic-proper-ntorsion.

No STATEMENT-DISPUTED flag, statement correction, or hollow definition.

## New nodes

`def-sc-twisted-cohomology-fractions` defines the localized additive cohomology
by the explicit fraction presentation needed in the 09MR ladder. Its module is
`Sheaf.AlgebraicGeometry.TwistedCohomologyFractions`, with the actual tensor
multiplication step, its powers, the established cohomology applied to the
nonnegative twists, the subgroup generated by i_n(x)-i_(n+1)(s*x), the quotient,
and the fraction inclusion. None uses `sorry`. This is precisely the usual
localization relation: two fractions agree after multiplying both numerators
by sufficiently large powers of s; quotienting the direct sum by the indicated
relations realizes the same directed-colimit group. It retains s-torsion and
nilpotents. It defines the additive object occurring in the diagram, so does
not introduce a second section ring or an arbitrary graded action. The source
is Stacks 09MR's xi/s^n construction and Mayer--Vietoris paragraph; the blueprint
ancestor and via chain are recorded. The three recorded searches are actual
LeanSearch (unavailable), LeanFinder (generic Tilde and presentation results),
and Mathlib grep (no hits); local project/DAG/blueprint searches are detailed
above. No existing definition node or Lean declaration supplies this object.

## Second reading by G1

I independently read the node statement, both delivery modules, and the recorded dependency declarations. The node introduces a quasi-compact, quasi-separated scheme `Y` (rendered as `X : Scheme.{uMV}` with `[CompactSpace X]` and `[QuasiSeparatedSpace X]`), an invertible module `L`, a quasi-coherent module `F`, a global section `s`, opens `U,V`, and the compact/affine hypotheses. The Lean binders preserve this order and impose no extra characteristic, nonemptiness, finiteness, or universe assumptions. `L.IsInvertible` is the project's `Scheme.Modules.IsInvertible`; `F.IsQuasicoherent` is the recorded quasi-coherence predicate.

The conclusion is rendered clause by clause: `S` is the nonvanishing locus; the two intersection/union identities are present; `e` is an additive equivalence induced by `twistSectionPower`; `δ` is the chosen common Mayer--Vietoris connecting transformation; `c` is the additive fraction comparison with the stated restriction and inverse-trivialization formula; and `a,b,d` have the restriction, difference, and connecting formulas on fraction generators. The Lean conclusion includes injectivity at degree zero, all three exactness clauses for every `p`, and the three commutative-square clauses in the same quantifier order. The lower row uses `openModuleCohomology`, while the upper row uses `TwistedCohomologyFractions`, exactly matching the node's localized degree-zero and localized-open descriptions.

The auxiliary definition was read as a new notion. It has no hollow data: `twistSectionStep`, `twistSectionPower`, cohomology, relations, quotient, and fraction inclusion are all actual definitions. Its relation is the source relation `xi/s^n = (s*xi)/s^(n+1)` and its index is the nonnegative denominator index appropriate to degree zero. Searches in Mathlib, `WeilConjectures`, `lean/Sheaf`, and the DAG found no existing declaration of this notion; the dependency records for invertibility, open cohomology, nonvanishing loci, and Mayer--Vietoris were inspected and are the declarations used by the modules.

Edge cases remain covered: `p=0` is handled by `Function.Injective (a 0)`, `n=0` uses the canonical right-unitor power, zero or nilpotent `s` and zero modules are allowed, and empty schemes or opens require no nonemptiness assumption. Universes are tied to the scheme (`uMV`), and no independent index universe is introduced. I found no mismatch and made no source or Lean changes. Both modules compile together with `scompile.py`; the node's recorded `lean.statement` remains verbatim equal to the theorem signature.
