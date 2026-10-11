## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage` states
`AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections_chart_preimage`.
It uses `ULift (Fin (n+1))` for the coordinates, so `n : ℕ` and all indices
`j,l` range over exactly `0,…,n`. The binder `g : Y ⟶ S`, invertible module
`L`, and epimorphism `hs` render the hypotheses that the sections generate
`L`. For each `j`, the first conjunct identifies the inverse image of
`standardOpen _ S j` with `nonvanishingLocus L ((s j).val (op ⊤))`, the
projective chart and the section nonvanishing locus. For each `l`, the second
conjunct says that the pullback of `coordRatio _ S j l` multiplies the
restricted `s_j` to the restricted `s_l`, and that every function with this
property equals that pullback ratio; this is existence plus uniqueness of the
ratio function.

Dependency declarations used: `AlgebraicGeometry.ProjectiveSpace.ProjectiveSpace`
from `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`; `AlgebraicGeometry.Scheme.Modules.IsInvertible`
from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`;
`AlgebraicGeometry.Scheme.residueField` from Mathlib (used by the shared
nonvanishing-locus definition); and
`AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections` from
`Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`.
The chart and ratio interfaces are the source declarations
`AlgebraicGeometry.ProjectiveSpace.standardOpen`, `coordRatio`, and the
nonvanishing locus is
`AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`.

Edge cases checked: `n = 0` gives the singleton coordinate `Fin 1`; the
statement allows empty `Y`; no nonempty-coordinate assumption is added (the
coordinate family itself supplies the recorded epimorphism); and all scheme
and module universes are the shared `u`.

Searches made: `msearch.py` LeanSearch query “A morphism to projective space
defined by generating sections of an invertible module pulls each standard
chart back to the nonvanishing locus and coordinate ratios to section ratios”
(service unavailable); LeanFinder with the same chart-preimage query returned
only Mathlib's trivial-bundle `Proj.fromOfGlobalSections_*` declarations;
Loogle query `AlgebraicGeometry.Proj.fromOfGlobalSections` likewise returned
only the trivial-bundle declarations; grep of Mathlib
`AlgebraicGeometry/ProjectiveSpectrum` found only those trivial-bundle
preimage and away-section declarations. `rg` over `WeilConjectures` found
`homOfSections_preimage_standardOpen` for the trivial bundle and
`coordRatio`/invertible-section infrastructure, but no declaration of this
invertible-module statement. `rg` over `lean/Sheaf` found no prior item
module.


## Second reading by M1

Read the item node, all four original statement-dependency nodes and their
recorded declarations, and the module independently. Source read:
`/home/ubuntu/c1-stacks-review/constructions.tex` (the local Stacks source copy;
this clone has no `literature/stacks-project/`), lines 1688ff (01MM),
2449ff (01N8), 2612ff (01NA), and 2785–2850 (01NE, 01NF and the following
paragraph). The source assumes arbitrary schemes, an invertible module,
and generating global sections; it imposes no Noetherian, field, finite-type,
separatedness or characteristic hypothesis on Y or the base.

Object/hypothesis/conclusion checklist, in the order of the node:

- S and Y arbitrary schemes, and g : Y → S: `{Y S : Scheme.{u}}` and
  `(g : Y ⟶ S)`. Exact; g supplies the specified base morphism.
- n ≥ 0 and coordinates 0,...,n: `(n : ℕ)` and
  `ULift.{u} (Fin (n + 1))` for s, j and l. Exact finite coordinate set;
  ULift only changes its universe, not its elements.
- P^n_S and its two projections: the inferred target of
  `homOfGeneratingSections _ g L s hs` is the recorded
  `ProjectiveSpace (ULift (Fin (n+1))) S`. Read ProjectiveSpace.lean:130–145:
  it is the fibre product with raw integral Proj; the structural map is
  pullback.fst and `toProjInt` is pullback.snd. No replacement projective space.
- D_+(T_j)_S and u_{l/j}: `standardOpen _ S j` and `coordRatio _ S j l`.
  Read OfSections.lean:113 and OfInvertible.lean:57: the former is the
  second-projection preimage of Proj.basicOpen X_j; the latter is precisely
  the second-projection pullback of the homogeneous localization fraction
  X_l/X_j. Denominator/numerator order is correct.
- Invertible O_Y-module L: `(L : Y.Modules) [L.IsInvertible]`.
  Read Modules/Invertible.lean:57: every point has an open neighbourhood
  trivializing L. This is the recorded rank-one Zariski-local notion,
  with quasi-coherence a consequence, not an added hypothesis.
- Global sections s_0,...,s_n: `(s : ULift.{u} (Fin (n+1)) → L.sections)`.
  Read Presheaf.lean:320 and Free.lean:61. These are compatible sections;
  evaluation `(s i).val (op ⊤)` identifies them with ordinary global
  sections, since ⊤ is terminal in the opens category. No extra data.
- The sections generate L: `(hs : Epi (L.freeHomEquiv.symm s))` is the
  free-sheaf evaluation map. This is the same recorded generating
  hypothesis as in ProjectiveSpaceHomOfGeneratingSections and
  InvertibleGeneratingSectionsFibre, whose signatures were read.
  It is a real hypothesis, not an epimorphism automatically supplied by
  invertibility.
- The specified morphism φ: `homOfGeneratingSections _ g L s hs`.
  Read its complete definition and `generatingSections_integralHom_exists`:
  it chooses the uniquely classified integral morphism and pairs g with
  its composite to raw Proj. Its defining theorem uses tensorPullback and
  the section-preserving isomorphism required by the node. No additional
  trivialization or chosen cover is a binder here.
- Y_s defined by nonzero residue-field value: `nonvanishingLocus L
  ((s j).val (op ⊤))`. Read Ample.lean:31: germ outside maximalIdeal
  times the stalk, equivalent to nonzero class in the residue-field
  fibre. Read Scheme.residueField: it is the local-ring residue field.
  This is the shared notion prescribed in STATE, with no inline copy.
- Conclusion (i), for every j: the first conjunct is equality of the
  underlying set of the open preimage with that nonvanishing locus.
  Exact; the equality also certifies openness of the right-hand set.
- Conclusion (ii), for every l: the first inner conjunct is the equation
  restricted s_l = φ.app(chart)(coordRatio) • restricted s_j.
  `L.presheaf.map (homOfLE le_top).op` is restriction from the top open
  to the preimage chart. φ.app is pullback of functions into Γ(Y,preimage).
  Via (i) this is precisely Γ(Y_{s_j},O), with no extra cast assumption.
- Uniqueness in (ii): `∀ a : Γ(Y,preimage chart), equation → a =
  φ.app(chart)(coordRatio)`. Together with the previous equation this
  is existence and uniqueness of the stated ratio. Quantifiers are
  ∀ j, (i) ∧ ∀ l, (equation ∧ uniqueness), exactly as in the node.

Edge cases: n=0 has the singleton Fin 1 and includes l=j; its ratio is 1.
The coordinate set cannot be empty for any n≥0, so no empty-coordinate
case from this item is lost. Empty Y and empty chart preimages are allowed:
sections on the empty open give the unique scalar. Empty S forces empty Y
through g and is also allowed. A zero module is invertible only on the
empty scheme, which is covered. No restriction on characteristic is present.
The sole bound universe u is arbitrary; any two schemes can be viewed in
one common universe, and ULift puts the finite coordinates in that universe.
There is no lower-universe test-object hypothesis or unbound universe.

Independent searches (recorded in searches.jsonl): LeanSearch query
“For a line bundle generated by finitely many sections the associated
projective morphism pulls back a distinguished affine chart to the locus
where its denominator section is nonzero” returned service unavailable,
so no verdict is inferred from it. LeanFinder query “line bundle generated
by homogeneous coordinates: inverse image of a distinguished projective
chart and induced quotient of sections”
returned basicOpenIsoAway_hom, awayToSection, awayι,
fromOfGlobalSections_resLE and related Proj localization results.
Loogle `"coordRatio"` returned no hits. The msearch grep
`fromOfGlobalSections.*(preimage|resLE)|nonvanishing|line.bundle` in
AlgebraicGeometry/ProjectiveSpectrum returned only the global-functions
special case. Read fromOfGlobalSections and its preimage lemma: they
require a ring map to Γ(Y,O), so do not state this general-L item.
Independent rg in source ProjectiveSpace/ and project Projective*.lean
found the existing standardOpen/coordRatio interfaces and partial source
results `homOfIsFreeGenerator_appLE_coordRatio`,
`isFreeGenerator_of_twistRestrict_iso`, and
`map_eq_coordRatio_smul_of_twistRestrict_iso`. Read their signatures:
they respectively require a selected cover/free generators, or a specified
isomorphism with twistRestrict. None gives both this chart-preimage
identity and the unique ratio for the recorded classified morphism.
No exact existing statement or duplicate declaration was found.

Changes: the Lean statement and proof docstring are correct and unchanged.
The worker omitted the direct DAG citation for the already shared
nonvanishingLocus declaration. Added the landed
`def-weil-pbc-ample-invertible-module` to stmt_deps; its lean.declarations
records nonvanishingLocus, and its statement explicitly gives the same X_s
predicate. This does not assume ampleness or CompactSpace Y. No new node,
no dependency module, and no statement correction is needed.

H5/H6/H8/H9: the delivery contains one theorem with only `by sorry`,
no definitions or private notions, no proved lemmas, and no local notation
or local instances. The source-and-blueprint docstrings include all four
node proof steps and their dependencies. Imports serve the morphism,
coordinate ratio, and nonvanishing locus respectively; lines are ≤100
characters and every variable is bound. The node lean.statement is the
file signature verbatim up to the proof assignment.

Validation: scompile.py compiled ProjectiveMorphismChartPreimage.lean on
the server in 2.2 seconds, exit 0, with no warnings or errors.
