## Worker report

The item is a stage-2 statement, not a new split. The live node is split and reviewed
PASS on 2026-10-24 but has no Lean record. The stage-handoff paragraph in
coord/brief-stage2.md explicitly permits recording its Lean statement. The inherited
stage-1 refusal therefore does not apply. No stage-1 field or accepted proof is changed.

The main module is Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformEtaleLocalization;
its sole theorem is AlgebraicGeometry.AlgebraicSpace.strictTransform_etale_localization.
It has a sorry proof. The companion definition module supplies the previously missing
module quotient presentation, with actual structure data and no sorry or choice.

Source read: spaces-divisors.tex, section Strict transform, the setup immediately before
Tag 0862, Definition 0862(1)-(2), and Lemma 0863(1)-(3) with its proof. These retain the
centre and define strict transforms by quotienting out supported sections. The local
power-torsion formulation is the rule of spaces-limits.tex Tag 0859(2). The added covering
assertion follows by the field-point covering definition and Tag 041F(3).

Hypothesis-by-hypothesis correspondence:

- The base S is explicitly `S : Scheme.{u}`; all algebraic spaces are over this same S
  and all fields, scheme tests and structure-ring sections have the framework's u.
  There is no new relation between independent universe levels.
- X and T are arbitrary algebraic spaces, and f is the arbitrary morphism `f : X ⟶ T`.
- The schemes A and W are encoded as algebraic spaces together with `hA` and `hW`,
  saying their underlying presheaves are isomorphic to `yoneda.obj A₀` and
  `yoneda.obj W₀` for schemes over S. This is exactly scheme representability, including
  empty and non-affine schemes; the isomorphisms are data encoding, not restrictions.
- The square consists of `a : A ⟶ T`, `w : W ⟶ X`, `g : W ⟶ A` and
  `comm : w ≫ f = g ≫ a`. It is assumed commuting only, not cartesian.
- Its horizontal arrows are etale by `ha : IsEtale a.hom.hom` and
  `hw : IsEtale w.hom.hom`, the recorded representable scheme-test definition.
- The centre is `K : QuasiCoherentIdeal T`, an actual subobject of the unit module
  with the Mathlib quasi-coherence predicate. Its finite-type hypothesis is
  `hK : (K.val : T.Modules).IsFiniteType`.
- `B : BlowupPresentation K` represents T' with its projection, by cartesian ordinary
  scheme blowups on every affine etale chart. `P : StrictTransformPresentation f K B`
  represents the ambient fibre product, the closed strict transform X', its inclusion,
  both ambient projections, and the full exceptional-torsion ideal. These are the
  already landed definitions, not independently chosen spaces or maps.
- The preliminary descriptions of quasi-compactness, quasi-separatedness, module finite
  type and finite presentation are conventions in the node, not additional hypotheses
  of this lemma. No compactness, separatedness, flatness or finite presentation of f or M
  is required. Open and closed immersions use the existing scheme-test predicates.

Clause-by-clause correspondence:

- `KA` and the epimorphism `k` with
  `k ≫ KA.val.arrow = idealTensorMap a K` specify exactly the image K O_A. Since the
  arrow of the subobject KA is monic, this is its image factorization and cannot change
  the centre. `BA : BlowupPresentation KA` is A', the same descended ordinary blowup
  when A is a scheme. `PA : StrictTransformPresentation g KA BA` is W' with ambient
  W times_A A'. The existential presentations expose the objects already defined in
  the node, including all their kernel rules, rather than assuming comparison maps.
- `IsPullback BA.projection.hom v.hom a.hom B.projection.hom` says that A' is canonically
  A times_T T', respecting both projections. A pullback square determines the unique
  isomorphism to the fibre product. `hv` gives etaleness of A' to T'.
- `hp : IsPullback h.hom PA.toSource.hom P.toSource.hom w.hom` identifies the ambient
  chart with W times_X (X times_T T'); `h ≫ P.toBlowup = PA.toBlowup ≫ v` retains the
  second projection. `hh` gives the other asserted etale map.
- The map j satisfies `j ≫ P.inclusion = PA.inclusion ≫ h` and the displayed cartesian
  square over X. Thus W' is canonically X' times_X W with its closed-subspace structure,
  not merely with an equality of point sets. The ambient inclusion is monic, so these
  conditions determine j uniquely.
- For every `M : X.Modules` with `M.IsQuasicoherent`, Q and QW are full quotient
  presentations of the two module strict transforms. Their complete local kernel
  rules and epimorphic quotient maps determine these objects up to the unique
  quotient-preserving isomorphisms. No mere arbitrary module witness is used.
- The object isomorphism c compares restriction of q^*M with q_W^*(M|_W). Its formula
  on every local tensor is exactly the normalization of the recorded tensor-pullback
  comparison: keep the restricted section m and multiply scalar coefficients b and d.
  This fixes c as the canonical tensor comparison.
- `∃! e` gives the canonical module-strict-transform comparison and explicitly imposes
  `(pullback h hh).map Q.quotient ≫ e.hom = c.hom ≫ QW.quotient`. Thus it preserves
  quotient maps from the pulled-back modules. The source map is an epimorphism, so
  this normalization supplies the claimed uniqueness.
- The final implication assumes precisely that a and the canonical presheaf map
  `pullback.lift w.hom.hom g.hom.hom ...` from W to X times_T A are surjective on field
  point classes. They are singleton `IsJointlySurjective` families indexed by Unit.
  Its three conclusions give surjectivity of v, h and j. This includes both transformed
  ambient charts and the strict-transform cover; it does not replace the original
  W to X times_T A hypothesis by a stronger cartesian-square assumption.

Dependency declarations used, read in their recorded modules:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, IsEtale, EtaleSite,
  etaleTopology, structureSheaf, Modules, etaleMap and pullback.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  fibreProduct_isAlgebraicSpace, etaleCover_pullback and etale_fibreProduct_isScheme;
  the cartesian square interface is Mathlib IsPullback on sheaves.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: the recorded chart-test
  morphism-property conventions are imported unchanged; none adds a hypothesis here.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: QCoh specializes Mathlib's
  SheafOfModules.IsQuasicoherent; the theorem uses the very same predicate on Modules.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback,
  moduleTensorSection and their recorded moduleTensorAdjunction normalization.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction:
  moduleChartBaseChange and etale_module_pushforward_restriction, including the latter's
  full section and local-tensor formulas. The theorem's c uses that same normalization.
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup, an actual scheme glued
  from the recorded datum. It is used by the existing BlowupPresentation chart rule.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIdeal: QuasiCoherentIdeal and
  idealTensorMap; Sheaf.AlgebraicGeometry.AlgebraicSpaceArtinRees: idealSectionImage
  (owned by def-sfb-space-ideal-power-products, not by the Artin-Rees theorem).
- Sheaf.AlgebraicGeometry.AlgebraicSpaceBlowupPresentation: BlowupPresentation and
  blowupChartIdeal; Sheaf.AlgebraicGeometry.AlgebraicSpaceStrictTransformPresentation:
  StrictTransformPresentation, including the full local kernel rule.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity: IsJointlySurjective, expanded
  as field-valued representatives lifting after field extension. The original
  fibre-product dependency already uses this point-class convention.
- Proof-only: Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus. The recorded
  proof dependency lem-sfb-space-blowup-chart-properties currently has no Lean module,
  so there is no import for it; its proof step is retained in the theorem docstring.
  The other two recorded proof dependencies are already publicly imported for their
  statement interfaces. The size-convention node is metatheoretic with no declaration.

Edge cases checked before drafting: the unit centre gives the identity blowup and zero
exceptional torsion; the zero centre gives the empty blowup. Empty A or W is allowed,
with no surjectivity conclusion unless the displayed covering antecedents hold. The
zero module and modules consisting entirely of exceptional torsion give zero quotient.
Exponent zero kills only a zero section, because the zeroth ideal power contains 1.
On a non-quasi-compact chart exponents may vary locally: the covering sieve and further
restrictions in the kernel rule preserve this case. The exceptional equation may become
a zero divisor after pullback; all powers are still admitted, so no regularity on f or M
is hidden. The original square need not be cartesian. No source correction or
STATEMENT-DISPUTED flag is needed.

Searches: msearch.py leanfinder queried "Strict transforms of algebraic spaces and quasi
coherent modules commute with etale localization": eight scheme-etaleness, scheme-module
restriction and localization hits, no exact result. Loogle queried
"AlgebraicGeometry.AlgebraicSpace.StrictTransformPresentation,
AlgebraicGeometry.AlgebraicSpace.ModuleStrictTransform": no Mathlib match. The Mathlib
AlgebraicGeometry grep `strictTransform|strict_transform|StrictTransform` returned no hits.
The new node additionally records the raw output of LeanSearch, LeanFinder and Mathlib
grep for the module quotient notion. Project rg under lean/WeilConjectures found the
scheme-only Compactification.StrictTransform; the item-id grep found no attachment.
Project rg under lean/Sheaf found the existing space blowup and space-strict-transform
presentations and the scheme-only ModuleStrictTransform family. DAG search found
scheme-only def-trf-module-strict-transform but no algebraic-space module quotient node.
blueprint_refs.py search "module strict transform" returned zero; ancestor returned
null, so the new node retains the item's existing null-ancestor provenance.

Validation: both delivered files compiled separately in dependency order through the
prescribed scompile.py wrapper with no errors or unexpected warnings. All universes and
variables are explicit (`autoImplicit false`), and all Lean lines are at most 100 columns.

## New nodes

`def-sfb-space-module-strict-transform-presentation` defines the module quotient in
Stacks Tag 0862(1), with the explicit locally exceptional-power-torsion kernel. Its
parameters retain K, the blowup presentation and the ambient projections of the space
strict-transform presentation. Its data are a genuine module, a quotient arrow, its
sheaf-epimorphism property and its exact kernel rule, with no sorry and no choice.
The new node's generic formula makes sense for all module sheaves; for the finite-type
centre and quasi-coherent M used by this item it is exactly the source's supported-section
quotient. The searches above and their recorded raw outputs exclude a second definition:
the similarly named existing module strict transform is on scheme Zariski modules, whereas
this module lives on the already recorded small etale module category of an algebraic
space. The item additionally cites the landed blowup, ideal, space strict-transform and
point-surjectivity nodes used here. Their records and modules are reused unchanged.

Preflight repair: the live new-node schema additionally requires `import_flags`; the new
definition node now carries the empty list. No import flags or mathematics are changed.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
