## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.UnipotentNormalQuotientImage` states
`AlgebraicGeometry.SolvableGroupStructure.unipotent_normal_quotient_image`, with
`sorry` as its only proof. No definitions or helper theorems are introduced.
The mathematical statement is unchanged. The only node changes are its `lean`
record and the addition of two already landed definition dependencies:
`def-sfb-solvable-group-structure` and `def-weil-pbc-faithfully-flat-ring-map`.

Hypothesis and conclusion correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The four F-group schemes are `A D N I : Grp (Over (Spec (.of F)))`.
  A bundled `Grp` carries the recorded `GrpObj` structure. For each of the four,
  `IsAffine X.X.left`, `LocallyOfFiniteType X.X.hom`, and `QuasiCompact X.X.hom`
  state affine and finite type, with no smoothness or connectedness on A or D.
- The quotient homomorphism is `f : A ⟶ D`. Its faithful flatness is exactly
  `hf : f.hom.hom.left.appTop.hom.FaithfullyFlat`, on F[D] to F[A]. This uses
  `RingHom.FaithfullyFlat`, equivalent to exact extension of scalars detecting
  zero modules. It is not an assumption of smoothness on f.
- The inclusion is `iN : N ⟶ A`, with
  `IsClosedSubgroupScheme iN.hom.hom` and
  `IsNormalSubgroupScheme iN.hom.hom`. The second class tests normality on
  every commutative F-algebra, including nonreduced ones.
- Smoothness and connectedness of N are `[Smooth N.X.hom]` and
  `[ConnectedSpace N.X.left]`. The latter includes nonemptiness.
- Unipotence is `hN : IsUnipotent N` from the already landed
  `SolvableGroupStructure` module: a faithful closed finite matrix representation
  with `(matrix - 1)^M = 0`, `0 < M`, at every point over every algebraically
  closed extension F-algebra. This predicate also includes smoothness, already
  assumed separately in the node. It adds no hypothesis here. The existing node
  explicitly interprets a faithful representation as a closed immersion.
- The factorization uses the homomorphism `uN : N ⟶ I`, the over-scheme map
  `j : I.X ⟶ D.X`, `[IsClosedImmersion j.left]`, faithful flatness
  `hu : uN.hom.hom.left.appTop.hom.FaithfullyFlat` on F[I] to F[N], and
  `hfactor : iN.hom.hom ≫ f.hom.hom = uN.hom.hom ≫ j`.
  In particular, j is not supplied with an extra homomorphism hypothesis.
- The four requested conclusions are `Smooth I.X.hom`,
  `ConnectedSpace I.X.left`, `IsUnipotent I`, and `IsNormalSubgroupScheme j`.
  The last class also establishes the homomorphism property and pointwise
  injectivity of j. Thus it states normality of the specified closed image,
  not normality of an abstract set of F-points.
- There is no hypothesis on either kernel: neither finite, central nor smooth.
  The introductory G_a and G_m notation does not occur in this assertion's
  hypotheses or conclusions; their recorded module is imported for the node's
  conventions and the trivial-torus proof input.

Dependency declarations read and reused:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (imported via AlgebraicClosure).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `CategoryTheory.Grp` and
  their bundled homomorphisms, Mathlib.CategoryTheory.Monoidal.Grp.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. Read the full class fields,
  especially `injective_comp` and `normal_range`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `QuasiCompact` from
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-sc-gm-ga`: `StandardGroupSchemes.affine`, `multiplicative`, and
  `additive` in Sheaf.AlgebraicGeometry.StandardGroupSchemes; retained through
  the definition/proof imports, rather than introducing alternative groups.
- `def-sc-general-linear-group`: Sheaf.AlgebraicGeometry.LinearGroupSchemes,
  which deliberately reuses `AlgebraicGeometry.GeneralLinearGroup` and
  `GeneralLinearGroup.homMulEquiv` in the upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Read the actual
  `Spec` coordinate-ring definition, the group structure, and natural points
  equivalence. `IsUnipotent` uses precisely this GL, not an unrelated GL model.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- Added landed node `def-sfb-solvable-group-structure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsUnipotent`,
  Sheaf.AlgebraicGeometry.SolvableGroupStructure. No copied predicate.
- Added landed node `def-weil-pbc-faithfully-flat-ring-map`:
  `RingHom.FaithfullyFlat`, Mathlib.RingTheory.RingHom.FaithfullyFlat, and
  `Module.FaithfullyFlat`, Mathlib.RingTheory.Flat.FaithfullyFlat.Basic.

Proof-only imports include the stated dependencies for faithfully flat tensor
injections and base change, affine tensor-product pullbacks, smooth geometric
reducedness, reduced group smoothness, residue-field identification and maximal
ideal existence, and `CentralTorusWeightBlocks.exists_faithful_weight_blocks`.
The still unstated proof dependency
`lem-sfb-rational-representation-unipotent-point` has no module to import;
it is not needed to type this statement. The six proof steps, including that
node, are fully recorded in the theorem docstring for stage 3.

Sources checked directly in the local Milne PDF: printed pp.24--25 for
Proposition 1.62(b), p.114 for Proposition 5.59(b), p.282 for Corollary 14.7,
and p.400 for the proof of Lemma 19.14. These explicitly support the quotient
smoothness, connectedness, unipotence and normality clauses without requiring
a smooth kernel.

Edge cases checked before writing:

- N=1 and I=1 are allowed; a trivial group admits a faithful representation,
  and connectedness includes its identity point. The existing predicate allows
  n=0, equivalent here to the trivial representation in positive dimension.
- A and D may be disconnected or nonsmooth; neither is accidentally excluded.
- Positive characteristic is unrestricted. In particular the Frobenius map on
  G_a has nonsmooth kernel alpha_p and is allowed as uN (or f).
- No condition on a kernel's dimension, finiteness or centrality is present.
- The conclusion's normality quantifies over all algebras, not only geometric
  points; the geometric-point quantification belongs only to unipotence.
- The common universe u permits the base field itself as a test extension, so
  the geometric condition is not vacuous. This follows the existing scheme and
  GL interfaces; finite-type geometric tests can be descended to same-universe
  extensions by their finitely many coordinates.
- The factorization equation is in `Over (Spec F)`, so all maps are genuinely
  F-morphisms and the composite is exactly f restricted to N.

Searches actually run with the prescribed `msearch.py N7` wrapper:

- leanfinder: "The image of a normal smooth connected unipotent affine group
  scheme under a faithfully flat homomorphism is smooth connected unipotent
  and normal". Eight hits, including `AlgebraicGeometry.Flat` and
  `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`; no theorem matching
  this group-scheme image statement.
- loogle: `"Unipotent", "GroupScheme"`. Zero hits.
- grep Mathlib: `unipotent.*(quotient|normal|image)|(quotient|normal|image).*unipotent`.
  Zero hits.
- leansearch: "The quotient image of a smooth connected normal unipotent
  algebraic subgroup is smooth connected unipotent and normal". Eight hits
  about abstract group quotients, including `QuotientAddGroup.map_normal`,
  `nilpotent_quotient_of_nilpotent`, and `solvable_quotient_of_solvable`;
  none states the affine group-scheme result.
- `rg` on lean/WeilConjectures and lean/Sheaf for unipotent/Unipotent and the
  node id found the existing IsUnipotent predicate and consumers' proof plans,
  but no declaration of this assertion. The explicit `grep -rn` for the id in
  lean/WeilConjectures found no occurrence. A full-name check in
  dag/lean_names_upstream.json found no duplicate theorem name.

No statement fault or STATEMENT-DISPUTED issue was found. The sample
CompactObject module was read as requested; it is now a withdrawn module with
no declarations, so the current neighboring stage-2 modules supplied the
module/header/docstring conventions.

Validation: scompile.py checked the module against current server sources,
with no errors or unexpected warnings. Its local precheck reported disk space
exhaustion; the wrapper automatically confirmed the compile on the server
successfully (3.0 seconds). Final import changes are checked again below by
the final compile and delivery preflight.

## Second reading by N7

A separate source-to-signature rereading was performed by the delivering worker;
independent maintainer review remains part of delivery, as specified in the
brief. No claim of an independent second agent is made.

The rereading compared the node with the final file: the field is algebraically
closed; all four groups are affine finite type; only N is assumed smooth and
connected; iN is closed and normal; hN uses the existing geometric faithful
matrix condition; the coordinate maps of f and uN are faithfully flat; hfactor
has the right composition order; j is a closed immersion over F. The conclusion
contains all four clauses for I and its specified immersion. In particular the
rereading checked the subtle missing assumption risk: j was kept as an over-map,
not bundled as a group homomorphism, since step 1 proves that property. It also
checked that no smooth-kernel assumption, fppf-kernel identification, or
pointwise surjectivity assumption was inserted.

The two added statement dependencies already have usable Lean records, and no
new or repaired definition is needed. The unipotence predicate's built-in
smoothness repeats an existing hypothesis/conclusion; its empty matrix-index
case adds only the already permitted trivial group. No mismatch requiring a
statement correction was found.
