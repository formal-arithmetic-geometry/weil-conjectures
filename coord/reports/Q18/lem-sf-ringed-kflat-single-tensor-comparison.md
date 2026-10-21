## Worker report

The module `Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison` states
`SheafOfModules.ringed_kFlat_single_tensor_comparison`, with one `sorry` and no new
definitions. The item statement is unchanged. Its `stmt_deps` cites the new
`def-sf-ringed-kflat-tensor-representative-data`, an `existing: true` binding of the five
published helpers used in the signature, and `def-pc-flat-sheaf-modules` for
`IsFlatOnSite`. The theorem `lem-weil-pbc-kflat-fixed-tensor-triangulated` is not a
statement dependency. No dependency record is repaired and no Lean declaration changes.

Source read: `literature/stacks-project/sites-cohomology.tex`, the construction immediately
before `definition-derived-tor` (Tag 06YU), `definition-K-flat`,
`lemma-K-flat-quasi-isomorphism`, `lemma-K-flat-resolution`, and
`lemma-derived-tor-quasi-isomorphism-other-side`. Also read the current blueprint
`sec-six-functors-basics/sk-lem-sf-flat-model/lem-sf-reduction-flat-model.proof.md`:
the ordinary tensor with the coefficient module in degree zero computes reduction.
The theorem docstring preserves all seven proof steps from this item's node.

Hypothesis and clause correspondence:

- The site is `{C : Type u} [Category.{v} C] {J : GrothendieckTopology C}`;
  `[EssentiallySmall.{r} C]` is precisely smallness in the coefficient universe.
  `R : Sheaf J CommRingCat.{r}` has coefficients in `r`. No equality of `u`, `v`,
  `r` is imposed. The independent `[HasDerivedCategory.{w} (Modules R)]` supplies
  the chosen localization universe. These implement `def-weil-size-convention`.
- `Modules R` unfolds to `ringedSiteModules.{r}` of the ring sheaf obtained by the
  forgetful functor, hence to Mathlib's `SheafOfModules.{r}`. No new category or
  abelian instance is chosen. `P : CochainComplex (Modules R) ℤ` is unrestricted.
- The sole mathematical hypothesis on P is
  `CochainComplex.IsKFlatIndependentCoefficients P`, the recorded acyclic-tensor
  predicate, not termwise flatness or a stronger replacement predicate.
  `M : Modules R` is arbitrary, and
  `(HomologicalComplex.single _ (.up ℤ) 0).obj M` is exactly M[0].
- `derivedTensor R` is `Functor.curry.obj (siteDerivedTensorIndependentCoefficients J R)`.
  It is the specified site-descent tensor, with `DerivedCategory.Q` as Q_R.
  `ordinaryTensor R` is the existing curried sheafified tensor.
- The target complex is `(((ordinaryTensor R).flip.obj M).mapHomologicalComplex
  (.up ℤ)).obj P`. Its term is P.X q tensor M and its differential is P.d q q'
  tensor the identity of M. `mapHomologicalComplex` supplies the complex and chain
  equations; no hollow data or independently defined termwise tensor is introduced.
- The existential family's values are isomorphisms oriented from the specified derived
  tensor to Q_R of that termwise complex. The first conjunct states naturality for
  every chain map `u : P ⟶ P'` between K-flat complexes and every module map
  `f : M ⟶ M'`. On the derived side we first map u, then f[0]. On the termwise
  side we map u by tensoring with M, then apply `NatTrans.mapHomologicalComplex`
  to the transformation induced by f. In degree q this is
  `(u.f q tensor id_M) ≫ (id_P'.X q tensor f) = u.f q tensor f`.
- The second conjunct quantifies over all flat-term K-flat A and B, and all
  quasi-isomorphisms p:A→P and b:B→M[0]. It states exactly
  `beta ≫ tensor(Qp,Qb) ≫ c.hom = Q(total(p,b) ≫ delta.hom)`, with beta the
  published `representativeIso` and delta the published
  `CochainComplex.mapBifunctorSingle₂Iso`. Delta projects the sole surviving
  summand (q,0), where the signed second differential is zero.
- Quantification over every pair of resolutions expresses independence of auxiliary
  choices. Beta and tensor(Qp,Qb) are invertible; flat-term K-flat resolutions exist.
  Thus this equation determines each c uniquely. `∃!` packages precisely this canonical
  normalization, including equality of the family and independence of proof witnesses.
  Flatness in this conjunct applies only to auxiliary A,B, never to P or M.
- There is no boundedness, flatness of P.X q, or flatness of M binder.

Dependency declarations used, with their recorded modules read:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` and `Qh`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `site_derived_tensor_descent_independentCoefficients` and its selected
  `siteDerivedTensorIndependentCoefficients`; read the complete comparison signature
  and construction, including unique extension.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `cochainModulesMonoidal`, the canonical localization tensor with independent universes.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `map₂CochainComplex` (signed direct-sum totalization).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.Modules`, `ordinaryTensor`, `totalTensor`,
  `derivedTensor`, and `representativeIso`. The last composes the actual selected
  descent comparison with its actual chain/homotopy comparison. It is reused unchanged.
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₂Iso`.

All recorded proof-dependency modules are imported too: the Grothendieck/K-injective
statement, `tensorClosed`, independent functorial flat resolutions,
`IsKFlatForTotalTensor`, `kFlatTensorPreservesQuasiIsoIndependentCoefficients`,
`DerivedCategory.hasDerivedMonoidalCategory`, and the K-flat resolution theorem.
Their signatures and docstrings were read. The Grothendieck/tensorClosed interfaces have
more specialized universe presentations; they are proof imports, not extra hypotheses
in this statement. A proof can use the small model prescribed by the node.

Edge cases checked mathematically before writing: P=0 and M=0; P=R[0]; the two-term
flat resolution [Z --2→ Z] tensor Z/2 (the nonzero negative Tor is retained);
a contractible identity complex [N --id→ N] with nonflat N (K-flat without flat terms);
unbounded K-flat complexes; empty site; degree q=0 and arbitrary negative q; and
independent site object/Hom/coefficient universes. In the single identification the
swap sign is (-1)^(q·0)=1, so there is no hidden degree-dependent sign.
No statement dispute or node correction was found.

Searches actually run:

- `msearch.py` leanfinder: “K-flat complex of sheaves tensor with module in degree
  zero computes derived tensor naturally”: eight hits on flat module exactness and Tor,
  no ringed-site canonical comparison.
- `msearch.py` loogle: `HomologicalComplex.tensorObj`: twelve underived total-tensor,
  associator and unitor hits, not this statement.
- `msearch.py` grep: `tensorObj|tensorHom|SingleIso` in `Algebra/Homology`:
  thirteen hits on total tensor, homology of a single complex, and extension; no match.
- `msearch.py` leansearch: “K-flat complex sheaves derived tensor module in degree
  zero canonical natural comparison”: eight hits on ordinary derived-zero functors,
  flat tensor exactness, and a complex unitor; no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for single/tensor,
  ringed/tensor, termwiseTensor, homotopyTensorSingleIso and map₂HomologicalComplex
  single comparisons; item-id search in WeilConjectures returned no declaration.
  `DerivedCategory.QObjTensorSingleFunctorObjIso` is a related generic native-monoidal
  comparison; it does not use the node's chosen descent tensor or state the two-variable
  normalization. The scheme representative lemma is also a specialization, not an exact
  match. The useful ordinary single identification is reused, not duplicated.
- Read `dag/lean_names_upstream.json` searches for the proposed name and the generic
  single comparison, and traced `siteDerivedTensorIndependentCoefficients` consumers;
  this found the already landed representativeIso helper reused above.

Validation: prescribed `scompile.py` compiled the draft separately as sandbox and library
module cleanly (19.8 s and 39.3 s). Final direct dependency imports are validated by the
required delivery dry run. The only postponed declaration is the named main theorem.

## Second reading by Q18

This is a second reading by the same dispatcher-started worker, not a claimed independent
agent review; the brief prohibits starting agents. The maintainer provides the independent
review. I reread the node and the full Lean signature after compilation.

I checked the site, ring, module universe, localization universe, K-flat predicate, arbitrary
M and unbounded integer indexing against the first paragraph. I unfolded ordinaryTensor,
derivedTensor and Modules in their owning module and checked the chosen descent theorem's
comparison is exactly the one used by representativeIso. I traced both naturality composites:
they have source tensor(QP,Q(M[0])) and target Q(T_M'(P')); the right edge first maps u and
then f and consequently has degree-q component u.f q tensor f. I checked the normalization
source is Q(Tot(A tensor B)), with its right side total(p,b) followed by the ordinary
single identification; no choice of arbitrary map replaces the canonical comparison.
The normalization is imposed for every p,b, so it determines the c family and expresses
the node's independence clause. No hypothesis mismatch was found.

The draft omitted direct imports for dependency modules already transitively visible; I
added the recorded imports explicitly in the final file. I also recorded the already landed
helper module through its new definition owner in stmt_deps. No mathematical statement was changed. All variables and
universes are explicitly bound, `autoImplicit` is false, maximum line width is 97, and the
sole theorem proof is `sorry`. No private definition, local notation, or new instance appears.


## New nodes

`def-sf-ringed-kflat-tensor-representative-data` owns exactly five existing declarations
in `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
`SheafOfModules.KFlatFixedTensor.Modules`, `ordinaryTensor`, `totalTensor`,
`derivedTensor`, and `representativeIso`. Its primary declaration is representativeIso;
its signature is recorded verbatim, and all five full names are in lean.declarations.
It creates no module and duplicates no definition. The module category is precisely
ringedSiteModules; ordinaryTensor is precisely the existing curried sheaf tensor;
totalTensor applies map₂CochainComplex; derivedTensor curries precisely the selected
site-descent functor. For K-flat A,B with flat terms, representativeIso composes
`(DerivedCategory.Qh.mapIso (c.app (A, B))).symm` with `d.app (a, b)` from the
selected site-descent data. This construction does not use the triangulated theorem.
The definition cites the six owners requested by the return: module sheaves, ordinary
tensor, total tensor, K-flatness, flatness, and site-derived-tensor descent.
Source: Stacks sites-cohomology.tex Tags 06YM and 06YU, total tensor and the
construction preceding definition-derived-tor, together with the published descent
comparison. This is construction data for the existing tensor, not a new existence claim.

New-node searches: msearch LeanSearch query `ringed site derived tensor flat term K-flat
representative comparison` gave eight module flatness/exactness hits, none this site
comparison; Loogle `SheafOfModules, DerivedCategory.Q` gave zero hits; Mathlib grep
`representativeIso|siteDerivedTensor|ordinaryTensor` in Algebra/Homology gave zero hits.
Their full returned output is retained in mathlib_searches. DAG grep of the five fully
qualified helper names found only the triangulated theorem node, not a definition owner.
Source grep in WeilConjectures and Sheaf located the five together in the published
KFlatFixedTensorTriangulated module, with no WeilConjectures match. Blueprint search
`representative tensor` gave zero hits; the broader `K-flat` search was also read.
Thus existing:true records the exact published data without introducing another copy.

## Returned-delivery repair

Return L at immutable head b588d79ca859, H2: the previous packet cited a theorem node
although its signature used only that module's four abbreviations and representativeIso.
The initial saved-packet dry run passed at b692c12503b; this mechanical pass does not
resolve the review fault. I compared the saved node to the current shared node: before
repair only lean and stmt_deps differed; the current shared node still has no lean binding.
I replaced the added theorem dependency by the new definition owner described above,
and added def-pc-flat-sheaf-modules directly for hAf/hBf. The source statement, proof,
proof_deps and Lean file are unchanged. The delivery wrapper rebases this repaired packet
on the current live branch.

Second reading of the repair by Q18: I reopened the item signature and the five published
helper definitions. The first four are transparent abbreviations for the existing data;
representativeIso uses the descent theorem's actual comparison choices with the inverse
homotopy-total comparison in the correct direction. The new definition statement records
exactly these constructions and their independent site/coefficient universes. Its only
flatness binders concern A,B in representativeIso, matching the normalization clause;
no flatness or bounds are imposed on P or M. IsFlatOnSite is directly owned by the added
flat-sheaf node and is used precisely in hAf and hBf. I checked all six new-node
statement dependencies against their existing records. The repaired DAG introduces no
new mathematical hypothesis, conclusion, theorem or choice. Zero A or B, unbounded A,B,
and independent universes remain covered. The main signature remains verbatim and its
naturality and unique normalization are unchanged from the reviewed head.

Repair validation: scompile.py compiled the unchanged main module cleanly in both sandbox
and library positions (28.4 s and 24.2 s), with no errors or unexpected warnings.
Self-check confirms the item differs from current main only in lean and stmt_deps,
the main signature is verbatim, all six new-node citations match stmt_deps, and the new
existing:true record lists exactly the five requested definitions.
