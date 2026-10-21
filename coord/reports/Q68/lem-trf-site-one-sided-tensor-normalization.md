## Worker report

The module `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization` states
`SheafOfModules.site_one_sided_tensor_normalization`, with one `sorry` and no definitions.
Its source is Stacks sites-cohomology.tex, construction immediately before
`definition-derived-tor` (06YU), together with the signed symmetry immediately following.
The seven proof steps in the node are carried into the theorem docstring, including
homotopies, the cone argument, localization, normalization, uniqueness using resolutions,
fixed-factor naturality, and reversed order.

Hypotheses and clauses, matched individually:

- Site and size: `{C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]`,
  `{J : GrothendieckTopology C}`. Object, morphism, coefficient and derived Hom
  universes `u v r w` are independent. Essential smallness is precisely smallness
  relative to the module universe, and the standard sheafification/abelian instances
  are inferred, not additional mathematical assumptions.
- Commutative ring sheaf: `R : Sheaf J CommRingCat.{r}`. The node's letter B for
  coefficients becomes R, reserving B for the homotopy tensor bifunctor.
- Module category: `Modules R` is the existing transparent abbreviation for
  `CategoryTheory.ringedSiteModules.{r}` on R's underlying ring sheaf, hence
  Mathlib's `SheafOfModules.{r}` with its existing abelian structure. Its owning
  definition node is now `def-sf-ringed-kflat-tensor-representative-data`.
- Homotopy category and localization: `HomotopyCategory (Modules R) (.up ℤ)`
  and `DerivedCategory.Qh`; `HasDerivedCategory.{w} (Modules R)` specifies the
  localization universe.
- Resolving subcategory: `P : ObjectProperty ...` and `hP` identify its objects
  exactly with `CochainComplex.IsKFlatIndependentCoefficients X.as` and
  `∀ n : ℤ, IsFlatOnSite ... (X.as.X n)`. The iff supplies both directions.
- Total tensor on homotopy categories: B is a curried bifunctor and `hB` is the
  natural comparison of its composite with the product homotopy quotient to
  `Functor.uncurry.obj (totalTensor R)` followed by that quotient. The existing
  `totalTensor` is `(ordinaryTensor R).map₂CochainComplex`, and `ordinaryTensor`
  is the existing curried sheaf tensor. These abbreviations are owned by
  `def-sf-ringed-kflat-tensor-representative-data`, with no exactness theorem used.
  The signs and direct sums are precisely the dependency's total tensor.
- Specified derived tensor and comparison: D is the curried derived bifunctor;
  δ is a natural isomorphism `(P.ι.prod P.ι) ⋙ uncurry B ⋙ Qh ≅
  ((P.ι ⋙ Qh).prod (P.ι ⋙ Qh)) ⋙ uncurry D`. These parameters fix the given
  two-sided comparison as actual data, rather than forgetting it in an existential
  `Nonempty`. The theorem works for each realization of the dependency's data.
- Preservation of every quasi-isomorphism in both orders is the first conjunct,
  using `HomotopyCategory.quasiIso` on arbitrary `M M'` and both
  `(B.obj T.obj).map f` and `(B.flip.obj T.obj).map f`.
- Left comparison family: the first existential c has type
  `∀ T : P.FullSubcategory, Qh ⋙ D.obj (Qh.obj T.obj) ≅ B.obj T.obj ⋙ Qh`.
  Components have exactly the direction derived tensor → localized total tensor.
- Naturality in every M-map is part of that `NatIso` type. In Lean composition
  order its hom naturality reads `D(1,Qf) ≫ c(T,M') = c(T,M) ≫ Q B(1,f)`,
  exactly the node's first displayed equation written in the opposite order.
- Normalization is `(c T).app V.obj = (δ.app (T,V)).symm` for every T,V in P.
- Uniqueness is explicitly `∀ c', normalization c' → c' = c`, over all families
  of natural isomorphisms. It does not assume fixed-factor naturality of c'.
- Fixed-factor naturality is the separate equation involving every full-subcategory
  `g : T ⟶ T'`, `B.map g.hom`, and `D.map (Qh.map g.hom)`. No quasi-isomorphism
  condition on g is introduced. This is exactly the second displayed equation.
- For every resolution V→M, the first naturality equation applies because M and
  its morphisms are arbitrary. Along with the explicit normalization and uniqueness
  this includes the node's assertion that the resolution square determines c.
- The second existential repeats all three clauses for the reversed order via
  `D.flip`, `B.flip`, and normalization `(δ.app (V,T)).symm`.
- Signed chain symmetry: the last conjunct states the bidegree (i,j) component of
  the existing `CochainComplex.Monoidal.braiding`, using `ιTensorObj` and the scalar
  `((i*j).negOnePow : ℤ)`. Ordinary module-sheaf braiding interchanges the pure
  tensors; the scalar gives precisely (-1)^(ij). The target summand uses j,i.
- The arbitrary M has no K-flatness, termwise flatness, or boundedness predicate.

Dependency declarations used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`:
  `SheafOfModules.KFlatFixedTensor.Modules`, `.ordinaryTensor`, `.totalTensor`,
  through their existing definition owner
  `def-sf-ringed-kflat-tensor-representative-data`. None uses the triangulated
  exactness theorem or any `.choose` of that theorem.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Qh`, `HomotopyCategory.quotient`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Mathlib.Algebra.Homology.Bifunctor`: `Functor.map₂CochainComplex`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`:
  `SheafOfModules.site_derived_tensor_descent_independentCoefficients`; P, B, D
  and δ unpack its existential data, without choosing new resolutions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the
  existing independent-universe monoidal/additive/colimit instances.
- `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` supplies the existing signed
  `CochainComplex.Monoidal.braiding` and `ι_braiding_hom`; their signatures and
  construction were read. The latter is the known summand identity in the last clause.

Proof-only dependency modules are imported for the K-flat resolution, cone criterion,
tensor-cone isomorphism, and localization universal property, as the stage requires.
The size-convention node has no declaration and is rendered by explicit universe binders.

Edge cases checked by reading the types: the empty site and zero coefficient ring
are admitted; zero complexes and zero fixed-factor maps are admitted; no map g is
inverted; negative i,j are supported by integer `negOnePow`; all n are integers;
M may be unbounded in both directions and nonflat in every degree. The same construction
handles identity resolutions and arbitrary supplied resolutions. The universe binders
allow unequal site object/Hom universes and larger independent coefficients.

Searches actually run (see searches.jsonl generated by msearch.py):

- LeanFinder: "Unique one-sided K-flat derived tensor comparison normalized by the
  two-sided tensor comparison on a ringed site". Eight hits, ordinary tensor flatness
  and Tor, including `IsTensorProduct.map_id_injective_of_flat_right` and
  `CategoryTheory.Tor'_obj_obj`; none is this normalized comparison.
- Loogle: `"KFlat"`. Only `Lean.mkFlatCtorOfStructCtorName`.
- msearch grep: `KFlat|oneSidedTensor|one_sided_tensor`, subdirectory
  `Algebra/Homology`. No hits.
- LeanSearch: "Unique natural isomorphism for one-sided K-flat tensor computation
  normalized on two K-flat complexes". Eight hits including
  `CategoryTheory.Bicategory.LeftExtension.IsKan.uniqueUpToIso`,
  `CategoryTheory.Functor.leftDerivedNatIso`, and `HomologicalComplex.rightUnitor'`;
  none gives the stated site tensor normalization and uniqueness.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `oneSided|one_sided|tensor.*normalization|siteDerivedTensor`: the existing descent,
  KFlatFixedTensorTriangulated and other specialized normalization modules were found.
  The fixed-tensor theorem has no uniqueness of this family or arbitrary homotopy
  fixed-factor naturality. The single-tensor comparison treats a degree-zero other
  factor. Neither states this item. The existing transparent tensor helpers are
  used through their published definition owner, rather than the theorem node.
- grep for the item's ID in `lean/WeilConjectures`: no hits.
- rg for the proposed declaration name in Mathlib-facing upstream names,
  `lean/WeilConjectures`, and `lean/Sheaf`: no collision.

No statement correction, new node, dependency replacement, or disputed statement.
The original packet compiled cleanly through scompile.py in both sandbox and
library modes (19.9 s and 13.2 s respectively). Repair validation is recorded below.

## Second reading by Q68

This is the author's second reading; the maintainer supplies the independent review.
I reopened the node and Lean file and traced every quantifier and conclusion. In
particular `hP` is an iff, so the resolving category is neither a subset nor a
superset; δ retains its original orientation and both normalization equations use
its inverse, with (T,V) versus (V,T). I checked the sources and targets of the
naturality composites: c followed by localized ordinary tensor is equal to derived
tensor followed by c. Every g is a homotopy-category arrow in the full subcategory.
Uniqueness quantifies over families natural only in M, so the later naturality in T
has not been smuggled into the uniqueness assumption. The preservation clause
covers both tensor orders on arbitrary homotopy-category arrows. The signed
interchange includes negative degrees and uses the existing chain isomorphism.
No additional flatness/boundedness assumptions were found. The repaired signature
still has exactly these quantifiers and clauses. The seven base dependencies are
retained and the existing definition owner of the abbreviations is cited; the
rejected theorem-only dependency is removed.

## Returned-delivery repair

Return H2 at immutable head `645f5df3ec49` identified the added theorem dependency
used only for `Modules` and `totalTensor`. The return expressly allowed a definition
node owning those existing abbreviations. The live repository now has exactly that
node: `def-sf-ringed-kflat-tensor-representative-data`, independently reviewed by L
for Q18 on 2026-10-21 with `existing: true`. Its `lean.declarations` lists
`Modules`, `ordinaryTensor`, `totalTensor`, `derivedTensor`, and `representativeIso`
in `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`. I read its complete
statement and record and the source definitions, including their docstrings.

I replaced `lem-weil-pbc-kflat-fixed-tensor-triangulated` in `stmt_deps` with
`def-sf-ringed-kflat-tensor-representative-data`. The original seven dependencies
are retained. No new node or definition is introduced. The module import remains
because it is now the recorded module of the definition owner, exactly as allowed
by the return's parenthetical alternative. The definition owner explicitly excludes
the triangulated exactness assertion. The theorem is not used, and no `.choose` of
it enters this signature. `lean.statement` was extracted verbatim from the final
signature. Every other node field agrees with the current read-only base.

Searches made during repair:

- `rg` over `dag/nodes` for `KFlatFixedTensor.(Modules|ordinaryTensor|totalTensor)`
  found the rejected theorem owner and the now-landed Q18 definition owner. The
  latter already records all three exact declarations; no duplicate node is needed.
- `tools/blueprint_refs.py search 'total tensor'` returned 13 related blueprint
  nodes; none replaces this normalized one-sided theorem.
- `rg` in `lean/Sheaf` located the existing abbreviations at lines 54, 59 and 63
  of `KFlatFixedTensorTriangulated.lean`; no counterpart in `lean/WeilConjectures`.
- LeanSearch query "Named abbreviation for the category of module sheaves over a
  commutative ring sheaf and its total tensor bifunctor on unbounded cochain
  complexes" returned eight hits including `SheafOfModules` and `Scheme.Modules`.
- LeanFinder query "Abbreviation for curried total tensor bifunctor on complexes
  of module sheaves on a ringed site" returned eight hits, including
  `HomologicalComplex.tensorObj` and `HomologicalComplex.ιTensorObj`.
- msearch grep `KFlatFixedTensor|totalTensor|ringedSiteModules` in
  `Algebra/Homology` returned zero Mathlib hits.

The advisory about fixing D was considered: the independently accepted free D/δ
interface is retained, so every specified realization of the two-sided descent
comparison remains covered.

Repair validation: `scompile.py` compiled the final module cleanly in sandbox mode
(19.9 s) and library mode (13.2 s), with no errors or warnings. The final signature
retains explicit `autoImplicit false` and independent `u v r w`; every Lean line
fits within 100 characters, and the only postponed proof is the named theorem.
